"""Rebuild, check generator reproducibility, replay proof terms and audit axioms."""
import argparse
import json
from pathlib import Path
import re
import subprocess
import tempfile

from generate_minors import emit
from subset_check import verify as check_subsets


ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def run(args, **kwargs):
    print('$', ' '.join(map(str, args)), flush=True)
    return subprocess.run(args, cwd=ROOT, check=True, **kwargs)


def verify(paranoid):
    generated = ROOT/'CondeMerino'/'Minors.lean'
    if generated.read_text() != emit():
        raise ValueError('Generated certificate differs from the release source.')
    sources = [*ROOT.glob('*.lean'), *(ROOT/'CondeMerino').glob('*.lean')]
    for src in sources:
        if re.search(r'\b(sorry|admit|native_decide|axiom|unsafe)\b', src.read_text()):
            raise ValueError(f'Forbidden declaration or proof shortcut in {src.name}')
    print('Certificate regeneration and source checks passed.', flush=True)
    check_subsets()
    run(['lake', 'build'])
    audit = run(['lake', 'env', 'lean', 'Audit.lean'], capture_output=True, text=True).stdout
    print(audit, end='', flush=True)
    roots = re.findall(r'^#print axioms (\S+)$', (ROOT/'Audit.lean').read_text(), re.M)
    for name in roots:
        line, = [s for s in audit.splitlines() if s.startswith(f"'{name}' ")]
        if 'does not depend on any axioms' in line:
            continue
        axioms = re.fullmatch(r"'.+' depends on axioms: \[(.*?)\]", line)
        if not axioms or set(axioms[1].split(', ')) - ALLOWED:
            raise ValueError(line)
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp)/'proof.ndjson'
        with path.open('wb') as out:
            run(['lake', 'env', 'leanexport', 'CondeMerino', '--', *roots], stdout=out)
        print(f'Exported {len(roots)} theorem roots and their transitive dependencies.', flush=True)
        run(['lake', 'env', 'leanchecker', '--from-export', str(path)])
        if paranoid:
            run(['lake', 'env', 'leanchecker-paranoid', '--from-export', str(path)])
            config = Path(tmp)/'nanoda.json'
            config.write_text(json.dumps({'use_stdin': False, 'export_file_path': str(path),
                                          'permitted_axioms': sorted(ALLOWED),
                                          'unpermitted_axiom_hard_error': True,
                                          'num_threads': 1, 'nat_extension': True,
                                          'string_extension': True}))
            run(['lake', 'env', 'nanoda_bin', str(config)])
        # Negative control: a one-unit change in the exact gap must be rejected
        # for the arithmetic reason shown below.
        test = Path(tmp)/'Rejected.lean'
        test.write_text('''import CondeMerino
open CondeMerino
example : 2 * P h - P 0 - P endpoint =
    26123280769243048353292998299952433382036731394 / 2^159 := by
  rw [exact_excess]
  decide +kernel
''')
        result = subprocess.run(['lake', 'env', 'lean', str(test)], cwd=ROOT,
                                capture_output=True, text=True)
        if result.returncode == 0 or 'false' not in result.stdout.lower():
            raise ValueError('Expected rejection of the altered certificate: ' + result.stdout)
        print('Negative control passed: Lean rejected a unit increase in the numerator.', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--paranoid', action='store_true', help='also use the paranoid Lean kernel and the independent nanoda checker')
    verify(parser.parse_args().paranoid)
