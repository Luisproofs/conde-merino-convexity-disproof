"""Independent rank–nullity expansion, grouping subsets by frontier partitions."""
import ast
from collections import Counter
from fractions import Fraction
from itertools import combinations
from math import comb
from pathlib import Path
import re


def graph():
    edges = list(combinations(range(5), 2))
    start = 0
    for i in range(5):
        a = 5 + 3*i
        end = 1 if i == 4 else a+2
        edges.extend(((start, a), (a, end), (start, a+1), (a+1, end)))
        start = end
    return edges


def histogram(edges):
    """Count edge subsets by (#spanning components, #chosen edges).

    The partition records connectivity through all previously processed edges.
    A block closes exactly when its last vertex leaves the frontier.
    """
    last = {v: i for i, edge in enumerate(edges) for v in edge}
    states = Counter({((), 0, 0): 1})
    for i, (u, v) in enumerate(edges):
        next_states = Counter()
        for (blocks, closed, size), count in states.items():
            active = [frozenset(block) for block in blocks]
            for w in (u, v):
                if not any(w in block for block in active):
                    active.append(frozenset([w]))
            left = next(block for block in active if u in block)
            right = next(block for block in active if v in block)
            joined = [block for block in active if block != left and block != right]
            joined.append(left | right)
            for chosen, partition in enumerate((active, joined)):
                kept = [tuple(sorted(w for w in block if last[w] > i)) for block in partition]
                key = (tuple(sorted(block for block in kept if block)),
                       closed + kept.count(()), size + chosen)
                next_states[key] += count
        states = next_states
    assert all(not blocks for blocks, _, _ in states)
    return {(closed, size): count for (_, closed, size), count in states.items()}


def verify():
    edges = graph()
    vertices = set(range(19))
    assert {v for e in edges for v in e} == vertices
    assert all(u != v for u, v in edges)
    assert len({tuple(sorted(edge)) for edge in edges}) == len(edges) == 30
    for removed in vertices:
        seen = {next(iter(vertices - {removed}))}
        for _ in vertices:
            for u, v in edges:
                if removed not in (u, v) and (u in seen or v in seen):
                    seen.update((u, v))
        assert seen == vertices - {removed}
    counts = histogram(edges)
    assert sum(counts.values()) == 2**30
    for j in range(31):
        assert sum(c for (k, size), c in counts.items() if size == j) == comb(30, j)
    coeffs = [0]*31
    for (k, j), count in counts.items():
        nullity = j - len(vertices) + k
        assert nullity >= 0
        degree = k - 1 + nullity
        for i in range(degree + 1):
            coeffs[i] += count*(-1)**(k-1+i)*comb(degree, i)
    while coeffs[-1] == 0:
        coeffs.pop()
    src = (Path(__file__).resolve().parents[1]/'CondeMerino'/'Minors.lean').read_text()
    published = re.search(r'^def coefficients : Coeffs := (\[.*\])$', src, re.M)
    assert published and coeffs == ast.literal_eval(published[1])
    h = Fraction(1, 256)
    p0, pm, pe = [sum(c*x**i for i, c in enumerate(coeffs)) for x in (0, h, 2*h)]
    excess = 2*pm - p0 - pe
    assert excess == Fraction(26123280769243048353292998299952433382036731393, 2**159)
    print(f'Rank–nullity check counted {sum(counts.values()):,} edge subsets.')
    print(f'All {len(coeffs)} coefficients agree. All 19 vertex deletions are connected.')
    print(f'Exact midpoint excess: {excess}')


if __name__ == '__main__':
    verify()
