"""Exact Tutte evaluations of all series/parallel edge labellings of a fixed core."""
from fractions import Fraction
from itertools import combinations


def component_counts(n, edges):
    counts = []
    for mask in range(1 << len(edges)):
        labels = list(range(n))
        components = n
        for i, (u, v) in enumerate(edges):
            if mask & (1 << i) and labels[u] != labels[v]:
                old, new = labels[v], labels[u]
                labels = [new if a == old else a for a in labels]
                components -= 1
        counts.append(components)
    return counts


def transform(values, m, series, parallel):
    # Each pass converts one input bit (edge absent/present) to one output
    # bit (edge replaced by a path/bundle). The other axes are untouched.
    result = values.copy()
    for i in range(m):
        step = 1 << i
        for start in range(0, len(result), 2 * step):
            for j in range(start, start + step):
                u, v = result[j], result[j + step]
                result[j] = series[0] * u + series[1] * v
                result[j + step] = parallel[0] * u + parallel[1] * v
    return result


def counts(n, kcomp, m, path, bundle):
    signs = [(-1) ** k for k in kcomp]
    trees = [int(k == 1 and a.bit_count() == n - 1) for a, k in enumerate(kcomp)]
    a = transform([(-1) ** n * t for t in signs], m, (2**path - 1, -1), (1, -1))
    c = transform([-t for t in signs], m, (1, 1), (1, 2**bundle - 1))
    b = transform(trees, m, (path, 1), (1, bundle))
    return a, c, b


def wheel(r):
    return [(0, i + 1) for i in range(r)] + [(i + 1, (i + 1) % r + 1) for i in range(r)]


def cases():
    yield 'K4', 4, list(combinations(range(4), 2))
    yield 'W4', 5, wheel(4)
    yield 'K33', 6, [(u, v) for u in range(3) for v in range(3, 6)]
    yield 'prism', 6, [(j+i, j+(i+1)%3) for j in (0,3) for i in range(3)] + [(i,i+3) for i in range(3)]
    yield 'K5', 5, list(combinations(range(5), 2))
    yield 'cube', 8, [(i,i^(1<<j)) for i in range(8) for j in range(3) if not i & (1<<j)]
    yield 'octahedron', 6, [(i,j) for i,j in combinations(range(6),2) if i//2 != j//2]
    yield 'W6', 7, wheel(6)
    yield 'Petersen', 10, [(i,(i+1)%5) for i in range(5)] + [(i,i+5) for i in range(5)] + [(i+5,5+(i+2)%5) for i in range(5)]
    yield 'K6', 6, list(combinations(range(6),2))


def check():
    # Bare triangle, doubled triangle and triangle with every edge subdivided.
    k = component_counts(3, [(0, 1), (1, 2), (0, 2)])
    assert tuple(x[0] for x in counts(3,k,3,1,1)) == (6,2,3)
    a,c,b = counts(3,k,3,2,2)
    assert (a[0],c[0],b[0]) == (62,2,6)
    assert (a[-1],c[-1],b[-1]) == (6,46,12)


if __name__ == '__main__':
    check()
    print('core path bundle labellings best_mask acyclic cyclic trees min_max_ratio min_product_ratio')
    for name,n,edges in cases():
        m = len(edges)
        k = component_counts(n,edges)
        for path,bundle in [(2,2),(2,3),(3,2),(3,3)]:
            a,c,b = counts(n,k,m,path,bundle)
            i = min(range(len(b)), key=lambda j: Fraction(max(a[j],c[j]),b[j]))
            j = min(range(len(b)), key=lambda j: Fraction(a[j]*c[j],b[j]**2))
            print(name,path,bundle,len(b),hex(i),a[i],c[i],b[i],Fraction(max(a[i],c[i]),b[i]),Fraction(a[j]*c[j],b[j]**2))
