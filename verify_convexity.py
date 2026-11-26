"""Reproduce the finite arithmetic in the convexity disproof using only Python stdlib."""
from collections import Counter
from fractions import Fraction as F
from functools import cache
from itertools import combinations

EDGES = tuple(combinations(range(6), 2))[1:]


def trim(p):
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return tuple(p)


def add(a, b):
    return trim((a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
                for i in range(max(len(a), len(b))))


def connected_parts(edges):
    p = list(range(6))
    for u,v in edges:
        old,new = p[v],p[u]
        p = [new if i == old else i for i in p]
    return p


def subset_pair():
    coeff = [Counter(),Counter()]
    for m in range(1 << len(EDGES)):
        part = connected_parts(e for i,e in enumerate(EDGES) if m >> i & 1)
        k = len(set(part))
        j = m.bit_count() - 6 + k
        same = part[0] == part[1]
        coeff[same][k - 2 + int(same) + j] += (-1)**j
    return tuple(trim(row[i] for i in range(max(row)+1)) for row in coeff)


def identify(edges, u, v):
    def label(x):
        return u if x == v else x
    return tuple(sorted(tuple(sorted((label(a),label(b)))) for a,b in edges))


@cache
def deletion_contraction(edges):
    # Isolated vertices do not affect the Tutte polynomial.
    if not edges:
        return (1,)
    (u,v), rest = edges[0],edges[1:]
    deleted = deletion_contraction(rest)
    if u == v:
        return add(deleted,(0,) + tuple(-a for a in deleted))
    contracted = deletion_contraction(identify(rest,u,v))
    part = connected_parts(rest)
    if part[u] != part[v]:
        return add(contracted,(0,) + contracted)
    return add(deleted,contracted)


def eval_poly(poly, t):
    acc = 0
    for a in reversed(poly):
        acc = acc*t+a
    return acc


def log_interval(z):
    # log z = 2*atanh((z-1)/(z+1)). Bound the tail by a geometric series.
    u = (z-1)/(z+1)
    n = 4
    partial = 2*sum(u**(2*k+1)/(2*k+1) for k in range(n))
    radius = 2*abs(u)**(2*n+1)/((2*n+1)*(1-u*u))
    return partial-radius, partial+radius


def run():
    d,c = subset_pair()
    ordinary = deletion_contraction(EDGES)
    merged = deletion_contraction(identify(EDGES,0,1))
    assert ordinary == add(c,(0,)+d)
    assert merged == add(d,(0,)+tuple(-x for x in c))
    print('D',d)
    print('C',c)
    # e^(2L) = 16 * D*C^3 / (3*C-t*D).
    h = add(tuple(3*a for a in c),(0,)+tuple(-a for a in d))
    first,second = F(0),F(0)
    for p,k in [(d,1),(c,3),(h,-1)]:
        slope = F(p[1],p[0])
        first += k*slope/2
        second += k*(F(2*p[2],p[0])-slope*slope)/2
    assert (first,second,first+second) == (F(-173,72),F(12451,5184),F(-5,5184))
    print("L' L'' sum",first,second,first+second)
    lam = F(216250003,90000000)
    left,middle,right = F(1,10**6),F(1,25000),F(1,10000)

    def rate(t):
        D,C = eval_poly(d,t),eval_poly(c,t)
        assert D>0 and C>0 and 0<1-t*C/D<1 and 1<1+t*D/C<2
        return 16*D*C**3/(3*C-t*D)

    for endpoint in (left,right):
        lo1,hi1 = log_interval(rate(middle)/rate(endpoint))
        lo2,hi2 = log_interval((1+middle)/(1+endpoint))
        low,high = lo1/2+lam*lo2,hi1/2+lam*hi2
        if endpoint == left:
            assert F(60,10**14)<low<=high<F(61,10**14)
        else:
            assert F(94,10**14)<low<=high<F(95,10**14)
        print('certified M(middle)-M(endpoint) times 10^14 lies between',
              (low*10**14).__floor__(),(high*10**14).__ceil__())
    print('All exact checks passed.')


if __name__ == '__main__':
    run()
