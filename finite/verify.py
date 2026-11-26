"""Independent exact verification. Run with python3 verify.py (no dependencies)."""
from fractions import Fraction
from functools import cache
from itertools import combinations


def cell(edges, start, end, a, b, diagonal=False):
    edges.extend(((start, a), (start, b), (a, end), (b, end)))
    if diagonal:
        edges.append((a, b))


def clique_with_squares():
    edges = list(combinations(range(5), 2))
    start = 0
    for i in range(5):
        a = 5 + 3*i
        end = a+2 if i < 4 else 1
        cell(edges, start, end, a, a+1)
        start = end
    return edges


def necklace(squares, diamonds):
    edges = []
    start = 0
    count = squares + diamonds
    for i in range(count):
        a = 1 + 3*i
        end = a+2 if i+1 < count else 0
        cell(edges, start, end, a, a+1, i >= squares)
        start = end
    return edges


def reachable(edges, start):
    adj = {}
    for a, b in edges:
        adj.setdefault(a, []).append(b)
        adj.setdefault(b, []).append(a)
    seen = {start}
    todo = [start]
    while todo:
        for v in adj.get(todo.pop(), ()):
            if v not in seen:
                seen.add(v)
                todo.append(v)
    return seen


def check_graph(edges, vertices, size, max_degree):
    pairs = {tuple(sorted(e)) for e in edges}
    vs = {v for e in pairs for v in e}
    assert len(vs) == vertices and len(edges) == len(pairs) == size
    assert all(a != b for a, b in edges)
    assert max(sum(v in e for e in edges) for v in vs) == max_degree
    for v in vs:
        rest = [e for e in edges if v not in e]
        assert reachable(rest, next(iter(vs-{v}))) == vs-{v}


def canonical(edges):
    # Isolated vertices do not affect the Tutte polynomial.
    edges = tuple(edges)
    labels = sorted({v for e in edges for v in e})
    ids = dict(zip(labels, range(len(labels))))
    return tuple(sorted(tuple(sorted((ids[a],ids[b]))) for a,b in edges))


def add(p, q):
    return tuple((p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0)
                 for i in range(max(len(p),len(q))))


@cache
def tutte(edges):
    """Coefficients of T(x,2-x) by deletion–contraction on the actual multigraph."""
    if not edges:
        return (1,)
    a,b = edges[-1]
    rest = edges[:-1]
    if a == b:
        p = tutte(canonical(rest))
        return add(tuple(2*c for c in p), (0,) + tuple(-c for c in p))
    contracted = canonical((a if u==b else u, a if v==b else v) for u,v in rest)
    p = tutte(contracted)
    if b not in reachable(rest,a):
        return (0,) + p
    return add(tutte(canonical(rest)),p)


def at(p, x):
    result = 0
    for c in reversed(p):
        result = x*result+c
    return result


def square_recursion(x):
    base = at((544,-932,796,-374,106,-16,1),x)
    closed = at((680,-1680,1898,-1240,499,-123,17,-1),x)
    for _ in range(5):
        closed = (3+x)*closed + (1+x)**2*base
        base *= 2+x*x+x**3
    return closed


def ring_formula(x, squares, diamonds):
    u = 1-x
    connected = (3+x)**squares*(12-5*x+x*x)**diamonds
    ordinary = (2+x*x+x**3)**squares*(6+x*x+x**3)**diamonds
    return ((1+u*u)*connected-ordinary)/u


def main():
    small = clique_with_squares()
    check_graph(small, 19, 30, 6)
    p = tutte(canonical(small))
    assert p[:3] == (280024,5612,-3278)
    # Both polynomial expressions have degree <=30, hence equality at 31 points suffices.
    assert all(at(p,i)==square_recursion(i) for i in range(31))
    h = Fraction(1,256)
    gap = 2*at(p,h)-at(p,0)-at(p,2*h)
    assert gap*2**159 == 26123280769243048353292998299952433382036731393
    assert Fraction(1,32)<gap<Fraction(1,27)
    print('19 vertices, 30 edges; P(0), P\'(0), P\'\'(0):',p[0],p[1],2*p[2])
    print('Midpoint excess 2P(1/256)-P(0)-P(1/128):', gap)

    planar = necklace(19,15)
    check_graph(planar,102,151,4)
    poly = tutte(canonical(planar))
    points = (Fraction(0),Fraction(1,8),Fraction(1,4))
    a,b,c = [at(poly,x) for x in points]
    assert [a,b,c] == [ring_formula(x,19,15) for x in points]
    assert 1002*a < 1000*b and 1004*c < 1000*b
    print('102 vertices, 151 edges; exact ratio checks: P(1/8) > 1.002 P(0), P(1/8) > 1.004 P(1/4)')


if __name__=='__main__':
    main()
