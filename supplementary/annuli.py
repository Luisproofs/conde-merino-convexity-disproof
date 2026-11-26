"""Exact self-dual capped annular grid orientation/tree counts."""
from collections import defaultdict
from functools import lru_cache


def normalize(parts):
    ids = {}
    return tuple(ids.setdefault(a,len(ids)) for a in parts)


@lru_cache(None)
def detach(parts,i):
    vertex = parts[i]
    if parts.count(vertex)==1:
        return parts,-1
    return normalize(parts[:i]+(-1,)+parts[i+1:]),1


@lru_cache(None)
def join(parts,i):
    a,b = parts[i-1],parts[i]
    return normalize(tuple(a if v==b else v for v in parts))


def next_ring(states,n,radial_path):
    radial,ring = (3,1) if radial_path else (1,3)
    for i in range(n):
        updated = defaultdict(int)
        for p,weight in states.items():
            new,closed = detach(p,i)
            updated[new] += radial*closed*weight
            updated[p] -= weight
        states = {p:v for p,v in updated.items() if v}
    for i in range(n):
        updated = defaultdict(int)
        for p,weight in states.items():
            updated[p] += ring*weight
            updated[join(p,i)] -= weight
        states = {p:v for p,v in updated.items() if v}
    return states


def det(matrix):
    a = [row[:] for row in matrix]
    previous = 1
    for k in range(len(a)-1):
        pivot = a[k][k]
        assert pivot
        for i in range(k+1,len(a)):
            for j in range(k+1,len(a)):
                v = a[i][j]*pivot-a[i][k]*a[k][j]
                assert v%previous == 0
                a[i][j] = v//previous
        previous = pivot
    return a[-1][-1]


def rows(n,depth,radial_path=False):
    states = {(0,)*n:1}
    radial,ring = (1,4) if radial_path else (4,1)
    previous = [1]+[0]*(n-1)
    current = [radial+2*ring,-ring]+[0]*(n-3)+[-ring]
    for w in range(1,depth+1):
        states = next_ring(states,n,radial_path)
        a = (-1)**(1+n*w)*sum((-1)**len(set(p))*v for p,v in states.items())
        b = det([[current[(j-i)%n] for j in range(n)] for i in range(n)])
        yield w,a,b
        new = [(2*radial+2*ring)*x-ring*(current[i-1]+current[(i+1)%n])-radial**2*previous[i]
               for i,x in enumerate(current)]
        previous,current = current,new


if __name__=='__main__':
    from math import exp,log
    from substitutions import component_counts,counts,wheel
    for n in (3,4,5):
        edges=wheel(n)
        values=counts(n+1,component_counts(n+1,edges),2*n,2,2)
        for rev in (False,True):
            mask=(2**n-1)<<(n if rev else 0)
            _,a,b=next(rows(n,1,rev))
            assert (a,a,b)==tuple(v[mask] for v in values)
    print('circumference depth radial_path min_ratio_at_depth last_log_ratio_per_cell')
    for n in range(3,11):
        for rev in (False,True):
            data=list(rows(n,16,rev))
            assert all(a>0 and b>0 for w,a,b in data)
            from fractions import Fraction
            w,a,b=min(data,key=lambda rec:Fraction(rec[1],rec[2]))
            _,last_a,last_b=data[-1]
            print(n,16,rev,w,Fraction(a,b),round((log(last_a)-log(last_b))/(n*16),9))
        detach.cache_clear()
        join.cache_clear()
