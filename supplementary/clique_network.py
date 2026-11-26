"""Exact signed partial Tutte polynomials for a complete graph missing its terminal edge."""
from itertools import combinations
from math import comb
from functools import cache
from collections import Counter


@cache
def connected(n,edges,missing):
    # Connected labelled graphs on n fixed vertices, with a fixed pair forbidden if missing.
    if edges<n-1 or edges>comb(n,2)-missing: return 0
    count=comb(comb(n,2)-missing,edges)
    for k in range(1,n):
        # component containing vertex 0, the first terminal when a pair is forbidden
        options=[(False,comb(n-1,k-1))] if not missing else [(False,comb(n-2,k-1))]
        if missing and k>=2:options.append((True,comb(n-2,k-2)))
        for miss,mult in options:
            room=comb(n-k,2)
            for s in range(max(k-1,edges-room),min(edges,comb(k,2)-miss)+1):
                count-=mult*connected(k,s,miss)*comb(room,edges-s)
    return count


@cache
def all_components(n):
    if not n:return {(0,0):1}
    coeff=Counter()
    for k in range(1,n+1):
        for e in range(k-1,comb(k,2)+1):
            count=comb(n-1,k-1)*connected(k,e,False)
            for (j,f),v in all_components(n-k).items():
                coeff[j+1,f+e]+=v*count
    return coeff


def clique(n):
    D,C=Counter(),Counter()
    for k in range(1,n+1):
        for both in (False,True):
            h=k-1-int(both)
            if not 0<=h<=n-2:continue
            for edges in range(k-1,comb(k,2)-both+1):
                weight=comb(n-2,h)*connected(k,edges,both)
                for (j,e),v in all_components(n-k).items():
                    nullity=edges+e-n+j+1
                    degree=j+nullity-int(not both)
                    if weight*v:
                        assert degree>=0
                        (C if both else D)[degree]+=weight*v*(-1)**nullity
    return tuple(tuple(f[i] for i in range(max(f)+1)) for f in (D,C))


if __name__=='__main__':
    from explicit_search import gadget
    for n in (4,5,6):
        for a,b in zip(clique(n),gadget(n)):
            while a and not a[-1]:a=a[:-1]
            while b and not b[-1]:b=b[:-1]
            assert a==b
    for n in range(4,11):
        print(n,[p[:3] for p in clique(n)])
