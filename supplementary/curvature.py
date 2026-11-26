"""Right-hand derivatives of the Tutte free energy at (1,1) for inflated regular cores."""
from itertools import combinations
from math import comb
from terminal_cores import subset_sum
from substitutions import component_counts


def jets(n,m,parts):
    arrays=[]
    for j in range(3):
        coeff=[]
        for mask,k in enumerate(parts):
            nullity=mask.bit_count()-n+k
            power=k-1+nullity
            coeff.append((-1)**nullity if power==j else 0)
        arrays.append(subset_sum(coeff,m))
    return arrays


def records(n):
    m=comb(n,2)
    k=component_counts(n,list(combinations(range(n),2)))
    a,b,c=jets(n,m,k)
    e,f,g=jets(n-1,m,[k[j|1] for j in range(1<<m)])
    for i in range(1<<m):
        if k[i]!=1:
            continue
        # Exclude edges on no cycle in the completed two-terminal graph.
        if any(k[(i^1<<j)|1]!=1 for j in range(m) if i>>j&1):
            continue
        yield (e[i],f[i]+a[i],g[i]+b[i]-e[i],a[i],b[i]-e[i],c[i]-f[i]-a[i]),(n,hex(i))


def log_jet(d,net):
    D,u,v,C,s,t=net
    h=d/2-1
    B=(d-1)**2-1
    xp=D/C
    xpp=2*(u/C-D*s/C**2)
    first=h*u/D+s/C+h*xp/B
    second=h*(2*v/D-(u/D)**2)+2*t/C-(s/C)**2+h*(xpp/B+(xp/B)**2)
    return first,second


if __name__=='__main__':
    entries=dict(item for n in range(2,7) for item in records(n))
    for d in range(3,11):
        results=[(p+q,p,q,src) for net,src in entries.items() for p,q in [log_jet(d,net)] if p<0]
        print(d,len(results),min(results,default=None))
