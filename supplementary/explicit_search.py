"""Search for a finite block with negative log curvature in log x."""
from itertools import combinations
from math import log
from collections import Counter
from substitutions import component_counts


def gadget(m):
    E=list(combinations(range(m),2))[1:]
    k=component_counts(m,E)
    j=component_counts(m-1,[(max(0,i-1),max(0,h-1)) for i,h in E])
    D,C=Counter(),Counter()
    for A,(b,z) in enumerate(zip(k,j)):
        separated=b!=z
        nullity=A.bit_count()-m+b
        power=b-1+nullity-int(separated)
        (D if separated else C)[power]+=(-1)**nullity
    return [tuple(f[i] for i in range(max(f)+1)) for f in (D,C)]


def value(poly,t):
    s=0
    for a in reversed(poly):
        s=a+t*s
    return s


def chain(x,y,t):
    d,c=x
    e,f=y
    return c*e+d*f+t*d*e,c*f


def bundle(x,y,t):
    d,c=x
    e,f=y
    return d*e,c*e+d*f-t*c*f


def test(sig,t):
    eps=0.0002
    vals=[]
    for u in (t-eps,t,t+eps):
        d,c=sig(u)
        vals.append(log(c+u*d))
    p=(vals[2]-vals[0])/(2*eps)
    pp=(vals[0]+vals[2]-2*vals[1])/eps**2
    return p,(1+t)*pp+p


if __name__=='__main__':
    primitive=[('E',lambda t:(1,1))]
    for n in range(4,7):
        D,C=gadget(n)
        primitive.append((f'K{n}-e',lambda t,D=D,C=C:(value(D,t),value(C,t))))
    output=[]
    for name,base in primitive[1:]:
        for other,extra in primitive:
            pairs=[(name,base)]
            for step in range(1,4):
                nxt=[]
                for tag,sig in pairs:
                    for desc,join in [('S',chain),('P',bundle)]:
                        if other=='E' and desc=='P' and tag.endswith('PE'):continue
                        label=tag+desc+other
                        fn=lambda t,a=sig,b=extra,j=join:j(a(t),b(t),t)
                        nxt.append((label,fn))
                        for t in [0.001,0.05,0.15,0.3,0.5,0.7,0.9,0.99]:
                            p,q=test(fn,t)
                            if p<0 and q<0:output.append((q,label,t,p))
                pairs=nxt
    print(sorted(output)[:20])
