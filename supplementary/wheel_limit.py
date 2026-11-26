"""Transfer eigenvalue test for wheel cores with two different simple networks."""
from math import sqrt,log
from itertools import product
from explicit_search import value
from clique_network import clique

def eigen(t,rim,spoke):
    d,c=rim
    f,b=spoke
    tr=t*d*f+2*c*f+d*b-t*c*b
    det=(f-t*b)*f*c*(t*d+c)
    return (tr+sqrt(tr*tr-4*det))/2


def evaluate(net,t):
    return tuple(value(p,t) for p in net)


if __name__=='__main__':
    edges={'E':((1,),(1,)),'SS':((2,1),(1,))}
    for m in range(4,10):
        edges[str(m)]=clique(m)
    found=[]
    for t in (.0001,.02,.1,.2,.35,.5,.7,.9):
        for (x,A),(y,B) in product(edges.items(),repeat=2):
            h=0.00005
            f,g,k=[log(eigen(u,evaluate(A,u),evaluate(B,u))) for u in (t-h,t,t+h)]
            p=(k-f)/(2*h)
            pp=(k+f-2*g)/h**2
            if p<0 and p+(1+t)*pp<0:
                found.append((p+(1+t)*pp,x,y,t,p))
    print(sorted(found)[:12])
