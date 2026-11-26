"""Compare two-terminal networks using rigorous local upper bounds and tree entropy."""
from math import log, exp


def dual(net):
    a,p,c,q,t,f = net
    return c,q,a,p,f,t


def series(left,right):
    a,p,c,q,t,f = left
    b,h,d,k,u,v = right
    return a*b,p*h,c*d-2*q*k,(c-q)*(d-k)-(c-2*q)*(d-2*k),t*u,t*v+f*u


def tree_entropy(d):
    return (d-1)*log(d-1) - (d/2-1)*log(d*(d-2))


def candidates(limit):
    levels = [set(),{(2,1,2,1,1,1)}]
    for n in range(2,limit+1):
        nets = set()
        for i in range(1,n//2+1):
            for x in levels[i]:
                for y in levels[n-i]:
                    nets.add(series(x,y))
                    nets.add(dual(series(dual(x),dual(y))))
        levels.append(nets)
    return levels


if __name__ == '__main__':
    levels = candidates(10)
    print("state counts by number of edges",list(map(len,levels[1:])))
    all_nets = set.union(*levels[1:])
    for d in range(3,11):
        density = 2/d
        def cost(x,kind):
            a,p,c,q,t,f=x
            upper = log(max(a,c)) if kind=='max' else (log(a)+log(c))/2
            return upper - density*log(t) - (1-density)*log(f) - density*tree_entropy(d)
        for kind in ('max','product'):
            net = min(sorted(all_nets),key=lambda v: cost(v,kind))
            print(d,kind,net,round(exp(cost(net,kind)),9))

def refined_logs(d, net):
    a,p,c,g,t,f = net
    x = a/p
    if x >= d-1:
        acyclic = (d/2)*log(a)
    else:
        tutte = log(d-1)+(d/2-1)*log((d-1)**2/((d-1)**2-x))
        acyclic = (d/2-1)*log(a-p)+log(p)+tutte
    cyclic = (d/2)*log(c)+0.5*log(1-2*(g/c)**d)
    tree = log(t)+(d/2-1)*log(f)+tree_entropy(d)
    return acyclic-tree, cyclic-tree

if __name__ == '__main__':
    for d in range(3,17):
        def objective(net):
            left,right = refined_logs(d,net)
            return (left+right)/2
        net = min(sorted(all_nets),key=objective)
        print("refined",d,net,round(exp(objective(net)*2/d),9))
