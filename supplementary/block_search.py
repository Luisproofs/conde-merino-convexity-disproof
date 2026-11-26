"""Exact search over recursively constructed blocks at t=0, retaining three coefficients."""
from clique_network import clique

def plus(*args):
    return tuple(map(sum,zip(*args)))

def mul(x,y):
    a,b,c=x
    d,e,f=y
    return (a*d,a*e+b*d,a*f+b*e+c*d)

def shift(x,sign):
    return (0,sign*x[0],sign*x[1])

def combine(left,right,par):
    d,c=left
    e,f=right
    mid=plus(mul(c,e),mul(d,f))
    if par:return mul(d,e),plus(mid,shift(mul(c,f),-1))
    return plus(mid,shift(mul(d,e),1)),mul(c,f)


def examine(P):
    v,p,q=P
    # log P decreases in x, and has negative second derivative in log x at 1.
    return p<0 and (2*q+p)*v-p*p<0


def solve(n,limit):
    D,C=clique(n)
    levels=[{}, {(D[:3],C[:3]):'N'}]
    for k in range(2,limit+1):
        pending={}
        for j in range(1,k//2+1):
            for x,s in levels[j].items():
                for y,t in levels[k-j].items():
                    for par in (False,True):
                        v=combine(x,y,par)
                        if v in pending:continue
                        d,c=v
                        label=('P' if par else 'S')+'('+s+','+t+')'
                        for target,p in [('D',d),('T',plus(c,shift(d,1)))]:
                            if examine(p):return k,target,p,label
                        pending[v]=label
        levels.append(pending)
    return None

if __name__=='__main__':
    for n in range(4,10): print(n,solve(n,10))
