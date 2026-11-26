"""All labelled simple networks on up to six vertices with terminals 0 and 1."""
from itertools import combinations
from math import exp
from networks import refined_logs
from substitutions import component_counts


def subset_sum(values, m):
    for bit in range(m):
        step = 1 << bit
        for i in range(0,len(values),2*step):
            for j in range(i+step,i+2*step):
                values[j] += values[j-step]
    return values


def three_counts(n, m, comps):
    idx = range(1 << m)
    a = subset_sum([(-1)**(n+comps[i]+i.bit_count()) for i in idx],m)
    c = subset_sum([(-1)**(1+comps[i]) for i in idx],m)
    b = subset_sum([int(comps[i]==1 and i.bit_count()==n-1) for i in idx],m)
    return a,c,b


def terminal_records(n):
    edges = list(combinations(range(n),2))
    m = len(edges)
    comp = component_counts(n,edges)
    contracted = [comp[i|1] for i in range(1<<m)] # first edge is (0,1)
    a,c,b = three_counts(n,m,comp)
    neutral,cyclic,f = three_counts(n-1,m,contracted)
    for i in range(1<<m):
        if comp[i]==1 and cyclic[i] > 0:
            yield (a[i],(a[i]-neutral[i])//2,cyclic[i],(cyclic[i]-c[i])//2,b[i],f[i]),(n,hex(i))


if __name__ == '__main__':
    nets = dict(entry for n in range(2,7) for entry in terminal_records(n))
    print('distinct states',len(nets))
    for d in range(3,13):
        for name,fun in [('product',lambda a,c:(a+c)/2),('max',max)]:
            def cost(net):
                return fun(*refined_logs(d,net))*2/d
            net=min(nets,key=cost)
            print(d,name,net,nets[net],round(exp(cost(net)),9))
