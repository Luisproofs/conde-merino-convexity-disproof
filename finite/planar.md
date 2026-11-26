# A planar graph whose Tutte polynomial has a strict interior peak

Make a ring of 34 squares. Each square shares one corner with its predecessor and the opposite corner with its successor. In 15 squares add the diagonal joining the two **unshared** corners. Use the first 19 squares without diagonals and the last 15 with diagonals. Write $P(x)=T_G(x,2-x)$.

This graph has 102 vertices, 151 edges and maximum degree four. Draw its shared corners on a polygon and replace each side by two short disjoint arcs with one new vertex apiece. Each diagonal fits inside its own cell. The graph is simple. For 2-vertex-connectivity, choose one arc on every polygon side to form a cycle, add each other arc as an ear, and then add the diagonals.

For this graph, exact arithmetic gives
$$
1000P(1/8)>1002P(0),\qquad 1000P(1/8)>1004P(1/4).
$$
Thus quasiconvexity already fails on a fixed rational interval for simple planar graphs of maximum degree four. The verification requires only powers of four low-degree polynomials.

## The formula

Set $u=1-x>0$. For each two-terminal cell, split its Tutte subset sum into two parts. Let $C$ sum the terms for terminals in the same component, and write the sum for separated terminals as $-uD$. Thus the ordinary cell polynomial is $V=C-uD$. A subset with $k$ spanning components and cycle rank $j$ contributes $(-u)^{k-1}u^j$ to $V$.

| cell | $C$ | $V$ |
|---|---:|---:|
| Square | $3+x$ | $2+x^2+x^3$ |
| Square with diagonal | $12-5x+x^2$ | $6+x^2+x^3$ |

For the square, a terminal-connected subset contains a whole two-edge path. The two such two-edge subsets contribute $-2u$, the four trees contribute 4, and the full square contributes $u$. The ordinary square polynomial is the cycle polynomial. For the cell with a diagonal, split on whether the diagonal is present. Its deletion leaves the square. Its contraction leaves two pairs of parallel edges in series. The terminal-connected sum of this contracted graph is $(2+u)^2$, since at each pair either one edge is used in two ways or both are used with cycle weight $u$. Its ordinary evaluation is $(x+2-x)^2=4$. Adding these respective contributions gives the second row.

For a ring of $k$ ordinary and $j$ diagonal cells with $k+j\ge3$, the closed form is
$$
 P(x)=\frac{(1+u^2)(3+x)^k(12-5x+x^2)^j
       -(2+x^2+x^3)^k(6+x^2+x^3)^j}{u}. \tag{2}
$$

Indeed, when every cell connects its terminals, closure adds one cycle, giving $u\prod C_i$. With $h\ge1$ separated cells, the core ring has $h$ components and no cycle. Besides local factors $D_i$ and $C_i$ this contributes $(-u)^{h-1}$. Summing the nonempty choices of separated cells gives $(\prod C_i-\prod V_i)/u$. Adding both terms proves (2). This count includes isolated vertices in every cell.

For a short integer check put $x=p/q$ and define
$$
 A=3q+p,\quad B=12q^2-5pq+p^2,\quad
 E=2q^3+p^2q+p^3,\quad F=6q^3+p^2q+p^3.
$$
Then (2) reads
$$
 P(p/q)=\frac{(q^2+(q-p)^2)A^k B^j q^{2k+j-2}-E^kF^j}
 {(q-p)q^{3(k+j)-1}}.
$$
Use $(p,q)=(0,8),(1,8),(2,8)$ and $(k,j)=(19,15)$ to check the two displayed inequalities by cross multiplication. A second calculation applies deletion–contraction directly to the 151 edges. [Exact verifier](verify.py)

## An elementary infinite family

Four ordinary and three diagonal cells per repeated unit give a useful closed-form family. In the variable $u$ the leading factor per unit is
$$
 f(u)=(4-u)^4(8+3u+u^2)^3.
$$
The sign of $f'(u)$ on $0<u<1$ is the sign of $4+3u-10u^2$, so $f$ has its strict maximum at $u=4/5$. The product of the ordinary cell evaluations per unit is strictly smaller than $f$ at every point of this interval: their differences from $C$ are respectively $u(2-u)^2$ and $u(8-3u+u^2)$, both positive, and all ordinary evaluations are positive. Formula (2) with $(k,j)=(4r,3r)$ consequently gives $P(1-u)^{1/r}\to f(u)$. For the three fixed points $u=7/10,4/5,9/10$ the interior value eventually exceeds both outer ones by exponentially growing factors. This argument uses only powers of explicit polynomials. The previous large-girth proof additionally places violations arbitrarily close to $(1,1)$ and remains available separately.
