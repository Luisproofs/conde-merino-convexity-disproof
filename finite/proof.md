# Tutte convexity fails on 19 vertices

**Theorem.** Take a $K_5$ with two distinguished vertices $s,t$. Add a chain of five squares from $s$ to $t$, entering and leaving each square at opposite corners. Consecutive squares meet in one vertex. Keep the edge $st$. For the resulting simple 2-connected graph $G$,
$$
P(x)=T_G(x,2-x)=280024+5612x-3278x^2+O(x^3).
$$
In particular $P''(0)=-6556$. By continuity $P''$ is negative on an interval inside $(0,2)$, contradicting the convexity required by Conde and Merino's Conjecture 2.4. [Published statement](https://fs.unm.edu/IJMC/ComparingTheNumberOfAcyclicAndTotallyCyclicOrientations.pdf)

The chain adds four junctions, ten intermediate vertices and twenty edges. This gives 19 vertices and 30 edges. To see 2-vertex-connectivity, first add a path of length ten between $s$ and $t$. Then add five paths of length two, one alongside each successive two-edge section of that path. Each addition has distinct existing endpoints and fresh internal vertices. After any one vertex deletion every surviving part of the new path still meets the connected remainder. These additions also preserve simplicity.

## Proof

Write $P_J=T_J(x,2-x)$. For distinct vertices $v,w$ of a connected graph $J$, let $J/vw$ identify them while keeping every edge. Adding a two-edge path between them gives $(1+x)P_J+P_{J/vw}$ by deletion–contraction. Deleting the first edge leaves a bridge, and contracting it leaves a single added edge. Apply the same identity a second time. Upon identifying $v,w$, the first path becomes a two-edge cycle, of evaluation $x+(2-x)=2$, attached at one vertex. Thus adding a square through its opposite corners gives
$$
(1+x)^2 P_J+(3+x)P_{J/vw}. \tag{1}
$$
Here Tutte polynomials multiply at a one-vertex union, as follows by choosing edge subsets independently and adding their rank deficiencies and cycle ranks.

Let $A_i$ be the polynomial of the clique with an open chain of $i$ squares attached at $s$, and $B_i$ its polynomial after identifying the free end with $t$. At $i=0$ the free end is $s$. A one-vertex attachment of a square multiplies the polynomial by $T_{C_4}(x,2-x)=2+x^2+x^3$. Closing the next square is exactly (1). Hence
$$
 A_{i+1}=(2+x^2+x^3)A_i,\qquad
 B_{i+1}=(1+x)^2A_i+(3+x)B_i,\qquad P=B_5.
$$

The initial polynomials $A_0=P_{K_5}$ and $B_0=P_{K_5/st}$ have the following coefficient lists in increasing degree.

| Polynomial | Coefficients |
|---|---|
| $A_0$ | 544, −932, 796, −374, 106, −16, 1 |
| $B_0$ | 680, −1680, 1898, −1240, 499, −123, 17, −1 |

To reproduce the initial values, sum over subsets $S$ of the ten labelled clique edges. If $k$ is the number of spanning components, including isolated vertices, and $j=|S|-n+k$, the summand in the Tutte definition is $(-1)^{k-1}(1-x)^{k-1+j}$. Use $n=5$ for the clique. For the identified graph use $n=4$ and identify $s,t$ before counting components, keeping the loop and parallel edges.

Keeping only the constant, linear and quadratic terms in the five recurrence steps gives the claimed sign.

| $i$ | First three coefficients of $A_i$ | First three coefficients of $B_i$ |
|---:|---:|---:|
| 0 | 544, −932, 796 | 680, −1680, 1898 |
| 1 | 1088, −1864, 2136 | 2584, −4204, 3490 |
| 2 | 2176, −3728, 5360 | 8840, −9716, 5762 |
| 3 | 4352, −7456, 12896 | 28696, −19684, 7650 |
| 4 | 8704, −14912, 30144 | 90440, −29108, 5602 |
| 5 | 17408, −29824, 68992 | **280024, 5612, −3278** |

**Rational certificate.** At $h=1/256$, the same recurrence gives
$$
2P(h)-P(0)-P(2h)
=\frac{26123280769243048353292998299952433382036731393}{2^{159}}
>\frac1{32}.
$$
Convexity requires this difference to be nonpositive. This second certificate uses only rational arithmetic. The independent verifier computes the full graph polynomial by deletion–contraction, compares it with the recurrence, and checks connectivity after each vertex deletion. [Verifier](verify.py)

### Seven-term hand check of the clique

Put $u=1-x$, $q=-u^2$, $y=1+u$. For each partition shape of five vertices the table gives the number $\ell$ of parts, the number $e$ of pairs within parts and the number $m$ of labelled partitions.

| shape | $\ell$ | $e$ | $m$ |
|---|---:|---:|---:|
| 11111 | 5 | 0 | 1 |
| 2111 | 4 | 1 | 10 |
| 221 | 3 | 2 | 15 |
| 311 | 3 | 3 | 10 |
| 32 | 2 | 4 | 10 |
| 41 | 2 | 6 | 5 |
| 5 | 1 | 10 | 1 |

With $(q)_\ell=q(q-1)\cdots(q-\ell+1)$, sum $m(q)_\ell y^e$ and divide by $qu^4$ for $A_0$. For $B_0$, multiply each summand by $e/10$ and divide the sum by $qu^3$. To verify the formulas, initially take independent $q,u$ and weight each coloring with $q$ colors by $1+u$ per monochromatic edge. Group by color classes. Forcing $s,t$ to have equal colors selects a fraction $e/10$ of each shape by symmetry. Alternatively, expanding the product of edge weights gives $\sum_S q^{k(S)}u^{|S|}$. Both expressions are polynomial in $q$ and agree for positive integers $q$, so one may substitute $q=-u^2$. Division by $qu^{n-1}$ then gives the connected-graph Tutte polynomial at $(x,2-x)$, wherever the denominator is nonzero.

### Scope and formalization

The size of a smallest counterexample remains undetermined. The overlap with Hiraishi et al.'s 2019 proceedings paper remains unresolved. [Priority record](../review.md)

The rational midpoint certificate is now formalized in Lean 4, including the equivalence of the recursive Tutte evaluation with the classical rank-subset definition. See [formal verification](../lean/README.md).
