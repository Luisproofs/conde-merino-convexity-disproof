# A Lean 4 counterexample to Conde–Merino Conjecture 2.4

The theorem `CondeMerino.not_publishedConjecture` disproves Conjecture 2.4 of Rodolfo Conde and Criel Merino. The conjecture requires the Tutte polynomial of every finite simple loopless 2-vertex-connected graph to be convex on the closed segment from $(2,0)$ to $(0,2)$. The authors define the polynomial by the edge-deletion and contraction rules R1–R3 in §1.1. [Conde and Merino, *International Journal of Mathematical Combinatorics* 2 (2009), 79–89](https://fs.unm.edu/IJMC/IJMC-2-2009.pdf) · [Authors’ copy](https://www.matem.unam.mx/~merino/online_papers/conjecture_5.pdf)

## The witness and the inequality

Start with a complete graph on vertices 0 through 4. Join 0 to 1 by a chain of five squares, entering and leaving each square through opposite corners. The chain junctions, in order, are 0, 7, 10, 13, 16 and 1. The other two corners of each square are respectively (5,6), (8,9), (11,12), (14,15) and (17,18). Keep all ten clique edges. Lean proves that the resulting graph is simple and loopless, has 19 vertices and 30 edges, is connected, and remains connected after deletion of any vertex.

Write $P(x)=T_G(x,2-x)$. The witness to failure of convexity uses weight $1/2$ between abscissae 0 and $1/128$. Lean proves the exact identity

$$
2P(1/256)-P(0)-P(1/128)
=\frac{26123280769243048353292998299952433382036731393}{2^{159}}
>\frac{1}{32}.
$$

Here $P(0)=280024$. The two other values and the full degree-20 restriction polynomial are included in the certificate. The formal convexity statement quantifies over every pair of **real** points on the segment and every real weight between zero and one. Its negation follows by inserting the displayed rational points into that inequality. [Final statement and proof](CondeMerino.lean) · [Exact values](CondeMerino/Arithmetic.lean)

## Equality with the classical Tutte polynomial

For every finite undirected multigraph, Lean proves the bivariate identity

$$
T_G(x,y)=\sum_{A\subseteq E(G)}
  (x-1)^{k(A)-k(E(G))}(y-1)^{|A|+k(A)-|V(G)|}.
$$

Here $k(A)$ counts the walk components of the spanning subgraph, including isolated vertices. The sum indexes subsets by Boolean masks of the edge positions. Lean proves that each mask of the correct length occurs exactly once, so parallel edges can be chosen independently. The theorem holds over any commutative ring. Its real specialization identifies the entire bivariate function used in the convexity proof with the subset sum. The theorems `classical_exact_excess` and `witness_classical_not_convex` give the rational certificate and the real convexity violation directly for that sum. [Universal identity](CondeMerino/RankSubset.lean) · [Counterexample for the classical definition](CondeMerino.lean)

The rank proof counts each component at its least vertex. Inserting an edge between distinct components removes exactly one such representative. Contracting a nonloop decreases rank by one even though the implementation keeps the vacated vertex as an isolated label. Splitting the subsets according to whether they contain the selected edge then proves the loop, bridge and ordinary-edge rules directly from the sum. [Graphic rank](CondeMerino/GraphicRank.lean) · [Ring operations on the Cauchy reals](CondeMerino/RealRing.lean)

## Reproduce the verification

Install the toolchain specified in `lean-toolchain` (Lean 4.36.0). The Lake package has no external dependencies. From the directory containing `lakefile.toml` run

```sh
lake build
lake env lean Audit.lean
lake env leanchecker --fresh --verbose CondeMerino
python3 tools/verify_release.py --paranoid
```

The third command rechecks the whole module and all its imports in a fresh kernel environment. The last command requires Python 3 and the checkers distributed with the pinned toolchain. It regenerates the proof source in memory and compares it byte-for-byte, checks the graph independently by rank–nullity, builds the library, and audits all listed theorem roots. It exports their complete declaration dependencies for replay by Lean’s kernel, the paranoid Lean kernel and the independent nanoda checker. The allowed axioms are exactly `propext`, `Classical.choice` and `Quot.sound`. The final negative control changes the gap numerator by one and checks that Lean rejects the altered identity. The source proof uses ordinary kernel reduction for closed exact computations. [Verification script](tools/verify_release.py) · [Clean build and fresh kernel replay](audit/kernel.txt) · [Axiom audit](audit/axioms.txt) · [Verification transcript](audit/release.txt)

## How the proof works

| Source | Content |
| --- | --- |
| [Graph](CondeMerino/Graph.lean) | Finite undirected edge lists, simplicity, walks and vertex deletion. A proof identifies a computable connectivity test with walk reachability, using cuts. |
| [Tutte](CondeMerino/Tutte.lean) | A bivariate polynomial expression is built from the empty graph, loops, bridges and ordinary edges. A contraction substitutes one endpoint label for the other in every remaining edge. Each loop and parallel edge keeps its own list occurrence. |
| [Witness](CondeMerino/Witness.lean) | The clique and five squares, the size checks, and a walk proof for every surviving vertex pair after each deletion. |
| [Restriction](CondeMerino/Restriction.lean) | Substitution of $y=2-x$ gives integer coefficient lists. Evaluation by Horner’s rule agrees with evaluation of the original bivariate expression for all rational $x$. |
| [Square chains](CondeMerino/SquareChains.lean) and [minor proofs](CondeMerino/Minors.lean) | The 19-vertex witness uses 416 distinct minors, including the empty graph. Extending the proof to the open and closed chains of lengths 0 through 5 uses 863 distinct minors in total. Each proof instantiates a graph rule and combines previously proved coefficients. |
| [Arithmetic](CondeMerino/Arithmetic.lean) | Both square-chain recurrence identities for the five attachments, the three rational evaluations, the exact gap and its sign. |
| [Real arithmetic](CondeMerino/Real.lean) | Reals are the Cauchy completion of the rationals. Addition, multiplication and order descend to the quotient, every rational Cauchy sequence is bounded, and the rational embedding preserves the operations and reflects order. |
| [Final theorem](CondeMerino.lean) | Real bivariate evaluation, the published conjecture, the concrete counterexample, and the negation of the conjecture. |

The auxiliary labels left isolated by contraction contribute no edges. The graph recursion stops at the edge count. The polynomial is defined on the full bivariate plane before any specialization. The independent Python check uses the spanning-subgraph rank–nullity formula, grouping subsets by their edge count and component partition. It accounts for all $2^{30}$ subsets, checks every binomial layer, and recovers all 21 coefficients. [Subset verifier](tools/subset_check.py)

## Historical scope

The overlap with Hiraishi, Imai, Moriyama, Okamura and Shiroshita’s 2019 work on Tutte convexity remains unresolved. The accessible project report does not specify both the relevant line and the graph hypotheses. Historical priority and the smallest possible order of a counterexample remain open questions for this release. [2019 symposium program](https://www.opt.mist.i.u-tokyo.ac.jp/hj2019/wp-content/uploads/sites/3/2019/04/program19.pdf) · [Project report](https://kaken.nii.ac.jp/ja/file/KAKENHI-PROJECT-16K12392/16K12392seika.pdf)
