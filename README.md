# A counterexample to the Conde–Merino convexity conjecture

An AI-assisted mathematical investigation of Conjecture 2.4 in Rodolfo Conde and Criel Merino's 2009 paper [Comparing the Number of Acyclic and Totally Cyclic Orientations with that of Spanning Trees of a Graph](https://www.matem.unam.mx/~merino/online_papers/conjecture_5.pdf).

## Main result

Let G be the complete graph K₅ with a chain of five squares added between two distinct vertices, using opposite corners as terminals in each square. Keep the original clique edges. The resulting graph is simple and 2-vertex-connected, with 19 vertices and 30 edges.

Writing $P(x)=T_G(x,2-x)$ for the restricted Tutte polynomial, we obtain

$$
P(x)=280024+5612x-3278x^2+O(x^3).
$$

In particular, $P''(0)=-6556$. The explicit rational midpoint certificate is

$$
2P(1/256)-P(0)-P(1/128)>1/32>0.
$$

This contradicts convexity on the segment from (0,2) to (2,0). It does **not** disprove the original Merino–Welsh conjecture or its additive or multiplicative versions.

## Proofs and verification

- [Research preprint (PDF)](preprint/conde-merino.pdf)
- [LaTeX source](preprint/conde-merino.tex)

- [Elementary proof of the 19-vertex counterexample](finite/proof.md)
- [Lean 4 source and instructions](lean/README.md)
- [Final Lean theorem](lean/CondeMerino.lean): `CondeMerino.not_publishedConjecture`
- [Exact rational certificate](lean/CondeMerino/Arithmetic.lean)
- [Build and fresh kernel replay log](lean/audit/kernel.txt)
- [Axiom audit](lean/audit/axioms.txt)
- [Independent rank–nullity computation](lean/tools/subset_check.py)
- [102-vertex planar counterexample and elementary infinite family](finite/planar.md)
- [Separate large-girth infinite-family argument](convexity-proof.md)
- [Literature and priority assessment](review.md)

The strengthened Lean development proves `CondeMerino.tutte_eq_classicalTutte`, the general identity between deletion–contraction and the classical rank-subset definition for finite undirected multigraphs, and `CondeMerino.witness_classical_not_convex`, the violation for the classical definition. See [the general equivalence theorem](lean/CondeMerino/RankSubset.lean), [the classical counterexample theorem](lean/CondeMerino.lean), and the [updated axiom audit](lean/audit/axioms.txt). An independent AI-assisted audit using Fable 5.2 reproduced the finite calculations by a different algorithm; this is not external peer review.

## Reproduce

From the repository root, with Lean 4.36.0 (pinned in `lean/lean-toolchain`):

```sh
cd lean
lake build
lake env lean Audit.lean
lake env leanchecker --fresh --verbose CondeMerino
python3 tools/verify_release.py --paranoid
```

For the more extensive verification, see [the Lean README](lean/README.md). The recorded audit reports only standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) for the final theorem. The Lean package has no external Lake dependencies. The recorded finite verification is separate from the conventional proofs of the additional results.

From the repository root, the Python checks can also be reproduced with the standard library:

```sh
python3 finite/verify.py
python3 verify_convexity.py
python3 lean/tools/subset_check.py
```

See [the search record](finite/search-notes.md) and [supplementary exploratory scripts](supplementary/README.md). The search was bounded; it was not a census of all small graphs or a proof of minimality.

## Research status and attribution

The 19-vertex disproof has a complete Lean formalization and recorded successful kernel checks. The planar and infinite-family results are not Lean-formalized. This work has not undergone external peer review. The precise overlap with Hiraishi, Imai, Moriyama, Okamura and Shiroshita's 2019 proceedings paper, *Smallest Counterexamples for Convexity and Log-concavity of the Tutte Polynomial*, remains unresolved because its full text was not obtained. Recent work by Benedek Váli ([arXiv:2611.15008](https://arxiv.org/abs/2611.15008), November 2026) discusses the convexity strengthening; this is not conclusive evidence of priority. No claim of first-discovery priority or minimality is made. Independent review is welcome.

Research directed by Luis Gonzalez, with Astra 6.2 through OpenAI Codex used for AI-assisted mathematical discovery, proof development, computations and formalization.

Contact: [nftprogrammer@gmail.com](mailto:nftprogrammer@gmail.com) · [@100xluis on X](https://x.com/100xluis).
