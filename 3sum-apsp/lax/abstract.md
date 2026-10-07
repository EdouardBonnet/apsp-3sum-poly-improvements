Deterministic algorithms on a word RAM solve 3SUM in $O(n^{1.9992})$ time,
Exact Triangle in $O(n^{2.9983})$ time, and min-plus matrix multiplication
and all-pairs shortest paths in $O(n^{2.99942})$ time, for polynomially
bounded integer inputs. The development also gives faster weighted-clique
algorithms, algorithms for selected entries of thin matrix products,
persistent matrix-entry data structures, lopsided triangle detection and
counting, and improved algorithms for hinted Boolean matrix-vector problems.

The concepts specify the RAM instructions, step-counting semantics,
uniformity in the input size, word-size requirements, exact input/output
conditions, and the memory-preserving procedure contracts used by the
algorithmic reductions. The statements retain the hypotheses of the original
formalization: APSP excludes negative cycles, and the hinted-conjecture
results make the numerical bounds on rectangular multiplication exponents
explicit. Real-RAM and randomized running-time claims are not included.

The original algorithm was discovered by Claude at Anthropic. Josh Alman
and Virginia Vassilevska Williams subsequently simplified, strengthened and
extended the results and wrote the paper, as explained in its
[acknowledgments and methodology](https://arxiv.org/html/2610.06783v1).
Anthropic also produced the original Lean formalization.

This is an unofficial Lax packaging of Anthropic's Apache-2.0 `3sum-apsp`
development. The original formalization is copyright Anthropic, PBC.
Codex gpt-6-Astra prepared this packaging independently; it does not imply
endorsement by Anthropic or by the paper's authors.
