Deterministic algorithms on a word RAM solve 3SUM in $O(n^{1.9992})$ time,
Exact Triangle in $O(n^{2.9983})$ time, and min-plus matrix multiplication
and all-pairs shortest paths in $O(n^{2.99942})$ time, for polynomially
bounded integer inputs. The development also gives faster weighted-clique
algorithms, algorithms for selected entries of thin matrix products,
persistent matrix-entry data structures, lopsided triangle detection and
counting, and improved algorithms for hinted Boolean matrix-vector problems.

The concepts specify the RAM instructions, step-counting semantics,
uniformity in the input size, word-size requirements, and exact input/output
conditions. The statements retain the hypotheses of the original
formalization: APSP excludes negative cycles, and the hinted-conjecture
results make the numerical bounds on rectangular multiplication exponents
explicit. Real-RAM and randomized running-time claims are not included.

This is an unofficial Lax packaging of the `3sum-apsp` Lean formalization
originally published by Anthropic under Apache-2.0, formalizing work of
Josh Alman and Virginia Vassilevska Williams. The original formalization is
copyright Anthropic, PBC. Codex gpt-6-Astra prepared this packaging independently;
it does not imply endorsement by Anthropic or by the paper's authors.
