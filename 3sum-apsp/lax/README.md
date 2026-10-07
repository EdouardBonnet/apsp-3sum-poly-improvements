# 3SUM and APSP for the Lax Lean Archive

This is an independent Lax packaging of Anthropic's formalization of Josh
Alman and Virginia Vassilevska Williams,
[*Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse
Lopsided Graphs*](https://arxiv.org/abs/2610.06783v1).

The public fork is
[`EdouardBonnet/apsp-3sum-poly-improvements`](https://github.com/EdouardBonnet/apsp-3sum-poly-improvements/tree/lax-3sum-apsp);
the submission is in `3sum-apsp/lax`.

The source is the `3sum-apsp` directory of
[`anthropics/formal-math`, commit
`e1a4e6508154ea59f030480661590a9fe3018011`](https://github.com/anthropics/formal-math/tree/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp).
The fork retains the complete upstream Git history. Upstream files outside
this `lax` directory remain unchanged.

The original formalization is copyright 2026 Anthropic, PBC. The Lax
packaging was prepared independently by Codex gpt-6-Astra and does not imply
endorsement by Anthropic or by the paper's authors. Lax submission ownership
belongs to the submitting GitHub account, `EdouardBonnet`; attribution does
not assign ownership to upstream contributors.

## Scope

The concept package exposes the word RAM, its uniform running-time
semantics, persistent queries and phased inputs, and the following results.

| Result | Bound or scope |
| --- | --- |
| Exact Triangle | Deterministic `O(n^2.9983)` |
| 3SUM at three distinct positions | Deterministic `O(n^1.9992)` |
| Min-plus product and APSP | Deterministic `O(n^2.99942)` |
| Zero-, minimum- and maximum-weight k-clique | `O(n^(k - 0.0017 floor(k/3)))` for fixed `k >= 3` |
| Selected entries of thin matrix products | Theorems 1, 5, 25 and 30; Corollaries 26 and 32 |
| Thin matrix entry data structures | Theorems 3, 24 and 30; Corollaries 26 and 31 |
| Lopsided triangle detection and counting | Corollaries 15 and 16 |
| Hinted Boolean matrix-vector problems | Theorem 4 and Corollary 40, with the explicit exponent hypotheses |

The integer-input problems assume polynomially bounded input magnitudes.
APSP assumes no negative cycles and records unreachable pairs explicitly.
Programs are fixed before the input size and instance, and must work at
every sufficiently large logarithmic word size.

The upstream artifact does **not** establish all running-time claims of
the paper. In particular, its real-RAM/randomized running-time claims and
the machine running times of Section 5.1 are outside this submission's
certified algorithm statements. Rectangular matrix-multiplication exponents
are numerical parameters in the hinted conjectures: their named lower
bounds are explicit hypotheses. Consult the unchanged
[upstream scope discussion](../README.md#what-is-not-proved) for details.

## Layout and reproducibility

`concepts/` contains readable definitions and Lax statement axioms.
`proofs/` contains the transitive dependencies of the adapted algorithm proofs
and annotated certificates. Other upstream results remain available in the
unchanged development outside this directory.
The two packages use Lax's active Lean 4.33.0 environment and pinned mathlib,
while the untouched upstream development retains its 4.33.1 configuration.
`package.py` records the extraction, namespace changes and compatibility
adaptations. Run it from any directory to regenerate the Lean sources.

The RAM instructions and interpreter, persistent-query and phased-execution
relations, APSP path relation and thin-matrix input records are shared
between concepts and proofs. The remaining duplicated
definitions are compared by Lean's definitional equality when checking
each annotated certificate. No challenge file containing `sorry` is
imported into the Lax package.

From this directory:

```sh
python3 package.py
python3 package.py --check
lax build
lax serve
```

From the repository root, after committing and pushing:

```sh
lax submit 3sum-apsp/lax
```

Registration is a separate, irreversible archive operation; this packaging
is intended to be submitted as a replaceable draft for review.

Every use of an exposed machine-level theorem imports and uses its concept
statement, including uses inside intermediate helper lemmas. The generator
preserves the theorem's own proof and replaces references to that theorem
throughout the adapted library with the corresponding concept axiom. Lax
therefore records these dependencies in the proof network. The proof package
requires only mathlib and this submission's concepts.
In particular, the five rational-exponent headline claims depend
on the more detailed running-time statements. Internal procedure-level
reductions and compiler correctness remain in the proof library: a theorem
asserting the existence of a RAM program is not silently substituted for
the stronger callable-procedure contract used by those reductions.
Auxiliary theorems in retained upstream modules are preserved intentionally,
including useful variants that can cause Lax's `unused-lemma` warnings.

## Licensing and modifications

The root repository license, upstream project `LICENSE` and `NOTICE`, and
the copies of `LICENSE` and `NOTICE` in this submission retain their
upstream contents. In particular, the NOTICE preserves the attribution and
permission concerning quoted paper passages, and the mathlib-derived
proofs credited to Patrick Stevens and Bolton Bailey.

Every adapted Lean source retains the upstream copyright/SPDX header and
carries a prominent modification notice naming its source and pinned
commit. The packaging script and new documentation are also distributed
under Apache-2.0. No trademark licence or endorsement is asserted.
