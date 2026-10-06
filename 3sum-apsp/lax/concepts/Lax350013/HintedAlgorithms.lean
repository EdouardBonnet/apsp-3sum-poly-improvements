/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Modified for the independent Lax packaging by Édouard Bonnet, 2026.
Derived from 3sum-apsp/EndStatement.lean / PaperStatements.lean at upstream commit e1a4e6508154ea59f030480661590a9fe3018011.
Changes: Lax module/namespace layout, separated concepts and proofs, archive
annotations, and compatibility with the archive Lean/mathlib environment.
See NOTICE and README.md in the submission root for provenance and scope.
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Lax350013.HintedMatrixVector
import Lax350013.MatrixParameters

/-!
---
title: Improved algorithms with thin hints
type: theorem
---
Corollary 40 supplies explicit and general phase-time savings for the three hinted Boolean matrix-vector problems. Theorem 4 contradicts their conjectured trade-offs in the stated thin-hint regimes, conditional on the displayed numerical lower bounds for rectangular multiplication exponents. Those lower bounds are hypotheses, not independently verified facts about matrix-multiplication exponents.
-/

namespace Lax350013.HintedAlgorithms

open Finset
open Lax350013.WordRAM
open Lax350013.RAMResources
open Lax350013.ThinMatrices
open Lax350013.HintedMatrixVector
open Lax350013.MatrixParameters

/-- **Corollary 40**, the running times of its first paragraph (also in **Theorem 4**): for
Conjectures 5.2 and 5.7 and "every 0 < τ < 1/18: Phase 2 takes O(n^{2−0.063τ}) time and Phase 3
takes O(n^{1+0.437τ}) time"; for Conjecture 5.12 and "every 0 < τ₁ < τ₂/18: Phase 3 takes
O(n^{1+τ₂−0.063τ₁}) time and Phase 4 takes O(n^{τ₂+0.437τ₁}) time, with polynomial Phase 1 and a
Phase 2 that only stores I".  (Theorem 4 prints the first two bounds only.)

NOTE.  `τ₂ < 1` is assumed: it is the standing assumption of Section 5.4 ("for constants τ, τ_i ∈
(0,1)").  The words "only stores I" are read as `O(n^{τ₁})` time. -/
def Corollary_40_times : Prop :=
  (∀ τ : ℝ, 0 < τ → τ < 1 / 18 →
    AchievesVHinted τ (2 - 0.063 * τ) (1 + 0.437 * τ) ∧
      AchievesMvHinted τ (2 - 0.063 * τ) (1 + 0.437 * τ)) ∧
  ∀ τ₁ τ₂ : ℝ, 0 < τ₁ → τ₁ < τ₂ / 18 → τ₂ < 1 →
    AchievesUMvHinted τ₁ τ₂ τ₁ (1 + τ₂ - 0.063 * τ₁) (τ₂ + 0.437 * τ₁)

/-- **The proof of Corollary 40**, paragraph "General τ": the running times.  (For this range the
corollary itself says only that the conjectures fail: `Corollary_40_fail`.)  For every `0 < τ < ε*`
there is a `γ > 0` with "Phase 2 in O(n²/D^γ) = O(n^{2−γτ}) time and Phase 3 in O(n D^{1/2}) =
O(n^{1+τ/2}) time"; and for every `0 < τ₁ < ε* τ₂` (and `τ₂ < 1`) there is a `γ > 0` with Phase 2 in
`O(n^{τ₁})`, Phase 3 in `O(n^{1+τ₂−γτ₁})` and Phase 4 in `O(n^{τ₂+τ₁/2})` time.

NOTE.  For Conjecture 5.12 ("we use the same blocks") the three bounds are those that the argument
gives, with `D^γ` and `D^{1/2}` in place of `D^{0.063}` and `D^{0.437}`.  On `τ₂ < 1` see the NOTE
at `Corollary_40_times`. -/
def Corollary_40_general_times : Prop :=
  (∀ τ : ℝ, 0 < τ → τ < epsStar → ∃ γ : ℝ, 0 < γ ∧
    AchievesVHinted τ (2 - γ * τ) (1 + τ / 2) ∧ AchievesMvHinted τ (2 - γ * τ) (1 + τ / 2)) ∧
  ∀ τ₁ τ₂ : ℝ, 0 < τ₁ → τ₁ < epsStar * τ₂ → τ₂ < 1 → ∃ γ : ℝ, 0 < γ ∧
    AchievesUMvHinted τ₁ τ₂ τ₁ (1 + τ₂ - γ * τ₁) (τ₂ + τ₁ / 2)

/-- **Corollary 40** (also **Theorem 4**), "fail": Conjectures 5.2 and 5.7 of
[vdBNS19], read as statements about programs of this machine, fail for every `0 < τ < τ₀`, and
Conjecture 5.12 fails for every `0 < τ₁ < τ₀ τ₂` (with `τ₂ < 1`), "whatever the value of ω".

The exponents of rectangular matrix multiplication are not defined here.  `ω`, `ω₂`, `ω₃` stand for
`ω(1,1,τ) = ω(1,τ,1)`, `ω(1,τ₁,1)`, `ω(τ₂,τ₁,1)`, and the statement is made for all real numbers
that satisfy the lower bounds of Corollary 40, "ω(1,1,τ) = ω(1,τ,1) ≥ 2 and ω(τ₂,τ₁,1) ≥ 1 + τ₂
because of the input and output sizes"; the bound `2 ≤ ω₂` is the first of these at `τ = τ₁`.  That
the true exponents satisfy these bounds is not proved here. The paper has `τ₀ = 1/18` in the first
paragraph, `ε*` in the second, and `0.1204` in Theorem 4.

NOTE.  `τ₂ < 1` is assumed; see the NOTE at `Corollary_40_times`. -/
def Corollary_40_fail (τ₀ : ℝ) : Prop :=
  (∀ τ ω : ℝ, 0 < τ → τ < τ₀ → 2 ≤ ω →
    ¬ HintedMv.Conjecture52 (AchievesVHinted τ) ω τ ∧
      ¬ HintedMv.Conjecture57 (AchievesMvHinted τ) ω τ) ∧
  ∀ τ₁ τ₂ ω₂ ω₃ : ℝ, 0 < τ₁ → τ₁ < τ₀ * τ₂ → τ₂ < 1 → 2 ≤ ω₂ → 1 + τ₂ ≤ ω₃ →
    ¬ HintedMv.Conjecture512 (AchievesUMvHinted τ₁ τ₂) ω₂ ω₃ τ₁ τ₂

/-- **Theorem 4**: "The v-hinted Mv, Mv-hinted Mv, and uMv-hinted uMv conjectures of
[vdBNS19] [...] are refuted in the regime of thin hints.  For hint dimension t = n^τ with 0 < τ <
1/18, the phase after the hint takes O(n^{2−0.063τ}) time and the phase after the vector
O(n^{1+0.437τ}) time [...]. Correspondingly, the uMv version [...] fails for τ₁ < τ₂/18.  All three
fail, with smaller savings, for every τ < 0.1204 (for the uMv version, τ₁ < 0.1204 τ₂)."  The three
parts follow the sentences of the theorem.  (The first contains also the running times of the uMv
version, which are printed in Corollary 40 only; the second follows from the third.)

NOTE.  For the uMv version `τ₂ < 1` is assumed; see the NOTE at `Corollary_40_times`. -/
def Theorem_4 : Prop :=
  Corollary_40_times ∧ Corollary_40_fail (1 / 18) ∧ Corollary_40_fail 0.1204

/-- Improved algorithms with thin hints: Corollary 40 times. -/
axiom explicitTimes : Corollary_40_times


/-- Improved algorithms with thin hints: Corollary 40 general times. -/
axiom generalTimes : Corollary_40_general_times


/-- Improved algorithms with thin hints: Theorem 4. -/
axiom theorem4 : Theorem_4

end Lax350013.HintedAlgorithms
