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
import Lax350013.ThinMatrices
import Lax350013.MatrixParameters

/-!
---
title: Thin matrix preprocessing and query trade-offs
type: theorem
---
Theorem 24 and Corollary 31 give preprocessing time/space and per-entry query bounds. For every $\varepsilon<\varepsilon^*$ and $q>0$, some $\gamma>0$ permits $O(N^2\log^2 D/D^\gamma)$ preprocessing and $O(D^q\log D)$ queries when $2\leq D\leq N^\varepsilon$. Corollary 31 supplies explicit parameter choices.
-/

namespace Lax350013.MatrixTradeoffs

open Finset
open Lax350013.WordRAM
open Lax350013.RAMResources
open Lax350013.ThinMatrices
open Lax350013.MatrixParameters

/-- The hypotheses on the input in Corollaries 31 and 32 and Theorems 24 and 25: "where 2 ≤ D ≤
N^ε", with entries "of absolute value at most N^{O(1)}".  `lo` is the lower bound on `D`, which is 2
there.  (`N ≥ 1` follows if `lo = 2`; for `lo = 1` it excludes `N = 0`, `D = 1`, `ε = 0`, where the
bounds with the factor `N²` would be 0.) -/
def thinDom (lo : ℕ) (ε : ℝ) (c₀ : ℕ) (x : ThinPair) : Prop :=
  1 ≤ x.N ∧ lo ≤ x.D ∧ (x.D : ℝ) ≤ (x.N : ℝ) ^ ε ∧ x.U = x.N ^ c₀

/-- The conclusion of Theorem 24 and Corollary 31: there is a data structure for the inputs with
`2 ≤ D ≤ N^ε` with preprocessing in `O(N² log² D/D^γ)` time and space and queries in
`O(D^q log D)` time. -/
def HasDataStructure (ε γ q : ℝ) : Prop :=
  ∀ c₀ : ℕ, ∃ (P Q : List Instr) (qI qJ qOut : ℤ) (b : ℕ) (C : ℝ),
    IsDataStructure P Q qI qJ qOut b [] (thinDom 2 ε c₀)
      (fun x => C * ((x.N : ℝ) ^ 2 * Real.log x.D ^ 2 / (x.D : ℝ) ^ γ))
      (fun x => C * ((x.N : ℝ) ^ 2 * Real.log x.D ^ 2 / (x.D : ℝ) ^ γ))
      (fun x => C * ((x.D : ℝ) ^ q * Real.log x.D))

/-- **Theorem 24**: "For every ε < ε*, and every q > 0, there is a γ > 0 such that the
following holds. Given as input matrices X ∈ ℤ^{N×D} and Y ∈ ℤ^{D×N}, where 2 ≤ D ≤ N^ε, whose
entries are integers of absolute value at most N^{O(1)}, we can preprocess them deterministically in
O(N² log² D/D^γ) time and space, after which any single entry (XY)[I,J] can be computed
deterministically in O(D^q log D) time." -/
def Theorem_24 : Prop :=
  ∀ ε q : ℝ, ε < epsStar → 0 < q → ∃ γ : ℝ, 0 < γ ∧ HasDataStructure ε γ q

/-- **Corollary 31**: "Let c > 10 and 0 < θ < 0.9, let ρ_c := 9/(c−1), and let γ := θ
ln(1/ρ_c)/ln 4 > 0 and q := (H(θ) + θ ln 9)/ln 4.  Given as input matrices X ∈ ℤ^{N×D} and Y ∈
ℤ^{D×N} whose entries are integers of absolute value at most N^{O(1)}, where 2 ≤ D ≤ N^ε and ε <
R_c(γ), with R_c as in (11), we can preprocess them deterministically in O(N² log² D/D^γ) time and
space, after which any single entry (XY)[I,J] can be computed deterministically in O(D^q log D)
time.  The constants hidden in the O(·) depend on c, θ, and ε." -/
def Corollary_31 : Prop :=
  ∀ c θ ε : ℝ, 10 < c → 0 < θ → θ < 0.9 → ε < Rc c (gammaOf c θ) →
    HasDataStructure ε (gammaOf c θ) (qOf θ)

/-- For every `ε < ε₀` and every `q > 0` there is a `γ > 0` such that, whenever `D ≤ N^ε`, the pair
can be preprocessed in `O(N²/D^γ)` time (and space), after which any single entry can be computed in
`O(D^q)` time.  The paper has this sentence with `ε₀ = 0.1204` (Theorem 3).

NOTE.  The paper states no lower bound on `D` and `N` here, and speaks of time only; `D ≥ 1` and
`N ≥ 1` are assumed, and the space is bounded like the time.  Theorem 24 has logarithmic factors and
assumes `D ≥ 2`; on the step from there Section 4.1 says: "The logarithmic factors in both theorems
can be removed by halving γ and applying Theorem 24 with q/2 in place of q; for D = 1 the bounds are
trivial." -/
def DataStructureBelow (ε₀ : ℝ) : Prop :=
  ∀ ε q : ℝ, ε < ε₀ → 0 < q → ∃ γ : ℝ, 0 < γ ∧
    ∀ c₀ : ℕ, ∃ (P Q : List Instr) (qI qJ qOut : ℤ) (b : ℕ) (C : ℝ),
      IsDataStructure P Q qI qJ qOut b [] (thinDom 1 ε c₀)
        (fun x => C * ((x.N : ℝ) ^ 2 / (x.D : ℝ) ^ γ))
        (fun x => C * ((x.N : ℝ) ^ 2 / (x.D : ℝ) ^ γ))
        (fun x => C * (x.D : ℝ) ^ q)

/-- Thin matrix preprocessing and query trade-offs: Theorem 24. -/
axiom theorem24 : Theorem_24


/-- Thin matrix preprocessing and query trade-offs: Corollary 31. -/
axiom corollary31 : Corollary_31

end Lax350013.MatrixTradeoffs
