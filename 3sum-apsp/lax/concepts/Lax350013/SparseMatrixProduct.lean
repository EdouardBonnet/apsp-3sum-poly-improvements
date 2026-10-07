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
import Lax350013.MatrixPreprocessing
import Lax350013.CallableAlgorithms

/-!
---
title: Faster computation of selected matrix-product entries
type: theorem
---
Theorem 1 computes up to $N^2/\sqrt D$ selected entries in $O(N^2/D^{0.063})$ time when $1\leq D$ and $D^{18}\leq N$. More generally, for $D\leq N^\varepsilon$, $\varepsilon<0.1204$, any $N^2/D^\kappa$ selected entries admit a polynomial saving for every $\kappa>0$. The individual statements also record Theorems 5, 25 and 30 and Corollaries 26 and 32. The callable versions also preserve memory and resource guarantees needed when these algorithms are used as subroutines.
-/

namespace Lax350013.SparseMatrixProduct

open Finset
open Lax350013.WordRAM
open Lax350013.RAMResources
open Lax350013.ThinMatrices
open Lax350013.MatrixParameters
open Lax350013.MatrixTradeoffs
open Lax350013.MatrixPreprocessing

/-- **Theorem 5**: "Let D ≥ 4 be a power of four and N ≥ D^18.  Given as input matrices X ∈
ℤ^{N×D} and Y ∈ ℤ^{D×N}, whose entries are integers of absolute value at most N^{O(1)}, as well as a
set W of at most N²/√D positions of an N × N matrix, the entries (XY)[I,J], (I,J) ∈ W, can be
computed deterministically in time O(N² log² D/D^{1/18})."  `c` is the exponent hidden in
`N^{O(1)}`.  (As a statement about the existence of programs, this follows from
`Corollary_26_wanted`, whose bound is smaller on these inputs: a statement of this kind cannot say
by which algorithm a bound is reached.) -/
def Theorem_5 : Prop :=
  ∀ c : ℕ, ∃ (P : List Instr) (b : ℕ) (C : ℝ),
    Solves (thinProduct []) P b
      (fun x => (∃ k : ℕ, x.D = 4 ^ k) ∧ 4 ≤ x.D ∧ x.D ^ 18 ≤ x.N ∧
        (x.W.length : ℝ) ≤ (x.N : ℝ) ^ 2 / Real.sqrt x.D ∧ x.U = x.N ^ c)
      (fun x => C * ((x.N : ℝ) ^ 2 * Real.log x.D ^ 2 / (x.D : ℝ) ^ (1 / 18 : ℝ)))

/-- **Theorem 25**: "For every ε < ε* and every κ > 0 there is a γ > 0 such that the
following holds. Given as input matrices [...], where 2 ≤ D ≤ N^ε, [...] as well as a set W of at
most N²/D^κ positions of an N × N matrix, the entries (XY)[I,J], (I,J) ∈ W, can be computed
deterministically in time O(N² log² D/D^γ)." -/
def Theorem_25 : Prop :=
  ∀ ε κ : ℝ, ε < epsStar → 0 < κ → ∃ γ : ℝ, 0 < γ ∧
    ∀ c₀ : ℕ, ∃ (P : List Instr) (b : ℕ) (C : ℝ),
      Solves (thinProduct []) P b
        (fun x => thinDom 2 ε c₀ x.toThinPair ∧ (x.W.length : ℝ) ≤ (x.N : ℝ) ^ 2 / (x.D : ℝ) ^ κ)
        (fun x => C * ((x.N : ℝ) ^ 2 * Real.log x.D ^ 2 / (x.D : ℝ) ^ γ))

/-- **Corollary 26**, last sentence: "Hence, for every set W of positions of an N × N
matrix, the entries (XY)[I,J], (I,J) ∈ W, can be computed deterministically in O(|W| D^{0.437} +
N²/D^{0.063}) time".  (With `D ≥ 1`, as in `Corollary_26`.) -/
def Corollary_26_wanted : Prop :=
  ∀ c : ℕ, ∃ (P : List Instr) (b : ℕ) (C : ℝ),
    Solves (thinProduct []) P b (fun x => 1 ≤ x.D ∧ x.D ^ 18 ≤ x.N ∧ x.U = x.N ^ c)
      (fun x => C * ((x.W.length : ℝ) * (x.D : ℝ) ^ (0.437 : ℝ) +
        (x.N : ℝ) ^ 2 / (x.D : ℝ) ^ (0.063 : ℝ)))

/-- **Theorem 30**, the offline form (9): "In particular, for every set W of positions of
an N × N matrix, the entries (XY)[I,J], (I,J) ∈ W, can be computed deterministically in time O(L |W|
∑_{d=0}^{t} α_d + L m ρ^t/(1 − ρ) N² + N·10^L/(√K N₀))." -/
def Theorem_30_wanted : Prop :=
  ∀ c : ℕ, ∃ (P : List Instr) (b : ℕ) (C : ℝ), ∀ m L t : ℕ,
    Solves (thinProduct [(m : ℤ), (L : ℤ), (t : ℤ)]) P b
      (fun x => theorem30Dom c m L t x.toThinPair)
      (fun x => C * cost9 L m t x.N x.W.length)

/-- **Corollary 32**: "Let c, θ, γ, q, X, Y, D, and ε be as in Corollary 31, and let κ > 0.
For every set W of at most N²/D^κ positions of an N × N matrix, the entries (XY)[I,J], (I,J) ∈ W,
can be computed deterministically in time O(N² log² D (D^{−γ} + D^{q−κ}))". -/
def Corollary_32 : Prop :=
  ∀ c θ ε κ : ℝ, 10 < c → 0 < θ → θ < 0.9 → ε < Rc c (gammaOf c θ) → 0 < κ →
    ∀ c₀ : ℕ, ∃ (P : List Instr) (b : ℕ) (C : ℝ),
      Solves (thinProduct []) P b
        (fun x => thinDom 2 ε c₀ x.toThinPair ∧ (x.W.length : ℝ) ≤ (x.N : ℝ) ^ 2 / (x.D : ℝ) ^ κ)
        (fun x => C * ((x.N : ℝ) ^ 2 * Real.log x.D ^ 2 *
          ((x.D : ℝ) ^ (-gammaOf c θ) + (x.D : ℝ) ^ (qOf θ - κ))))

/-- For every `ε < ε₀` and every `κ > 0` there is a `γ > 0` such that, whenever `D ≤ N^ε`, the
entries at any set of at most `N²/D^κ` positions can be computed in `O(N²/D^γ)` time.  The paper has
this sentence with `ε₀ = 0.1204` (Theorem 1).

NOTE.  The paper states no lower bound on `D` and `N` here; `D ≥ 1` and `N ≥ 1` are assumed.  On the
case `D = 1`, which Theorem 25 and Corollary 32 exclude, see the NOTE at `DataStructureBelow`. -/
def WantedBelow (ε₀ : ℝ) : Prop :=
  ∀ ε κ : ℝ, ε < ε₀ → 0 < κ → ∃ γ : ℝ, 0 < γ ∧
    ∀ c₀ : ℕ, ∃ (P : List Instr) (b : ℕ) (C : ℝ),
      Solves (thinProduct []) P b
        (fun x => thinDom 1 ε c₀ x.toThinPair ∧ (x.W.length : ℝ) ≤ (x.N : ℝ) ^ 2 / (x.D : ℝ) ^ κ)
        (fun x => C * ((x.N : ℝ) ^ 2 / (x.D : ℝ) ^ γ))

/-- **Theorem 1**: "Let N ≥ D^18, let X ∈ ℤ^{N×D} and Y ∈ ℤ^{D×N} have entries of absolute
value N^{O(1)}, and let W be any set of |W| ≤ N²/√D positions.  The entries (XY)[I,J], (I,J) ∈ W,
can be computed deterministically in O(N²/D^{0.063}) operations on O(log N)-bit integers.  More
generally, for every ε < 0.1204 and every κ > 0 there is a γ > 0 such that, whenever D ≤ N^ε
and |W| ≤ N²/D^κ, the task takes O(N²/D^γ) operations."

NOTE.  The paper states no lower bound on `D`; `D ≥ 1` is assumed, and in the last sentence also
`N ≥ 1` (see `WantedBelow`). -/
def Theorem_1 : Prop :=
  (∀ c₀ : ℕ, ∃ (P : List Instr) (b : ℕ) (C : ℝ),
    Solves (thinProduct []) P b
      (fun x => 1 ≤ x.D ∧ x.D ^ 18 ≤ x.N ∧ (x.W.length : ℝ) ≤ (x.N : ℝ) ^ 2 / Real.sqrt x.D ∧
        x.U = x.N ^ c₀)
      (fun x => C * ((x.N : ℝ) ^ 2 / (x.D : ℝ) ^ (0.063 : ℝ)))) ∧
  WantedBelow 0.1204

/-- Faster computation of selected matrix-product entries: Theorem 5. -/
axiom theorem5 : Theorem_5


/-- Faster computation of selected matrix-product entries: Theorem 25. -/
axiom theorem25 : Theorem_25


/-- Faster computation of selected matrix-product entries: Corollary 26 wanted. -/
axiom corollary26_wanted : Corollary_26_wanted


/-- Faster computation of selected matrix-product entries: Theorem 30 wanted. -/
axiom theorem30_wanted : Theorem_30_wanted


/-- Faster computation of selected matrix-product entries: Corollary 32. -/
axiom corollary32 : Corollary_32


/-- Faster computation of selected matrix-product entries: Theorem 1. -/
axiom theorem1 : Theorem_1


/-- Callable contract proved by upstream `Light.Sec2.claim_theorem_5`. -/
axiom callableTheorem5 : Lax350013.CallableAlgorithms.Claim.Theorem_5 Lax350013.CallableAlgorithms.lightModel

end Lax350013.SparseMatrixProduct
