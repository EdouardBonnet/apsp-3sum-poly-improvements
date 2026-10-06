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

/-!
---
title: Hinted Boolean matrix-vector problems
type: definition
---
The v-hinted Mv, Mv-hinted Mv and uMv-hinted uMv problems reveal their inputs in successive phases. This specification includes the Boolean products, phase layouts and the conjectured trade-offs. Rectangular matrix-multiplication exponents are numerical parameters here; their values and lower bounds are not asserted.
-/

namespace Lax350013.HintedMatrixVector

open Finset
open Lax350013.WordRAM
open Lax350013.RAMResources
open Lax350013.ThinMatrices

namespace HintedMv

/-- Section 5.4: "All three are over the Boolean semiring".  The product of two Boolean matrices. -/
def boolMul {l m r : ℕ} (M : Matrix (Fin l) (Fin m) Bool) (V : Matrix (Fin m) (Fin r) Bool) :
    Matrix (Fin l) (Fin r) Bool :=
  fun i j => decide (∃ k, M i k = true ∧ V k j = true)

/-- Proof of Corollary 40: "We compute over ℤ with 0/1 matrices".  The 0/1 integer matrix
of a Boolean matrix. -/
def toInt {l m : ℕ} (M : Matrix (Fin l) (Fin m) Bool) : Matrix (Fin l) (Fin m) ℤ :=
  fun i j => if M i j = true then 1 else 0

/-- Section 5.4, v-hinted Mv (Definition 5.1 of [vdBNS19]): "Phase 1: an n × t matrix M.  Phase 2: a
t × n matrix V. Phase 3: an index i, after which the algorithm outputs MV_{[n],i}, the product of M
and column i of V." -/
def vHintedOutput {n t : ℕ} (M : Matrix (Fin n) (Fin t) Bool) (V : Matrix (Fin t) (Fin n) Bool)
    (i : Fin n) : Fin n → Bool :=
  fun r => boolMul M V r i

/-- Section 5.4, Mv-hinted Mv (Definition 5.6 of [vdBNS19]): "Phase 1: N ∈ {0,1}^{n×n} and V ∈
{0,1}^{t×n}.  Phase 2: a vector I ∈ [n]^t of column indices.  Phase 3: an index j, after which the
algorithm outputs N_{[n],I} V_{[t],j}, where N_{[n],I} is the n × t matrix whose k-th column is
column I_k of N." -/
def MvHintedOutput {n t : ℕ} (N : Matrix (Fin n) (Fin n) Bool) (V : Matrix (Fin t) (Fin n) Bool)
    (I : Fin t → Fin n) (j : Fin n) : Fin n → Bool :=
  fun r => boolMul (N.submatrix id I) V r j

/-- Section 5.4, uMv-hinted uMv (Definition 5.11 of [vdBNS19]): "Phase 1: U ∈ {0,1}^{n×t₁}, N ∈
{0,1}^{n×n}, and V ∈ {0,1}^{t₂×n}.  Phase 2: I ∈ [n]^{t₁}.  Phase 3: J ∈ [n]^{t₂}.  Phase 4: indices
i and j, after which the algorithm outputs (U N_{I,J} V)_{i,j}, where N_{I,J} is the t₁ × t₂
submatrix of N with the rows I and the columns J." -/
def uMvHintedOutput {n t₁ t₂ : ℕ} (U : Matrix (Fin n) (Fin t₁) Bool)
    (N : Matrix (Fin n) (Fin n) Bool) (V : Matrix (Fin t₂) (Fin n) Bool) (I : Fin t₁ → Fin n)
    (J : Fin t₂ → Fin n) (i j : Fin n) : Bool :=
  boolMul (boolMul U (N.submatrix I J)) V i j

/-- Section 5.4: "Each conjecture asserts that no algorithm simultaneously beats all of its listed
bounds, for any ε > 0." v-hinted Mv (Conjecture 5.2 of [vdBNS19]): "Bounds conjectured to be
impossible to achieve simultaneously: n^{ω(1,1,τ)-ε} for Phase 2 and n^{1+τ-ε} for Phase 3."

Running times are not defined here, so the conjecture is stated relative to a parameter:
`Achieves a₂ a₃` stands for "some algorithm solves the problem with t = n^τ, with polynomial time in
Phase 1, O(n^{a₂}) time in Phase 2 and O(n^{a₃}) time in Phase 3".  `ω` stands for the number
ω(1,1,τ).  For programs of the word RAM the parameter is `AchievesVHinted τ`.  The exponents of
rectangular matrix multiplication are not defined in Lean: `ω` is an arbitrary real number here, and
the definition says something only together with a condition on it. The statement that the
conjecture fails (`Items.Corollary_40_fail`) is made for every `ω ≥ 2`.

[vdBNS19] words the bounds as lower bounds Ω(n^{x-ε}) on the time of a phase.  That wording implies
the one used here, "not O(n^{x-ε})" (apply it with ε/2), so a refutation of the conjecture in this
form refutes it as worded there.  The same holds for `Conjecture57` and `Conjecture512`. -/
def Conjecture52 (Achieves : ℝ → ℝ → Prop) (ω τ : ℝ) : Prop :=
  ∀ ε > 0, ¬ Achieves (ω - ε) (1 + τ - ε)

/-- Section 5.4, Mv-hinted Mv (Conjecture 5.7 of [vdBNS19]): "n^{ω(1,τ,1)-ε} for Phase 2 and
n^{1+τ-ε} for Phase 3." `Achieves` is as in `Conjecture52`, for the Mv-hinted Mv problem
(`AchievesMvHinted τ`); `ω` stands for ω(1,τ,1). -/
def Conjecture57 (Achieves : ℝ → ℝ → Prop) (ω τ : ℝ) : Prop :=
  ∀ ε > 0, ¬ Achieves (ω - ε) (1 + τ - ε)

/-- Section 5.4, uMv-hinted uMv (Conjecture 5.12 of [vdBNS19]): "n^{ω(1,τ₁,1)-ε} for Phase 2,
n^{ω(τ₂,τ₁,1)-ε} for Phase 3, and n^{τ₁+τ₂-ε} for Phase 4."  `Achieves a₂ a₃ a₄` stands for "some
algorithm solves the problem with t₁ = n^{τ₁} and t₂ = n^{τ₂}, with polynomial time in Phase 1 and
O(n^{a₂}), O(n^{a₃}), O(n^{a₄}) time in Phases 2, 3, 4"; `ω₂` stands for ω(1,τ₁,1) and `ω₃` for
ω(τ₂,τ₁,1).  For programs of the word RAM the parameter is `AchievesUMvHinted τ₁ τ₂`. -/
def Conjecture512 (Achieves : ℝ → ℝ → ℝ → Prop) (ω₂ ω₃ τ₁ τ₂ : ℝ) : Prop :=
  ∀ ε > 0, ¬ Achieves (ω₂ - ε) (ω₃ - ε) (τ₁ + τ₂ - ε)

end HintedMv

open HintedMv

/-- Section 5.4: the hint dimension "t = n^τ".

NOTE.  The paper treats `n^τ` as an integer; here it is rounded down, which keeps what the proof of
Corollary 40 needs, for `n ≥ 1`: `t ≥ 1` if `τ ≥ 0`, and `t^18 ≤ n` if `0 ≤ τ ≤ 1/18`.  The number
`t` is given to the programs in Phase 1, after `n`; they need not compute it. -/
noncomputable def hintSize (τ : ℝ) (n : ℕ) : ℕ := ⌊(n : ℝ) ^ τ⌋₊

/-- **v-hinted Mv** (Section 5.4; Definition 5.1 of [vdBNS19]) with `t = n^τ` is solved with
polynomial time in Phase 1, `O(n^{a₂})` time in Phase 2 and `O(n^{a₃})` time in Phase 3.  Phase 1
receives `n`, `t` and the `n × t` matrix `M`; Phase 2 the `t × n` matrix `V`; Phase 3 the index `i`;
the output is the `n` entries of the Boolean product of `M` and column `i` of `V`. -/
def AchievesVHinted (τ a₂ a₃ : ℝ) : Prop :=
  ∃ (P₁ P₂ P₃ : List Instr) (b : ℕ) (C a₁ : ℝ), ∀ n : ℕ, 1 ≤ n →
    ∀ (M : Matrix (Fin n) (Fin (hintSize τ n)) Bool) (V : Matrix (Fin (hintSize τ n)) (Fin n) Bool)
      (i : Fin n) (bits : ℕ), Admissible b [n] bits →
      ∃ s₁ s₂ s₃ : ℕ, Within s₁ C n a₁ ∧ Within s₂ C n a₂ ∧ Within s₃ C n a₃ ∧
        RunsPhases (fun c off => ∀ r : Fin n, output c off r.val = bit (vHintedOutput M V i r))
          (loadWords bits []) 0
          [(P₁, [(n : ℤ), (hintSize τ n : ℤ)] ++ rowMajor (toInt M), s₁),
            (P₂, rowMajor (toInt V), s₂), (P₃, [(i.val : ℤ)], s₃)]

/-- **Mv-hinted Mv** (Section 5.4; Definition 5.6 of [vdBNS19]) with `t = n^τ`, in the same sense.
Phase 1 receives `n`, `t`, the `n × n` matrix `N` and the `t × n` matrix `V`; Phase 2 the `t` column
indices `I`; Phase 3 the index `j`; the output is the `n` entries of `N_{[n],I} V_{[t],j}`. -/
def AchievesMvHinted (τ a₂ a₃ : ℝ) : Prop :=
  ∃ (P₁ P₂ P₃ : List Instr) (b : ℕ) (C a₁ : ℝ), ∀ n : ℕ, 1 ≤ n →
    ∀ (N : Matrix (Fin n) (Fin n) Bool) (V : Matrix (Fin (hintSize τ n)) (Fin n) Bool)
      (I : Fin (hintSize τ n) → Fin n) (j : Fin n) (bits : ℕ), Admissible b [n] bits →
      ∃ s₁ s₂ s₃ : ℕ, Within s₁ C n a₁ ∧ Within s₂ C n a₂ ∧ Within s₃ C n a₃ ∧
        RunsPhases (fun c off => ∀ r : Fin n, output c off r.val = bit (MvHintedOutput N V I j r))
          (loadWords bits []) 0
          [(P₁, [(n : ℤ), (hintSize τ n : ℤ)] ++ rowMajor (toInt N) ++ rowMajor (toInt V), s₁),
            (P₂, List.ofFn fun k => ((I k).val : ℤ), s₂), (P₃, [(j.val : ℤ)], s₃)]

/-- **uMv-hinted uMv** (Section 5.4; Definition 5.11 of [vdBNS19]) with `t₁ = n^{τ₁}` and `t₂ =
n^{τ₂}` is solved with polynomial time in Phase 1 and `O(n^{a₂})`, `O(n^{a₃})`, `O(n^{a₄})` time in
Phases 2, 3, 4.  Phase 1 receives `n`, `t₁`, `t₂` and the matrices `U` (`n × t₁`), `N` (`n × n`),
`V` (`t₂ × n`); Phase 2 the `t₁` row indices `I`; Phase 3 the `t₂` column indices `J`; Phase 4 the
indices `i` and `j`; the output is the one entry `(U N_{I,J} V)_{i,j}`. -/
def AchievesUMvHinted (τ₁ τ₂ a₂ a₃ a₄ : ℝ) : Prop :=
  ∃ (P₁ P₂ P₃ P₄ : List Instr) (b : ℕ) (C a₁ : ℝ), ∀ n : ℕ, 1 ≤ n →
    ∀ (U : Matrix (Fin n) (Fin (hintSize τ₁ n)) Bool) (N : Matrix (Fin n) (Fin n) Bool)
      (V : Matrix (Fin (hintSize τ₂ n)) (Fin n) Bool) (I : Fin (hintSize τ₁ n) → Fin n)
      (J : Fin (hintSize τ₂ n) → Fin n)
      (i j : Fin n) (bits : ℕ), Admissible b [n] bits →
      ∃ s₁ s₂ s₃ s₄ : ℕ, Within s₁ C n a₁ ∧ Within s₂ C n a₂ ∧ Within s₃ C n a₃ ∧ Within s₄ C n a₄ ∧
        RunsPhases (fun c off => output c off 0 = bit (uMvHintedOutput U N V I J i j))
          (loadWords bits []) 0
          [(P₁, [(n : ℤ), (hintSize τ₁ n : ℤ), (hintSize τ₂ n : ℤ)] ++ rowMajor (toInt U) ++
              rowMajor (toInt N) ++ rowMajor (toInt V), s₁),
            (P₂, List.ofFn fun k => ((I k).val : ℤ), s₂),
            (P₃, List.ofFn fun k => ((J k).val : ℤ), s₃),
            (P₄, [(i.val : ℤ), (j.val : ℤ)], s₄)]

end Lax350013.HintedMatrixVector
