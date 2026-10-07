/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Modified for the independent Lax packaging by Édouard Bonnet, 2026.
Derived from 3sum-apsp/ThreeSumApsp/Lang and Util/List.lean at upstream commit e1a4e6508154ea59f030480661590a9fe3018011.
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
import Lax350013.StructuredPrograms

/-!
---
title: Reusable procedures and memory preservation
type: definition
---
A solver remains correct when other procedures are appended to its program. Its contract specifies inputs, outputs, preserved memory, time, and polynomial bounds on words, scratch space and call depth. These guarantees make the algorithmic reductions compositional.
-/

namespace Lax350013.ProcedureContracts

open Finset
open Lax350013.StructuredPrograms

/-- The statement s, started in σ, ends within T steps in a state that satisfies Q. -/
def Ends (lim : Limits) (P : Program) (d : ℕ) (s : Stmt) (σ : State) (T : ℕ) (Q : State → Prop) :
    Prop :=
  ∃ σ' c, Exec lim P d s σ σ' c ∧ c ≤ T ∧ Q σ'

/-- The bound 2^s · ((p₁ + 1) (p₂ + 1) ⋯)^k in the parameters of an instance. -/
def polyBound (s k : ℕ) (params : List ℕ) : ℕ := 2 ^ s * ((params.map (· + 1)).prod) ^ k

/-- The cell `b` is among the `n` cells from address `a`. -/
abbrev Inside (a n b : ℕ) : Prop := a ≤ b ∧ b < a + n

/-- The cell `b` is not among the `n` cells from address `a`. -/
abbrev Outside (a n b : ℕ) : Prop := b < a ∨ a + n ≤ b

/-- Two regions of the memory, of `n` cells from `a` and of `n'` cells from `a'`, do not meet. -/
abbrev Apart (a n a' n' : ℕ) : Prop := a + n ≤ a' ∨ a' + n' ≤ a

/-- The memory `μ'` agrees with `μ` on every cell that satisfies `K`. -/
def SameOn (K : ℕ → Prop) (μ μ' : ℕ → ℤ) : Prop := ∀ b, K b → μ' b = μ b

/-- No cell below the free pointer has changed. -/
abbrev Kept (μ μ' : ℕ → ℤ) (fr : ℕ) : Prop := SameOn (· < fr) μ μ'

/-- No cell below the free pointer has changed, except the `len` cells from `out`. -/
abbrev KeptBut (μ μ' : ℕ → ℤ) (fr out len : ℕ) : Prop :=
  SameOn (fun x => x < fr ∧ Outside out len x) μ μ'

/-- The cells a, a + 1, … of the memory μ hold the list l. -/
def Seg (μ : ℕ → ℤ) (a : ℕ) (l : List ℤ) : Prop := ∀ i (h : i < l.length), μ (a + i) = l[i]

/-- The cells a, a + 1, … hold a list of natural numbers. -/
abbrev SegN (μ : ℕ → ℤ) (a : ℕ) (l : List ℕ) : Prop := Seg μ a (l.map fun x : ℕ => (x : ℤ))

/-- All members of the list `l` have absolute value at most `U`. -/
def AbsLe (l : List ℤ) (U : ℤ) : Prop := ∀ x ∈ l, |x| ≤ U

/-- What a run needs: the largest absolute value it forms, the number of cells it uses from the free
pointer on, and the number of levels of calls below the procedure. -/
structure Need : Type where
  word : ℕ
  cells : ℕ
  depth : ℕ

/-- The limits allow for the need of a procedure that is called at depth `d` with the free pointer
`fr`.  An address always fits in a word. -/
structure Need.Ok (r : Need) (lim : Limits) (fr d : ℕ) : Prop where
  word : (r.word : ℤ) ≤ lim.word
  cells : fr + r.cells ≤ lim.space
  space : (lim.space : ℤ) ≤ lim.word
  depth : d + r.depth ≤ lim.depth

/-- A need that depends on a size and a bound is polynomially bounded in the two: by
`2^s ((n + 1) (U + 1))^k`. -/
def PolyNeed (need : ℕ → ℕ → Need) : Prop :=
  ∃ s k : ℕ, ∀ n U : ℕ, (need n U).word ≤ polyBound s k [n, U] ∧ (need n U).cells ≤
    polyBound s k [n, U] ∧
    (need n U).depth ≤ polyBound s k [n, U]

/-- A problem with a calling convention. -/
structure Task : Type 1 where
  /-- The instances, as they lie in the memory: sizes, bound, addresses, contents. -/
  Inst : Type
  /-- The size of an instance. -/
  size : Inst → ℕ
  /-- The bound on the absolute values of its numbers that is handed to the solver. -/
  bound : Inst → ℕ
  /-- The arguments of the call, without the free pointer, which comes last. -/
  args : Inst → List ℤ
  /-- The instance is valid, and it lies in the memory below the free pointer. -/
  Pre : Inst → (ℕ → ℤ) → ℕ → Prop
  /-- The result and the final memory are right.  (That the cells below the free pointer are
  otherwise unchanged is part of this.) -/
  Post : Inst → (ℕ → ℤ) → ℕ → ℤ → (ℕ → ℤ) → Prop

/-- **Procedure `p` of the program `P` solves the task** within `T (size) (bound)` steps, whenever
the limits allow for `need (size) (bound)`; and so it does in every program that begins with `P`. -/
def Solves (task : Task) (P : Program) (p : ℕ) (T : ℕ → ℕ → ℕ) (need : ℕ → ℕ → Need) : Prop :=
  ∃ body, P[p]? = some body ∧
    ∀ (R : Program) (lim : Limits) (d : ℕ) (x : task.Inst) (μ : ℕ → ℤ) (fr : ℕ), task.Pre x μ fr →
      (need (task.size x) (task.bound x)).Ok lim fr d →
      Ends lim (P ++ R) d body ⟨frame (task.args x ++ [(fr : ℤ)]), μ⟩
        (T (task.size x) (task.bound x))
        fun σ' => task.Post x μ fr (σ'.loc 0) σ'.mem

/-- "The task is solved in time `T`", for a real-valued `T` whose second argument is an upper bound
on the numbers: some solver with a polynomially bounded need takes at most `T n u` steps on every
instance of size `n ≥ 1` with a bound `1 ≤ U ≤ u`. -/
def SolvedIn (task : Task) (T : ℕ → ℝ → ℝ) : Prop :=
  ∃ (P : Program) (p : ℕ) (Tn : ℕ → ℕ → ℕ) (need : ℕ → ℕ → Need), PolyNeed need ∧
    Solves task P p Tn need ∧
    ∀ (n U : ℕ) (u : ℝ), 1 ≤ n → 1 ≤ U → (U : ℝ) ≤ u → (Tn n U : ℝ) ≤ T n u

/-- A problem with a calling convention and a list of parameters. -/
structure TaskN : Type 1 where
  /-- The instances, as they lie in the memory. -/
  Inst : Type
  /-- The parameters on which time and need depend. -/
  pars : Inst → List ℕ
  /-- The arguments of the call, without the free pointer, which comes last. -/
  args : Inst → List ℤ
  /-- The instance is valid, and it lies in the memory below the free pointer. -/
  Pre : Inst → (ℕ → ℤ) → ℕ → Prop
  /-- The result and the final memory are right. -/
  Post : Inst → (ℕ → ℤ) → ℕ → ℤ → (ℕ → ℤ) → Prop

/-- Procedure `p` of the program `P` solves the task within `T pars` steps, whenever the limits
allow for `need pars`; and so it does in every program that begins with `P`. -/
def SolvesN (task : TaskN) (P : Program) (p : ℕ) (T : List ℕ → ℕ) (need : List ℕ → Need) : Prop :=
  ∃ body, P[p]? = some body ∧
    ∀ (R : Program) (lim : Limits) (d : ℕ) (x : task.Inst) (μ : ℕ → ℤ) (fr : ℕ), task.Pre x μ fr →
      (need (task.pars x)).Ok lim fr d →
      Ends lim (P ++ R) d body ⟨frame (task.args x ++ [(fr : ℤ)]), μ⟩ (T (task.pars x))
        fun σ' => task.Post x μ fr (σ'.loc 0) σ'.mem

/-- A need that is polynomially bounded in the parameters. -/
def PolyNeedN (need : List ℕ → Need) : Prop :=
  ∃ s k : ℕ, ∀ ps : List ℕ, (need ps).word ≤ polyBound s k ps ∧ (need ps).cells ≤ polyBound s k ps ∧
    (need ps).depth ≤ polyBound s k ps

end Lax350013.ProcedureContracts
