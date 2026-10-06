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
import Lax350013.PolynomialTime

/-!
---
title: Time bounds, persistent queries and phased inputs
type: definition
---
The word-RAM resource conventions for problems with several size parameters, real exponents, logarithmic factors, persistent data structures and inputs revealed in phases. Programs are fixed before the instance. Queries retain the memory left by earlier queries; a phase cannot inspect the input of a later phase.
-/

namespace Lax350013.RAMResources

open Finset
open Lax350013.WordRAM

/-- The word size `W` is admissible against the slope `b` for an input with the parameters `params`
(its sizes): `W` is at least `b · (⌊log₂ p₁⌋ + ⌊log₂ p₂⌋ + … + 1)`.  If every parameter is at most a
fixed power of the size `n`, the smallest admissible word size is a constant times `log n`: "O(log
n)-bit words".  A statement fixes only the slope `b`, together with the program, and the program has
to work, within the same bound on the number of steps, at every admissible word size. -/
def Admissible (b : Nat) (params : List Nat) (W : Nat) : Prop :=
  b * ((params.map Nat.log2).sum + 1) ≤ W

/-- The output of a function problem: the cells right after the input, read as signed words.
`output c len i` is the number in the `i`-th cell of the memory `c` after an input of `len`
cells. -/
def output {W : Nat} (c : Int → BitVec W) (len : Nat) (i : Nat) : Int :=
  (c ((len : Int) + (i : Int))).toInt

/-- A computational problem on the word RAM. -/
structure Problem where
  /-- The instances. -/
  Inst : Type
  /-- The parameters of an instance on which the word size depends: its sizes. -/
  params : Inst → List ℕ
  /-- The input: the numbers written into the cells 0, 1, 2, … -/
  input : Inst → List ℤ
  /-- `IsAnswer x verdict out`: the verdict, and the numbers `out 0, out 1, …` in the cells right
  after the input, are a correct answer to the instance `x`. -/
  IsAnswer : Inst → Bool → (ℕ → ℤ) → Prop

/-- **Solving a problem within a time bound.**  The program `P` with slope `b` solves the problem on
the instances in `dom` within time `T`: on every such instance `x` and at every admissible word size
`bits`, the run from the first instruction on the starting memory (input in the cells 0, 1, 2, …,
zeros elsewhere) gives a verdict after at most `T x` steps, and the verdict and the output are a
correct answer. -/
def Solves (prob : Problem) (P : List Instr) (b : ℕ) (dom : prob.Inst → Prop) (T : prob.Inst → ℝ) :
    Prop :=
  ∀ x : prob.Inst, dom x → ∀ bits : ℕ, Admissible b (prob.params x) bits →
    ∃ (t : ℕ) (verdict : Bool) (c : ℤ → BitVec bits), (t : ℝ) ≤ T x ∧
      exec P t 0 (loadWords bits (prob.input x)) = some (verdict, c) ∧
      prob.IsAnswer x verdict (output c (prob.input x).length)

/-- The program `P` with slope `b` solves the problem `Q` within `T(n)` steps when all numbers are
integers of absolute value at most `n^κ`.  This is what `Lax350013.PolynomialTime.Problem.SolvedInTime` asks of
the runs of `P`, for a real bound `T`: on every such instance, of any size `n`, and at every word
size of at least `b (⌊log₂ n⌋ + 1)` bits, `P` halts within `T(n)` steps with the right verdict and
output (`Lax350013.PolynomialTime.Problem.SolvedBy`).

NOTE.  As in `Lax350013.PolynomialTime.Problem.SolvedInTime`, the bound speaks of every number of the input
list.  Where the input contains an adjacency matrix, its entries 1 count too; `n^κ` is at least 1 as
soon as there is a vertex. -/
def SolvesWithin (Q : Lax350013.PolynomialTime.Problem) (κ : ℕ) (P : List Instr) (b : ℕ) (T : ℕ → ℝ) : Prop :=
  ∀ (n : ℕ) (x : Q.Instance n), (∀ a ∈ Q.input x, a.natAbs ≤ n ^ κ) → ∀ W ≥ b * (Nat.log2 n + 1),
    ∃ t : ℕ, (t : ℝ) ≤ T n ∧ Q.SolvedBy x P W t

/-- The problem `Q`, a value of `Lax350013.PolynomialTime.Problem`, is solved by a deterministic algorithm in
`O(n^a (log n)^e)` time when all numbers are integers of absolute value at most `n^κ`: there are a
program, a slope and a constant `C` such that the program solves `Q` within `C (n^a (log n)^e + 1)`
steps.  (For `a ≥ 0` the `+ 1` matters only at `n ≤ 1`, where `n^a (log n)^e` may be 0.) -/
def SolvedInTimeAt (Q : Lax350013.PolynomialTime.Problem) (κ : ℕ) (a : ℝ) (e : ℕ) : Prop :=
  ∃ (P : List Instr) (b : ℕ) (C : ℝ),
    SolvesWithin Q κ P b fun n => C * ((n : ℝ) ^ a * Real.log n ^ e + 1)

/-- The same for every constant `κ`: "all numbers in the input are integers of absolute value
n^{O(1)}" (Theorem 2).  The program, the slope and the constant may depend on `κ`.

NOTE.  `κ` is the paper's ν.  Where the paper has ν ≥ 1 (Theorem 19, Corollary 39), `κ = 0` is
included here. -/
def SolvedInTime (Q : Lax350013.PolynomialTime.Problem) (a : ℝ) (e : ℕ) : Prop :=
  ∀ κ : ℕ, SolvedInTimeAt Q κ a e

/-- The same in `O(n^a (log n)^{O(1)})` time, which Theorem 22 writes Õ(n^a).

NOTE.  The exponent of the logarithm may depend on `κ` too: this is the weaker reading of the
Õ of Theorem 22. -/
def SolvedInPolylogTime (Q : Lax350013.PolynomialTime.Problem) (a : ℝ) : Prop :=
  ∀ κ : ℕ, ∃ e : ℕ, SolvedInTimeAt Q κ a e

/-- The problem `Q` is solved by a deterministic algorithm in `n^{a+o(1)}` time when all numbers are
integers of absolute value at most `n^κ`, for every constant `κ`: as `SolvedInTime`, with the bound
`C (n^{a+o(n)} + 1)` for a function `o` that tends to 0.  The program, the slope, the constant and
the function may depend on `κ`.  (The constant is needed at `n ≤ 1`, where `n^{a+o(n)}` is 0 or 1;
the `+ 1` keeps the form of `SolvedInTimeAt`.  For `a < 0` the bound means `O(1)`.) -/
def SolvedInLittleOTime (Q : Lax350013.PolynomialTime.Problem) (a : ℝ) : Prop :=
  ∀ κ : ℕ, ∃ (P : List Instr) (b : ℕ) (C : ℝ) (o : ℕ → ℝ), Filter.Tendsto o Filter.atTop (nhds 0) ∧
    SolvesWithin Q κ P b fun n => C * ((n : ℝ) ^ (a + o n) + 1)

/-- The memory on which a query starts: the memory `c`, left behind by the preprocessing or by the
previous query, with the row `I` and the column `J` written into the two query cells `qI` and
`qJ`. -/
def withQuery {bits : ℕ} (c : ℤ → BitVec bits) (qI qJ : ℤ) (I J : ℕ) : ℤ → BitVec bits :=
  fun a => if a = qI then BitVec.ofInt bits I else if a = qJ then BitVec.ofInt bits J else c a

/-- The query program `Q` serves the queries of the list one after the other, starting from the
memory `c`: each run starts at the first instruction, accepts within `tq` steps and leaves the right
entry in the cell `qOut`; the next query starts from the memory that this run leaves. -/
def Serves {bits : ℕ} (Q : List Instr) (qI qJ qOut : ℤ) (tq : ℕ) (entry : ℕ → ℕ → ℤ) :
    (ℤ → BitVec bits) → List (ℕ × ℕ) → Prop
  | _, [] => True
  | c, q :: rest =>
    ∃ c' : ℤ → BitVec bits, exec Q tq 0 (withQuery c qI qJ q.1 q.2) = some (true, c') ∧
      (c' qOut).toInt = entry q.1 q.2 ∧ Serves Q qI qJ qOut tq entry c' rest

/-- The memory on which a phase starts: the memory `c` with the list `ws` written into the cells
`off, off + 1, …`. -/
def withInput {bits : ℕ} (c : ℤ → BitVec bits) (off : ℕ) (ws : List ℤ) : ℤ → BitVec bits :=
  fun a =>
    if (off : ℤ) ≤ a ∧ a < (off : ℤ) + (ws.length : ℤ) then
      BitVec.ofInt bits (ws.getD (a - (off : ℤ)).toNat 0)
    else c a

/-- The phases of the list, each given by its program, its input and a number of steps, run one
after the other from the memory `c`: every phase starts at its first instruction and accepts within
its number of steps, the inputs are written one after the other from the cell `off` on, and the last
memory, with the address of the first cell after the last input, satisfies `good`.
-/
def RunsPhases {bits : ℕ} (good : (ℤ → BitVec bits) → ℕ → Prop) :
    (ℤ → BitVec bits) → ℕ → List (List Instr × List ℤ × ℕ) → Prop
  | c, off, [] => good c off
  | c, off, (P, ws, s) :: rest =>
    ∃ c' : ℤ → BitVec bits, exec P s 0 (withInput c off ws) = some (true, c') ∧
      RunsPhases good c' (off + ws.length) rest

/-- A number `s` of steps is `O(n^a)` with the constant `C`: `s ≤ C (n^a + 1)`.  For `n ≥ 1` and
`a ≥ 0` the `+ 1` only changes the constant; for `a < 0` the bound means `O(1)`. -/
def Within (s : ℕ) (C : ℝ) (n : ℕ) (a : ℝ) : Prop := (s : ℝ) ≤ C * ((n : ℝ) ^ a + 1)

end Lax350013.RAMResources
