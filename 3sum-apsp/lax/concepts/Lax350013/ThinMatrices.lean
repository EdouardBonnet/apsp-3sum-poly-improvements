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
import Lax350013.RAMResources

/-!
---
title: Thin matrix products and persistent entry queries
type: definition
---
Two integer matrices have dimensions $N\times D$ and $D\times N$, and entries bounded in absolute value by $U$. Wanted output positions are a list without repetitions. The data-structure specification bounds preprocessing time and the extent of retained memory, then requires correctness for every finite sequence of entry queries.
-/

namespace Lax350013.ThinMatrices

open Finset
open Lax350013.WordRAM
open Lax350013.RAMResources

/-- A matrix written row by row. -/
def rowMajor {n m : ℕ} (A : Fin n → Fin m → ℤ) : List ℤ :=
  (List.finRange n).flatMap fun i => (List.finRange m).map fun j => A i j

/-- A Boolean as a number. -/
def bit (p : Bool) : ℤ := if p then 1 else 0

/-- Two matrices `X ∈ ℤ^{N×D}` and `Y ∈ ℤ^{D×N}` with entries of absolute value at most `U`. -/
structure ThinPair where
  /-- The long side. -/
  N : ℕ
  /-- The short side. -/
  D : ℕ
  /-- The bound on the absolute values of the entries. -/
  U : ℕ
  /-- The first matrix. -/
  X : Matrix (Fin N) (Fin D) ℤ
  /-- The second matrix. -/
  Y : Matrix (Fin D) (Fin N) ℤ
  /-- The entries of `X` are bounded. -/
  boundX : ∀ i j, |X i j| ≤ (U : ℤ)
  /-- The entries of `Y` are bounded. -/
  boundY : ∀ i j, |Y i j| ≤ (U : ℤ)

/-- Theorem 5: two such matrices and "a set W of [...] positions of an N × N matrix".

NOTE.  The paper does not say how a set is given.  Here it is a list without repetitions, in any
order. -/
structure ThinInstance extends ThinPair where
  /-- The wanted positions. -/
  W : List (Fin N × Fin N)
  /-- No position is listed twice. -/
  nodup : W.Nodup

/-- The input of the matrix problems: `N`, `D`, `|W|`, then further parameters `extra` (none, except
in Theorem 30), then `X`, then `Y`, then the rows `I` of the wanted positions, then their columns
`J`. -/
def ThinInstance.input (x : ThinInstance) (extra : List ℤ) : List ℤ :=
  [(x.N : ℤ), (x.D : ℤ), (x.W.length : ℤ)] ++ extra ++ rowMajor x.X ++ rowMajor x.Y ++
    x.W.map (fun q => (q.1.val : ℤ)) ++ x.W.map (fun q => (q.2.val : ℤ))

/-- **The wanted entries of a thin matrix product** (Theorem 5): accept, and leave `(XY)[I,J]` for
the `i`-th wanted position `(I,J)` in the `i`-th output cell. -/
def thinProduct (extra : List ℤ) : Problem where
  Inst := ThinInstance
  params x := [x.N, x.D]
  input x := x.input extra
  IsAnswer x verdict out :=
    verdict = true ∧ ∀ (i : ℕ) (h : i < x.W.length), out i = (x.X * x.Y) x.W[i].1 x.W[i].2

/-- The input of the preprocessing: `N`, `D`, further parameters `extra` (none, except in
Theorem 30), then `X`, then `Y`.  The list `extra` is fixed before the instance. -/
def ThinPair.input (x : ThinPair) (extra : List ℤ) : List ℤ :=
  [(x.N : ℤ), (x.D : ℤ)] ++ extra ++ rowMajor x.X ++ rowMajor x.Y

/-- **A data structure for the entries of a thin matrix product** (Theorem 30, Corollary 26): "After
preprocessing X and Y [...], the data structure answers a query for any single entry of XY, not
known in advance" (Section 4).

`P` is the preprocessing program, `Q` the query program, `qI`, `qJ`, `qOut` the three cells through
which queries are put and answered; all of them, and the slope `b`, are fixed before the instance.
On every instance in `dom` and at every admissible word size:

* time: the preprocessing accepts within `Tp x` steps;
* space: it leaves unchanged every cell `a` with `a < -Sp x` or `a > len + Sp x`, where the input
  occupies the cells 0 to `len - 1` (so the cells of the input are not counted);
* queries: then every sequence of queries `(I, J)` with `I, J < N` is served, each query within
  `Tq x` steps.  A query starts on the memory left behind; nothing is reset for it.

NOTE.  The paper says "time and space" and does not define space.  Here space is the extent of the
memory in which the preprocessing leaves the data structure, not the number of cells written, which
is at most the time anyway; a structure that is scattered over a large range of addresses does not
count as small.  Cells that the preprocessing restores, and cells that the queries write, are not
constrained. -/
def IsDataStructure (P Q : List Instr) (qI qJ qOut : ℤ) (b : ℕ) (extra : List ℤ)
    (dom : ThinPair → Prop) (Tp Sp Tq : ThinPair → ℝ) : Prop :=
  ∀ x : ThinPair, dom x → ∀ bits : ℕ, Admissible b [x.N, x.D] bits →
    ∃ (tp tq : ℕ) (c : ℤ → BitVec bits), (tp : ℝ) ≤ Tp x ∧ (tq : ℝ) ≤ Tq x ∧
      exec P tp 0 (loadWords bits (x.input extra)) = some (true, c) ∧
      (∀ a : ℤ, ((a : ℝ) < -Sp x ∨ ((x.input extra).length : ℝ) + Sp x < (a : ℝ)) →
        c a = loadWords bits (x.input extra) a) ∧
      ∀ queries : List (ℕ × ℕ), (∀ q ∈ queries, q.1 < x.N ∧ q.2 < x.N) →
        Serves Q qI qJ qOut tq
          (fun I J => if h : I < x.N ∧ J < x.N then (x.X * x.Y) ⟨I, h.1⟩ ⟨J, h.2⟩ else 0) c queries

end Lax350013.ThinMatrices
