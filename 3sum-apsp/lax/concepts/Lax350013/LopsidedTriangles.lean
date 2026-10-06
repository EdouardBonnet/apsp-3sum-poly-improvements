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
title: Lopsided all-edges triangle detection and counting
type: definition
---
An unweighted tripartite graph has two parts of size $N$, a middle part of size at most $D$, and a specified set of query edges between the large parts. The tasks are to detect or count the triangles containing each query edge. The input uses two Boolean biadjacency matrices; zero padding represents a smaller middle part.
-/

namespace Lax350013.LopsidedTriangles

open Finset
open Lax350013.WordRAM
open Lax350013.RAMResources
open Lax350013.ThinMatrices

/-- **Definition 13**, the input: "an unweighted undirected tripartite graph with two parts
A and B of n vertices each and a middle part M [...], with arbitrary edges in M × A and M × B.  Let
W ⊆ A × B be the set of edges between A and B."  The bound "of at most D vertices" on the middle
part is `LopInstance.MiddleAtMost`. -/
structure LopInstance (n : ℕ) where
  /-- The middle part `M`. -/
  M : Type
  /-- The middle part is finite. -/
  [fintypeM : Fintype M]
  /-- `adjA a v`: the vertex `a ∈ A` and the middle vertex `v ∈ M` are adjacent. -/
  adjA : Fin n → M → Prop
  /-- `adjB v b`: the middle vertex `v ∈ M` and the vertex `b ∈ B` are adjacent. -/
  adjB : M → Fin n → Prop
  /-- The set `W ⊆ A × B` of edges between `A` and `B`; Section 3.1 calls its elements the query
  pairs. -/
  W : Finset (Fin n × Fin n)

attribute [instance] LopInstance.fintypeM

/-- Definition 13: "a middle part M of at most D vertices".  An instance of Lop-AE-SparseTri(n, D),
and of #Lop-AE-SparseTri(n, D), is an `I : LopInstance n` with `I.MiddleAtMost D`. -/
def LopInstance.MiddleAtMost {n : ℕ} (I : LopInstance n) (D : ℕ) : Prop :=
  Fintype.card I.M ≤ D

/-- Definitions 13 and 14: the common neighbors of `a` and `b` in `M`. -/
def LopInstance.commonNeighbors {n : ℕ} (I : LopInstance n) (a b : Fin n) : Set I.M :=
  {v | I.adjA a v ∧ I.adjB v b}

/-- Definition 13: the pair `(a, b)` "lies in a triangle with some vertex of M, that is, [...] a and
b have a common neighbor in M". -/
def LopInstance.InTriangle {n : ℕ} (I : LopInstance n) (a b : Fin n) : Prop :=
  ∃ v : I.M, I.adjA a v ∧ I.adjB v b

/-- **Definition 14**: "the number of triangles it lies in, that is, the number of common
neighbors of a and b in M". -/
noncomputable def LopInstance.numTriangles {n : ℕ} (I : LopInstance n) (a b : Fin n) : ℕ :=
  (I.commonNeighbors a b).ncard

/-- **Definition 13**, the task: "Decide, for every edge (a, b) ∈ W, whether it lies in a triangle
with some vertex of M".  `ans` is a correct answer to the instance `I` of Lop-AE-SparseTri; its
values outside `W` are not constrained. -/
def LopInstance.IsDetectionAnswer {n : ℕ} (I : LopInstance n) (ans : Fin n × Fin n → Bool) : Prop :=
  ∀ q ∈ I.W, (ans q = true ↔ I.InTriangle q.1 q.2)

/-- Footnote 8, Section 3.1: "An instance of #Lop-AE-SparseTri(n,D) asks for the wanted entries of a
thin matrix product of two 0/1 matrices."  This is the instance that two matrices and a set `W` of
positions describe: the middle part is the set of the `D` column indices of `X`, and adjacency means
that the entry is 1. -/
def LopInstance.ofMatrices {n D : ℕ} (X : Matrix (Fin n) (Fin D) ℤ) (Y : Matrix (Fin D) (Fin n) ℤ)
    (W : Finset (Fin n × Fin n)) : LopInstance n where
  M := Fin D
  adjA a v := X a v = 1
  adjB v b := Y v b = 1
  W := W

abbrev ThinInstance := Lax350013.ThinMatrices.ThinInstance

/-- The entries of both matrices are 0 or 1: the two biadjacency matrices of an instance of
Lop-AE-SparseTri(N, D) (Section 3.1). -/
def ThinInstance.ZeroOne (x : ThinInstance) : Prop :=
  (∀ i j, x.X i j = 0 ∨ x.X i j = 1) ∧ (∀ i j, x.Y i j = 0 ∨ x.Y i j = 1)

/-- The instance of the lopsided triangle problems that two 0/1 matrices and a list of query pairs
describe.

NOTE.  Definition 13 has "a middle part M of at most D vertices"; here the middle part has exactly
`D` vertices, the columns of `X`.  A smaller middle part is written with zero columns of `X` and
zero rows of `Y`: vertices without edges, which lie in no triangle. -/
def ThinInstance.lop (x : ThinInstance) : LopInstance x.N :=
  LopInstance.ofMatrices x.X x.Y x.W.toFinset

/-- **#Lop-AE-SparseTri** (Definition 14), with the graph given by its two biadjacency matrices: the
`i`-th output cell holds the number of triangles through the `i`-th query pair. -/
def lopCount : Problem where
  Inst := ThinInstance
  params x := [x.N, x.D]
  input x := x.input []
  IsAnswer x verdict out :=
    verdict = true ∧ ∀ (i : ℕ) (h : i < x.W.length),
      out i = (x.lop.numTriangles x.W[i].1 x.W[i].2 : ℤ)

/-- **Lop-AE-SparseTri** (Definition 13): the `i`-th output cell holds 1 if the `i`-th query pair
lies in a triangle, and 0 if not. -/
def lopDetect : Problem where
  Inst := ThinInstance
  params x := [x.N, x.D]
  input x := x.input []
  IsAnswer x verdict out :=
    verdict = true ∧ ∀ (i : ℕ) (h : i < x.W.length),
      (x.lop.InTriangle x.W[i].1 x.W[i].2 → out i = 1) ∧
        (¬ x.lop.InTriangle x.W[i].1 x.W[i].2 → out i = 0)

end Lax350013.LopsidedTriangles
