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
import Lax350013.LopsidedTriangles
import Lax350013.CallableAlgorithms

/-!
---
title: Faster lopsided triangle algorithms
type: theorem
---
Corollary 16 solves counting and detection in $O(|W|D^{0.437}+N^2/D^{0.063})$ time for $1\leq D$ and $D^{18}\leq N$. Corollary 15 records the earlier logarithmic bound for powers of four. The callable versions also preserve memory and resource guarantees needed when these algorithms are used as subroutines.
-/

namespace Lax350013.LopsidedTriangleAlgorithms

open Finset
open Lax350013.WordRAM
open Lax350013.RAMResources
open Lax350013.ThinMatrices
open Lax350013.LopsidedTriangles

/-- **Corollary 15**: "Let D ≥ 4 be a power of four with n ≥ D^18, and consider an instance
of #Lop-AE-SparseTri(n,D) or of Lop-AE-SparseTri(n,D) with |W| query pairs.  If |W| ≤ n²/√D, then
the instance can be solved deterministically in O(n² log² D/D^{1/18}) time.  In general, [...] in
time O((n² + |W|√D) log² D/D^{1/18})." The general bound contains the first one, since
`|W|√D ≤ n²` there.  (As a statement about the existence of programs, this follows from
`Corollary_16`, whose bound is smaller; see the remark at `Theorem_5`.) -/
def Corollary_15 : Prop :=
  ∃ (Pc Pd : List Instr) (b : ℕ) (C : ℝ),
    Solves lopCount Pc b
      (fun x => x.ZeroOne ∧ x.U = 1 ∧ (∃ k : ℕ, x.D = 4 ^ k) ∧ 4 ≤ x.D ∧ x.D ^ 18 ≤ x.N)
      (fun x => C * (((x.N : ℝ) ^ 2 + (x.W.length : ℝ) * Real.sqrt x.D) * Real.log x.D ^ 2 /
        (x.D : ℝ) ^ (1 / 18 : ℝ))) ∧
    Solves lopDetect Pd b
      (fun x => x.ZeroOne ∧ x.U = 1 ∧ (∃ k : ℕ, x.D = 4 ^ k) ∧ 4 ≤ x.D ∧ x.D ^ 18 ≤ x.N)
      (fun x => C * (((x.N : ℝ) ^ 2 + (x.W.length : ℝ) * Real.sqrt x.D) * Real.log x.D ^ 2 /
        (x.D : ℝ) ^ (1 / 18 : ℝ)))

/-- **Corollary 16**: "Let n ≥ D^18, and consider an instance of #Lop-AE-SparseTri(n,D) or
of Lop-AE-SparseTri(n,D) with |W| query pairs.  It can be solved deterministically in O(|W|
D^{0.437} + n²/D^{0.063}) time."

NOTE.  The paper states no lower bound on `D`; `D ≥ 1` is assumed, as in `Corollary_26` below. -/
def Corollary_16 : Prop :=
  ∃ (Pc Pd : List Instr) (b : ℕ) (C : ℝ),
    Solves lopCount Pc b (fun x => x.ZeroOne ∧ x.U = 1 ∧ 1 ≤ x.D ∧ x.D ^ 18 ≤ x.N)
      (fun x => C * ((x.W.length : ℝ) * (x.D : ℝ) ^ (0.437 : ℝ) +
        (x.N : ℝ) ^ 2 / (x.D : ℝ) ^ (0.063 : ℝ))) ∧
    Solves lopDetect Pd b (fun x => x.ZeroOne ∧ x.U = 1 ∧ 1 ≤ x.D ∧ x.D ^ 18 ≤ x.N)
      (fun x => C * ((x.W.length : ℝ) * (x.D : ℝ) ^ (0.437 : ℝ) +
        (x.N : ℝ) ^ 2 / (x.D : ℝ) ^ (0.063 : ℝ)))

/-- Faster lopsided triangle algorithms: Corollary 15. -/
axiom corollary15 : Corollary_15


/-- Faster lopsided triangle algorithms: Corollary 16. -/
axiom corollary16 : Corollary_16


/-- Callable contract proved by upstream `Light.Sec3.claim_corollary_15_first`. -/
axiom callableCorollary15First : Lax350013.CallableAlgorithms.Claim.Corollary_15_first Lax350013.CallableAlgorithms.lightModel


/-- Callable contract proved by upstream `Light.Sec3.claim_corollary_15`. -/
axiom callableCorollary15General : Lax350013.CallableAlgorithms.Claim.Corollary_15_general Lax350013.CallableAlgorithms.lightModel


/-- Callable contract proved by upstream `Light.Sec3.claim_corollary_16`. -/
axiom callableCorollary16 : Lax350013.CallableAlgorithms.Claim.Corollary_16 Lax350013.CallableAlgorithms.lightModel

end Lax350013.LopsidedTriangleAlgorithms
