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
import Lax350013.MatrixTradeoffs
import Lax350013.CallableAlgorithms

/-!
---
title: Explicit thin matrix preprocessing bounds
type: theorem
---
Corollary 26 gives $O(N^2/D^{0.063})$ preprocessing time and space and $O(D^{0.437})$ time per query for $1\leq D$ and $D^{18}\leq N$. Theorem 30 gives the underlying bounds at integer recursion parameters. Theorem 3 extends the trade-off to every $\varepsilon<0.1204$ and every positive query exponent. The callable versions also preserve memory and resource guarantees needed when these algorithms are used as subroutines.
-/

namespace Lax350013.MatrixPreprocessing

open Finset
open Lax350013.WordRAM
open Lax350013.RAMResources
open Lax350013.ThinMatrices
open Lax350013.MatrixParameters
open Lax350013.MatrixTradeoffs

/-- **Corollary 26**, first two sentences: "Let N ≥ D^18, and let X ∈ ℤ^{N×D} and Y ∈ ℤ^{D×N}
have entries of absolute value at most N^{O(1)}.  We can preprocess them deterministically in
O(N²/D^{0.063}) time and space, after which any single entry (XY)[I,J] can be computed
deterministically in O(D^{0.437}) time."

NOTE.  The paper states no lower bound on `D`; `D ≥ 1` is assumed (for `D = 0` the bound
`O(D^{0.437})` would be 0 steps). -/
def Corollary_26 : Prop :=
  ∀ c : ℕ, ∃ (P Q : List Instr) (qI qJ qOut : ℤ) (b : ℕ) (C : ℝ),
    IsDataStructure P Q qI qJ qOut b [] (fun x => 1 ≤ x.D ∧ x.D ^ 18 ≤ x.N ∧ x.U = x.N ^ c)
      (fun x => C * ((x.N : ℝ) ^ 2 / (x.D : ℝ) ^ (0.063 : ℝ)))
      (fun x => C * ((x.N : ℝ) ^ 2 / (x.D : ℝ) ^ (0.063 : ℝ)))
      (fun x => C * (x.D : ℝ) ^ (0.437 : ℝ))

/-- The hypotheses of **Theorem 30**: "Let m ≥ 1, D = 4^m, L ≥ 10m, 0 ≤ t ≤ m, and N ≥ √K
N₀", with entries "of absolute value at most N^{O(1)}". -/
def theorem30Dom (c m L t : ℕ) (x : ThinPair) : Prop :=
  1 ≤ m ∧ x.D = 4 ^ m ∧ 10 * m ≤ L ∧ t ≤ m ∧ Real.sqrt (K L m) * (N0 L m : ℝ) ≤ (x.N : ℝ) ∧
    x.U = x.N ^ c

/-- **Theorem 30**: "we can preprocess them deterministically in time and space" (8).  "After
this, any single entry (XY)[I,J] can be computed deterministically in O(L ∑_{d=0}^{t}
α_d) time."  "The constants hidden in the O(·) depend only on the exponent in N^{O(1)}": the
constant `C` is chosen after the exponent `c` and before `m`, `L`, `t`.  These parameters are given
to the preprocessing after `N` and `D`; the two programs do not depend on them. -/
def Theorem_30 : Prop :=
  ∀ c : ℕ, ∃ (P Q : List Instr) (qI qJ qOut : ℤ) (b : ℕ) (C : ℝ), ∀ m L t : ℕ,
    IsDataStructure P Q qI qJ qOut b [(m : ℤ), (L : ℤ), (t : ℤ)] (theorem30Dom c m L t)
      (fun x => C * cost8 L m t x.N) (fun x => C * cost8 L m t x.N) (fun _ => C * costQuery L m t)

/-- **Theorem 3**: "Let N ≥ D^18, and let X ∈ ℤ^{N×D}, Y ∈ ℤ^{D×N} have entries of absolute
value N^{O(1)}. The pair (X,Y) can be preprocessed deterministically in O(N²/D^{0.063}) time [...].
After this, any single entry (XY)[I,J] can be computed deterministically in O(D^{0.437}) time [...].
More generally, for every ε < 0.1204 and every q > 0 there is a γ > 0 such that, whenever D ≤ N^ε,
the pair can be preprocessed in O(N²/D^γ) time, after which any single entry can be computed in
O(D^q) time."  The first part is `Corollary_26`.

NOTE.  The departures are those of the two definitions: `D ≥ 1` in the first part; `D ≥ 1` and
`N ≥ 1` in the second; and in both the space is bounded like the time, while the theorem speaks of
time only. -/
def Theorem_3 : Prop :=
  Corollary_26 ∧ DataStructureBelow 0.1204

/-- Explicit thin matrix preprocessing bounds: Corollary 26. -/
axiom corollary26 : Corollary_26


/-- Explicit thin matrix preprocessing bounds: Theorem 30. -/
axiom theorem30 : Theorem_30


/-- Explicit thin matrix preprocessing bounds: Theorem 3. -/
axiom theorem3 : Theorem_3


/-- Callable contract proved by upstream `Light.Sec4.claim_corollary_26_wanted`. -/
axiom callableCorollary26 : Lax350013.CallableAlgorithms.Claim.Corollary_26_wanted Lax350013.CallableAlgorithms.lightModel

end Lax350013.MatrixPreprocessing
