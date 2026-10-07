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
import Lax350013.ExactTriangle
import Lax350013.ThreeSUM
import Lax350013.MinPlusProduct
import Lax350013.APSP
import Lax350013.RAMResources
import Lax350013.CallableAlgorithms

/-!
---
title: Integer algorithms before rounding the exponents
type: theorem
---
Theorem 19 gives Exact Triangle bounds from both constructions. Theorem 22 carries these improvements to 3SUM, min-plus product and APSP, retaining the logarithmic and $o(1)$ factors before rounding. These statements are deterministic integer word-RAM bounds; they do not assert the paper’s real-RAM or randomized bounds. The callable versions also preserve memory and resource guarantees needed when these algorithms are used as subroutines.
-/

namespace Lax350013.IntegerAlgorithmBounds

open Finset
open Lax350013.WordRAM
open Lax350013.RAMResources

/-- **Theorem 19**: "For every constant ν ≥ 1, Exact Triangle on n vertices per part with
integer weights of absolute value at most n^ν can be solved by a deterministic algorithm in
O(n^{3−1/648} log² n) time [...], and in O(n^{3−ε'} log n) ≤ O(n^{3−ε_T}) time", with `ε' = 0.00175`
and `ε_T = 0.0017`.  (The paper reaches the first bound using Theorem 5 and the second using
Corollary 26.  This cannot be said by "there is a program": as statements about the existence of
programs, the first and the third bound follow from the second, which is smaller.) -/
def Theorem_19 : Prop :=
  SolvedInTime Lax350013.ExactTriangle.ExactTriangle (3 - 1 / 648) 2 ∧
  SolvedInTime Lax350013.ExactTriangle.ExactTriangle (3 - 0.00175) 1 ∧
  SolvedInTime Lax350013.ExactTriangle.ExactTriangle (3 - 0.0017) 0

/-- **Theorem 22**, the bounds "Using Theorem 5": 3SUM in `O(n^{1.99923})` time, "and the
(min,+)-product [...] as well as APSP [...] in Õ(n^{3−1/1944}) ≤ O(n^{2.99949}) time".  (The
intermediate form `n^{2−1/1296+o(1)}` for 3SUM is `Theorem_22_threeSum` below.  "Using Theorem 5"
cannot be said by "there is a program": as statements about the existence of programs, all five
bounds follow from those of `Theorem_22_second`, which are smaller.) -/
def Theorem_22_first : Prop :=
  SolvedInTime Lax350013.ThreeSUM.ThreeSum 1.99923 0 ∧
  SolvedInPolylogTime Lax350013.MinPlusProduct.MinPlusProduct (3 - 1 / 1944) ∧
  SolvedInPolylogTime Lax350013.APSP.APSP (3 - 1 / 1944) ∧
  SolvedInTime Lax350013.MinPlusProduct.MinPlusProduct 2.99949 0 ∧
  SolvedInTime Lax350013.APSP.APSP 2.99949 0

/-- **Theorem 22**, the bounds "Using Corollary 26 instead": 3SUM in `O(n^{1.9992})` time,
the (min,+)-product and APSP in "Õ(n^{3−ε'/3}) ≤ O(n^{2.99942})" time, with
`ε' = 0.00175`.  (The intermediate form `n^{2−ε'/2+o(1)}` for 3SUM is `Theorem_22_threeSum`
below.) -/
def Theorem_22_second : Prop :=
  SolvedInTime Lax350013.ThreeSUM.ThreeSum 1.9992 0 ∧
  SolvedInPolylogTime Lax350013.MinPlusProduct.MinPlusProduct (3 - 0.00175 / 3) ∧
  SolvedInPolylogTime Lax350013.APSP.APSP (3 - 0.00175 / 3) ∧
  SolvedInTime Lax350013.MinPlusProduct.MinPlusProduct 2.99942 0 ∧
  SolvedInTime Lax350013.APSP.APSP 2.99942 0

/-- **Theorem 22**, the two bounds for 3SUM before rounding: "Using Theorem 5 (through
Theorem 19), deterministic algorithms solve 3SUM on n integers of absolute value at most n^ν in
n^{2−1/1296+o(1)} ≤ O(n^{1.99923}) time [...].  Using Corollary 26 instead, the times are
n^{2−ε'/2+o(1)} ≤ O(n^{1.9992}) [...]", with `ε' = 0.00175`. The rounded bounds are in
`Theorem_22_first` and `Theorem_22_second`.  (As a statement about the existence of programs, the
first bound follows from the second, which is smaller.) -/
def Theorem_22_threeSum : Prop :=
  SolvedInLittleOTime Lax350013.ThreeSUM.ThreeSum (2 - 1 / 1296) ∧
  SolvedInLittleOTime Lax350013.ThreeSUM.ThreeSum (2 - 0.00175 / 2)

/-- **Theorem 2**, the deterministic half: "On a word RAM with O(log n)-bit words,
deterministic algorithms solve the following problems, where all numbers in the input are integers
of absolute value n^{O(1)}: Exact Triangle on n-vertex graphs in O(n^{2.9983}) time, APSP on
directed n-vertex graphs with no negative cycles in O(n^{2.9995}) time, the (min,+)-product of two
n × n matrices in O(n^{2.9995}) time, and 3SUM on n numbers in O(n^{1.9992}) time."  (For APSP and
the (min,+)-product, Theorem 22 prints the smaller exponent 2.99942: `Theorem_22_second`.)

NOTE.  Here Exact Triangle has the tripartite form of Section 3.2, with `n` vertices per part; for
`n`-vertex graphs see `Theorem_2_graphs`. -/
def Theorem_2 : Prop :=
  SolvedInTime Lax350013.ExactTriangle.ExactTriangle 2.9983 0 ∧
  SolvedInTime Lax350013.APSP.APSP 2.9995 0 ∧
  SolvedInTime Lax350013.MinPlusProduct.MinPlusProduct 2.9995 0 ∧
  SolvedInTime Lax350013.ThreeSUM.ThreeSum 1.9992 0

/-- Integer algorithms before rounding the exponents: Theorem 19. -/
axiom theorem19 : Theorem_19


/-- Integer algorithms before rounding the exponents: Theorem 22 first. -/
axiom theorem22_first : Theorem_22_first


/-- Integer algorithms before rounding the exponents: Theorem 22 second. -/
axiom theorem22_second : Theorem_22_second


/-- Integer algorithms before rounding the exponents: Theorem 22 threeSum. -/
axiom theorem22_threeSum : Theorem_22_threeSum


/-- Integer algorithms before rounding the exponents: Theorem 2. -/
axiom theorem2 : Theorem_2


/-- Callable contract proved by upstream `Light.Sec3.claim_theorem_19_usingTheorem5`. -/
axiom callableExactTriangleFirst : Lax350013.CallableAlgorithms.Claim.Theorem_19_explicit Lax350013.CallableAlgorithms.lightModel (1 / 648) 2


/-- Callable contract proved by upstream `Light.Sec3.claim_theorem_19_usingCorollary26`. -/
axiom callableExactTriangleSecond : Lax350013.CallableAlgorithms.Claim.Theorem_19_explicit Lax350013.CallableAlgorithms.lightModel 0.00175 1


/-- Callable contract proved by upstream `Light.Sec3.claim_exactTriangleUniform_usingTheorem5`. -/
axiom uniformExactTriangleFirst : Lax350013.CallableAlgorithms.Claim.ExactTriangleUniform Lax350013.CallableAlgorithms.lightModel (1 / 648) 2


/-- Callable contract proved by upstream `Light.Sec3.claim_exactTriangleUniform_usingCorollary26`. -/
axiom uniformExactTriangleSecond : Lax350013.CallableAlgorithms.Claim.ExactTriangleUniform Lax350013.CallableAlgorithms.lightModel 0.00175 1

end Lax350013.IntegerAlgorithmBounds
