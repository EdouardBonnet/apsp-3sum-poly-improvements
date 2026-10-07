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
import Lax350013.CallableAlgorithms

/-!
---
title: Callable reductions between the algorithmic problems
type: theorem
---
Theorem 17 reduces Exact Triangle to lopsided triangle detection at the two parameter choices used in the paper. Theorem 21 transfers an Exact Triangle solver to 3SUM, min-plus products and APSP. Additional reductions turn selected matrix entries into triangle counts and detection, and split large query sets. All are proved transformations of callable programs. The callable versions also preserve memory and resource guarantees needed when these algorithms are used as subroutines.
-/

namespace Lax350013.AlgorithmReductions

open Finset

/-- Callable contract proved by upstream `Light.Sec3.claim_theorem_17₅`. -/
axiom exactTriangleViaTheorem5 : Lax350013.CallableAlgorithms.Claim.Theorem_17 Lax350013.CallableAlgorithms.lightModel Lax350013.CallableAlgorithms.strassen Lax350013.CallableAlgorithms.paramD₅ Lax350013.CallableAlgorithms.paramG₅


/-- Callable contract proved by upstream `Light.Sec3.claim_theorem_17₂₆`. -/
axiom exactTriangleViaCorollary26 : Lax350013.CallableAlgorithms.Claim.Theorem_17 Lax350013.CallableAlgorithms.lightModel Lax350013.CallableAlgorithms.strassen Lax350013.CallableAlgorithms.paramD₂₆ Lax350013.CallableAlgorithms.paramG₂₆


/-- Callable contract proved by upstream `Light.Sec3.claim_theorem_21a`. -/
axiom threeSumFromExactTriangle : Lax350013.CallableAlgorithms.Claim.Theorem_21a Lax350013.CallableAlgorithms.lightModel


/-- Callable contract proved by upstream `Light.Sec3.claim_theorem_21b_minPlus`. -/
axiom minPlusFromExactTriangle : Lax350013.CallableAlgorithms.Claim.Theorem_21b_minPlus Lax350013.CallableAlgorithms.lightModel


/-- Callable contract proved by upstream `Light.Sec3.claim_theorem_21b_apsp`. -/
axiom apspFromExactTriangle : Lax350013.CallableAlgorithms.Claim.Theorem_21b_apsp Lax350013.CallableAlgorithms.lightModel


/-- Callable contract proved by upstream `Light.Sec3.claim_lopCountFromThinProduct`. -/
axiom triangleCountsFromMatrixProduct : Lax350013.CallableAlgorithms.Claim.LopCountFromThinProduct Lax350013.CallableAlgorithms.lightModel


/-- Callable contract proved by upstream `Light.Sec3.claim_lopDetectFromCount`. -/
axiom triangleDetectionFromCounts : Lax350013.CallableAlgorithms.Claim.LopDetectFromCount Lax350013.CallableAlgorithms.lightModel


/-- Callable contract proved by upstream `Light.Sec3.claim_lopSplit`. -/
axiom splitTriangleQueries : Lax350013.CallableAlgorithms.Claim.LopSplit Lax350013.CallableAlgorithms.lightModel

end Lax350013.AlgorithmReductions
