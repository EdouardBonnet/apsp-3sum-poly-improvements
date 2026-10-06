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

import Lax350013.PolynomialTime

/-!
---
title: Truly subquadratic 3SUM
type: theorem
---
Given $n$ polynomially bounded integers, a deterministic word-RAM program decides whether three distinct positions contain numbers summing to zero in $O(n^{1.9992})$ steps (Theorem 22, using Corollary 26).
-/

namespace Lax350013.ThreeSUM

open Lax350013.PolynomialTime

/-- Section 1: «Given n numbers, decide whether three of them sum to 0». Three different positions. -/
def ThreeSum : Problem where
  Instance n := Fin n → Int
  input x := List.ofFn x
  yes x := ∃ i j k, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ x i + x j + x k = 0

/-- Theorem 22: «solve 3SUM on n integers of absolute value at most n^ν», in time «O(n^1.9992)». -/
def Theorem_22_3SUM : Prop :=
  ThreeSum.SolvedInTime 1.9992

/-- Truly subquadratic 3SUM: Theorem 22 3SUM. -/
axiom algorithm : Theorem_22_3SUM

end Lax350013.ThreeSUM
