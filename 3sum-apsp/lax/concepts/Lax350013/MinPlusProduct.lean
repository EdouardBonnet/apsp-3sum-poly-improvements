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
title: Truly subcubic min-plus matrix multiplication
type: theorem
---
The min-plus product of two $n\times n$ matrices with polynomially bounded integer entries can be computed deterministically in $O(n^{2.99942})$ word-RAM steps (Theorem 22). The output contains the minimum of $A_{ik}+B_{kj}$ for each pair $(i,j)$.
-/

namespace Lax350013.MinPlusProduct

open Lax350013.PolynomialTime

/-- Output, row by row: entry `(i, j)` is the least of the sums `A i k + B k j`. -/
def MinPlusProduct : Problem where
  Instance n := (Fin n → Fin n → Int) × (Fin n → Fin n → Int)
  input := fun (A, B) => rowByRow A ++ rowByRow B
  output := fun {n} (A, B) out => ∀ i j : Fin n,
    (∃ k, out (i.val * n + j.val) = A i k + B k j) ∧ ∀ k, out (i.val * n + j.val) ≤ A i k + B k j

/-- Theorem 22: «the (min, +)-product of two n × n integer matrices», in time «O(n^2.99942)». -/
def Theorem_22_MinPlus : Prop :=
  MinPlusProduct.SolvedInTime 2.99942

/-- Truly subcubic min-plus matrix multiplication: Theorem 22 MinPlus. -/
axiom algorithm : Theorem_22_MinPlus

end Lax350013.MinPlusProduct
