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
title: Truly subcubic Exact Triangle
type: theorem
---
Exact Triangle on a complete tripartite graph with $n$ vertices in each part and polynomially bounded integer weights is decidable deterministically in $O(n^{2.9983})$ word-RAM steps (Theorem 19). A triangle is accepted exactly when its three edge weights sum to zero.
-/

namespace Lax350013.ExactTriangle

open Lax350013.PolynomialTime

/-- Section 3.2: «S(a, b, c) := w(a, b) + w(b, c) + w(a, c). A zero triangle is a triangle … with S(a, b, c) = 0». -/
def ExactTriangle : Problem where
  Instance n := (Fin n → Fin n → Int) × (Fin n → Fin n → Int) × (Fin n → Fin n → Int)
  input := fun (wAB, wBC, wAC) => rowByRow wAB ++ rowByRow wBC ++ rowByRow wAC
  yes := fun (wAB, wBC, wAC) => ∃ a b c, wAB a b + wBC b c + wAC a c = 0

/-- Theorem 19: «ε_T := 0.0017». -/
def ε_T : Rat := 0.0017

/-- Theorem 19: «Exact Triangle … can be solved by a deterministic algorithm in … O(n^(3−ε_T)) time». -/
def Theorem_19 : Prop :=
  ExactTriangle.SolvedInTime (3 - ε_T)

/-- Truly subcubic Exact Triangle: Theorem 19. -/
axiom algorithm : Theorem_19

end Lax350013.ExactTriangle
