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
title: Truly subcubic all-pairs shortest paths
type: theorem
---
All-pairs shortest paths in a directed graph with $n$ vertices, polynomially bounded integer edge weights and no negative cycles can be computed deterministically in $O(n^{2.99942})$ word-RAM steps (Theorem 22). Each output pair contains a reachability flag and, when reachable, the minimum weight of a path. Paths may repeat vertices.
-/

namespace Lax350013.APSP

open Lax350013.PolynomialTime

/-- A path and its total weight; it may repeat vertices. -/
inductive Path {n : Nat} (w : Fin n → Fin n → Option Int) : Fin n → Fin n → Int → Prop
  | nil (i : Fin n) : Path w i i 0
  | cons {i j k : Fin n} {d e : Int} : w i j = some d → Path w j k e → Path w i k (d + e)

/-- Input: the 0/1 matrix of the edges, then the weights, with 0 for no edge. Output, two cells for each `(i, j)`: 1 if
there is a path, else 0; then the distance. -/
def APSP : Problem where
  Instance n := {w : Fin n → Fin n → Option Int // ∀ i d, Path w i i d → 0 ≤ d}
  input := fun ⟨w, _⟩ => rowByRow (fun i j => if (w i j).isSome then 1 else 0) ++ rowByRow fun i j => (w i j).getD 0
  output := fun {n} ⟨w, _⟩ out => ∀ i j : Fin n,
    let flag := out (2 * (i.val * n + j.val))
    let dist := out (2 * (i.val * n + j.val) + 1)
    (flag = 1 ∧ Path w i j dist ∧ ∀ e, Path w i j e → dist ≤ e) ∨ (flag = 0 ∧ ∀ e, ¬ Path w i j e)

/-- Theorem 22: «APSP on directed n-vertex graphs … and no negative cycles», in time «O(n^2.99942)». -/
def Theorem_22_APSP : Prop :=
  APSP.SolvedInTime 2.99942

/-- Truly subcubic all-pairs shortest paths: Theorem 22 APSP. -/
axiom algorithm : Theorem_22_APSP

end Lax350013.APSP
