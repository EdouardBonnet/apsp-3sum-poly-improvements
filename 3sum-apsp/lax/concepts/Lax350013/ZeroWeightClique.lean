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
import Lax350013.ExactTriangle

/-!
---
title: Faster zero-weight k-clique
type: theorem
---
For every fixed $k\geq 3$, a zero-weight clique with one vertex in each of $k$ parts of size $n$ is decidable deterministically in $O(n^{k-0.0017\lfloor k/3\rfloor})$ word-RAM steps. Edge weights are polynomially bounded integers (Corollary 39).
-/

namespace Lax350013.ZeroWeightClique

open Lax350013.PolynomialTime
open Lax350013.ExactTriangle

/-- `w i j u v`: weight between `u` in part `i` and `v` in part `j`. All `k²` blocks are input; only `i < j` counts. -/
def ZeroWeightKClique (k : Nat) : Problem where
  Instance n := Fin k → Fin k → Fin n → Fin n → Int
  input w := (List.ofFn fun i => (List.ofFn fun j => rowByRow (w i j)).flatten).flatten
  yes {n} w := ∃ v : Fin k → Fin n,
    (List.ofFn fun j => (List.ofFn fun i => if i < j then w i j (v i) (v j) else 0).sum).sum = 0

/-- Corollary 39: «decide in O(n^(k−ε_T⌊k/3⌋)) time whether some k-clique … has total edge weight zero». -/
def Corollary_39_ZeroWeight : Prop :=
  ∀ k ≥ 3, (ZeroWeightKClique k).SolvedInTime (k - ε_T * (k / 3 : Nat))

/-- Faster zero-weight k-clique: Corollary 39 ZeroWeight. -/
axiom algorithm : Corollary_39_ZeroWeight

end Lax350013.ZeroWeightClique
