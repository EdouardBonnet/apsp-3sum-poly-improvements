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
import Lax350013.ZeroWeightClique

/-!
---
title: Minimum- and maximum-weight multipartite cliques
type: definition
---
For fixed $k$, output the vertices of a minimum- or maximum-weight clique with one vertex from each of $k$ parts of size $n$. The encoding contains all $k^2$ blocks; the objective sums only the edges with part indices $i<j$.
-/

namespace Lax350013.CliqueOptimization

open Finset

/-- The total edge weight of the `k`-clique that has the vertex `v p` in part `p` (Corollary 39):
the sum, over the pairs of parts `p < q`, of the weight between `v p` and `v q`. -/
def cliqueWeight {k n : ℕ} (w : Fin k → Fin k → Fin n → Fin n → ℤ) (v : Fin k → Fin n) : ℤ :=
  ∑ p : Fin k, ∑ q ∈ Finset.univ.filter (fun q : Fin k => p < q), w p q (v p) (v q)

/-- **Min-Weight `k`-Clique** (Corollary 39): accept, and leave in the `p`-th of the `k`
output cells (`p = 0, …, k − 1`) the number, below `n`, of the vertex chosen in part `p`, so that
the `k` vertices form a `k`-clique of minimum total edge weight.  Every such clique is accepted.

NOTE.  The parts have at least one vertex: at `n = 0` there is no clique to output. -/
def MinKClique (k : ℕ) : Lax350013.PolynomialTime.Problem where
  Instance n := {_w : Fin k → Fin k → Fin n → Fin n → ℤ // 1 ≤ n}
  input w := (Lax350013.ZeroWeightClique.ZeroWeightKClique k).input w.1
  output {n} w out := ∃ v : Fin k → Fin n, (∀ p : Fin k, out p.val = ((v p).val : ℤ)) ∧
    ∀ v', cliqueWeight w.1 v ≤ cliqueWeight w.1 v'

/-- **Max-Weight `k`-Clique** (Corollary 39): the same with maximum total edge weight. -/
def MaxKClique (k : ℕ) : Lax350013.PolynomialTime.Problem where
  Instance n := {_w : Fin k → Fin k → Fin n → Fin n → ℤ // 1 ≤ n}
  input w := (Lax350013.ZeroWeightClique.ZeroWeightKClique k).input w.1
  output {n} w out := ∃ v : Fin k → Fin n, (∀ p : Fin k, out p.val = ((v p).val : ℤ)) ∧
    ∀ v', cliqueWeight w.1 v' ≤ cliqueWeight w.1 v

end Lax350013.CliqueOptimization
