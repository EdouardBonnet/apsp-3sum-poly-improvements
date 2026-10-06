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
import Lax350013.CliqueOptimization
import Lax350013.RAMResources

/-!
---
title: Faster weighted clique algorithms
type: theorem
---
Corollary 39 gives deterministic time $O(n^{k-0.0017\lfloor k/3\rfloor})$ for zero-weight clique detection and for finding a minimum- or maximum-weight clique, for every fixed $k\geq3$ and polynomially bounded integer weights.
-/

namespace Lax350013.WeightedCliqueAlgorithms

open Finset
open Lax350013.WordRAM
open Lax350013.RAMResources
open Lax350013.CliqueOptimization

/-- **Corollary 39**, the case of Zero-Weight k-Clique.  The paper: "Let k ≥ 3 and ν ≥ 1 be
constants.  Given a complete k-partite graph with parts of n vertices and integer edge weights of
absolute value at most n^ν, deterministic algorithms decide in O(n^{k−ε_T⌊k/3⌋}) time whether some
k-clique, with one vertex in each part, has total edge weight zero". -/
def Corollary_39_zero : Prop :=
  ∀ k : ℕ, 3 ≤ k →
    SolvedInTime (Lax350013.ZeroWeightClique.ZeroWeightKClique k) ((k : ℝ) - 0.0017 * ((k / 3 : ℕ) : ℝ)) 0

/-- **Corollary 39**, the other two cases: "deterministic algorithms [...] in
O(n^{k−ε_T⌊k/3⌋}) time [...] find a k-clique of minimum, or of maximum, total edge weight."  The
hypotheses are those of `Corollary_39_zero`; `ε_T = 0.0017` (Theorem 19).  That the time bound
covers finding, and not only deciding, is confirmed by the end of the paper's proof. -/
def Corollary_39_min_max : Prop :=
  ∀ k : ℕ, 3 ≤ k →
    SolvedInTime (MinKClique k) ((k : ℝ) - 0.0017 * ((k / 3 : ℕ) : ℝ)) 0 ∧
    SolvedInTime (MaxKClique k) ((k : ℝ) - 0.0017 * ((k / 3 : ℕ) : ℝ)) 0

/-- Faster weighted clique algorithms: Corollary 39 zero. -/
axiom zeroWeight : Corollary_39_zero


/-- Faster weighted clique algorithms: Corollary 39 min max. -/
axiom minMax : Corollary_39_min_max

end Lax350013.WeightedCliqueAlgorithms
