/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Modified for the independent Lax packaging by Édouard Bonnet, 2026.
Derived from 3sum-apsp/ThreeSumApsp/Statements and RunningTimes at upstream commit e1a4e6508154ea59f030480661590a9fe3018011.
Changes: Lax module/namespace layout, separated concepts and proofs, archive
annotations, and compatibility with the archive Lean/mathlib environment.
See NOTICE and README.md in the submission root for provenance and scope.
-/

import Lax350013
import Lax350013Proofs.ThreeSumApsp.Statements.Exponents
import Lax350013Proofs.ThreeSumApsp.RunningTimes

namespace Lax350013Proofs.ThreeSumApsp

open WordRam

/--
---
conclusion: Lax350013.ExactTriangle.algorithm
---
The upstream conversion from the certified real-exponent bound to the rational-exponent formulation, preserving the program and input/output semantics.
-/
theorem lax_endStatement_theorem_19 : Lax350013.ExactTriangle.Theorem_19 :=
  (show Items.Theorem_19 from Lax350013.IntegerAlgorithmBounds.theorem19).rounded.endStatement (by norm_num [EndStatement.ε_T, Lax350013.ExactTriangle.ε_T])
    (by norm_num [EndStatement.ε_T, Lax350013.ExactTriangle.ε_T])

/--
---
conclusion: Lax350013.ThreeSUM.algorithm
---
The upstream conversion from the certified real-exponent bound to the rational-exponent formulation, preserving the program and input/output semantics.
-/
theorem lax_endStatement_theorem_22_3SUM : Lax350013.ThreeSUM.Theorem_22_3SUM :=
  (show Items.Theorem_22_second from Lax350013.IntegerAlgorithmBounds.theorem22_second).threeSum.endStatement (by norm_num) (by norm_num)

/--
---
conclusion: Lax350013.MinPlusProduct.algorithm
---
The upstream conversion from the certified real-exponent bound to the rational-exponent formulation, preserving the program and input/output semantics.
-/
theorem lax_endStatement_theorem_22_MinPlus : Lax350013.MinPlusProduct.Theorem_22_MinPlus :=
  (show Items.Theorem_22_second from Lax350013.IntegerAlgorithmBounds.theorem22_second).minPlus.endStatement (by norm_num) (by norm_num)

/--
---
conclusion: Lax350013.APSP.algorithm
---
The upstream conversion from the certified real-exponent bound to the rational-exponent formulation, preserving the program and input/output semantics.
-/
theorem lax_endStatement_theorem_22_APSP : Lax350013.APSP.Theorem_22_APSP :=
  (show Items.Theorem_22_second from Lax350013.IntegerAlgorithmBounds.theorem22_second).apsp.endStatement (by norm_num) (by norm_num)

/--
---
conclusion: Lax350013.ZeroWeightClique.algorithm
---
The upstream conversion from the certified real-exponent bound to the rational-exponent formulation, preserving the program and input/output semantics.
-/
theorem lax_endStatement_corollary_39_zeroWeight : Lax350013.ZeroWeightClique.Corollary_39_ZeroWeight :=
  by
  intro k hk
  have hdiv : ((k / 3 : ℕ) : ℚ) ≤ (k : ℚ) := by exact_mod_cast Nat.div_le_self k 3
  have hk0 : (0 : ℚ) ≤ (k : ℚ) := by positivity
  refine ((show Items.Corollary_39_zero from Lax350013.WeightedCliqueAlgorithms.zeroWeight) k hk).endStatement (by norm_num [EndStatement.ε_T, Lax350013.ExactTriangle.ε_T]) ?_
  norm_num [EndStatement.ε_T, Lax350013.ExactTriangle.ε_T]
  linarith

/--
---
conclusion: Lax350013.IntegerAlgorithmBounds.theorem19
---
The corresponding upstream theorem about programs of the word RAM. Direct uses of other exposed machine-level statements appear as proof-network dependencies.
-/
theorem lax_wordRam_theorem_19 : Lax350013.IntegerAlgorithmBounds.Theorem_19 :=
  wordRam_theorem_19

/--
---
conclusion: Lax350013.MatrixTradeoffs.theorem24
---
The corresponding upstream theorem about programs of the word RAM. Direct uses of other exposed machine-level statements appear as proof-network dependencies.
-/
theorem lax_wordRam_theorem_24 : Lax350013.MatrixTradeoffs.Theorem_24 :=
  wordRam_theorem_24

/--
---
conclusion: Lax350013.MatrixTradeoffs.corollary31
---
The corresponding upstream theorem about programs of the word RAM. Direct uses of other exposed machine-level statements appear as proof-network dependencies.
-/
theorem lax_wordRam_corollary_31 : Lax350013.MatrixTradeoffs.Corollary_31 :=
  wordRam_corollary_31

/--
---
conclusion: Lax350013.MatrixPreprocessing.corollary26
---
The corresponding upstream theorem about programs of the word RAM. Direct uses of other exposed machine-level statements appear as proof-network dependencies.
-/
theorem lax_wordRam_corollary_26 : Lax350013.MatrixPreprocessing.Corollary_26 :=
  wordRam_corollary_26

/--
---
conclusion: Lax350013.MatrixPreprocessing.theorem30
---
The corresponding upstream theorem about programs of the word RAM. Direct uses of other exposed machine-level statements appear as proof-network dependencies.
-/
theorem lax_wordRam_theorem_30 : Lax350013.MatrixPreprocessing.Theorem_30 :=
  wordRam_theorem_30

/--
---
conclusion: Lax350013.MatrixPreprocessing.theorem3
---
The corresponding upstream theorem about programs of the word RAM. Direct uses of other exposed machine-level statements appear as proof-network dependencies.
-/
theorem lax_wordRam_theorem_3 : Lax350013.MatrixPreprocessing.Theorem_3 :=
  ⟨(show Items.Corollary_26 from Lax350013.MatrixPreprocessing.corollary26), fun ε q hε hq =>
    dataStructureBelow_wantedBelow_epsStar.1 ε q (hε.trans sec4_epsStar_numeric.1) hq⟩

/--
---
conclusion: Lax350013.SparseMatrixProduct.theorem5
---
The corresponding upstream theorem about programs of the word RAM. Direct uses of other exposed machine-level statements appear as proof-network dependencies.
-/
theorem lax_wordRam_theorem_5 : Lax350013.SparseMatrixProduct.Theorem_5 :=
  wordRam_theorem_5

/--
---
conclusion: Lax350013.SparseMatrixProduct.theorem25
---
The corresponding upstream theorem about programs of the word RAM. Direct uses of other exposed machine-level statements appear as proof-network dependencies.
-/
theorem lax_wordRam_theorem_25 : Lax350013.SparseMatrixProduct.Theorem_25 :=
  wordRam_theorem_25

/--
---
conclusion: Lax350013.SparseMatrixProduct.corollary26_wanted
---
The corresponding upstream theorem about programs of the word RAM. Direct uses of other exposed machine-level statements appear as proof-network dependencies.
-/
theorem lax_wordRam_corollary_26_wanted : Lax350013.SparseMatrixProduct.Corollary_26_wanted :=
  wordRam_corollary_26_wanted

/--
---
conclusion: Lax350013.SparseMatrixProduct.theorem30_wanted
---
The corresponding upstream theorem about programs of the word RAM. Direct uses of other exposed machine-level statements appear as proof-network dependencies.
-/
theorem lax_wordRam_theorem_30_wanted : Lax350013.SparseMatrixProduct.Theorem_30_wanted :=
  wordRam_theorem_30_wanted

/--
---
conclusion: Lax350013.SparseMatrixProduct.corollary32
---
The corresponding upstream theorem about programs of the word RAM. Direct uses of other exposed machine-level statements appear as proof-network dependencies.
-/
theorem lax_wordRam_corollary_32 : Lax350013.SparseMatrixProduct.Corollary_32 :=
  wordRam_corollary_32

/--
---
conclusion: Lax350013.SparseMatrixProduct.theorem1
---
The corresponding upstream theorem about programs of the word RAM. Direct uses of other exposed machine-level statements appear as proof-network dependencies.
-/
theorem lax_wordRam_theorem_1 : Lax350013.SparseMatrixProduct.Theorem_1 :=
  ⟨fun c₀ => exists_solves_of_dominated ((show Items.Corollary_26_wanted from Lax350013.SparseMatrixProduct.corollary26_wanted) c₀)
      (fun x ⟨hD, hthin, _, hU⟩ => ⟨hD, hthin, hU⟩)
      (.of_le_const_mul zero_le_two fun x ⟨hD, _, hW, _⟩ =>
        corollary_26_W x.N x.D x.W.length hD hW),
    fun ε κ hε hκ =>
      dataStructureBelow_wantedBelow_epsStar.2 ε κ (hε.trans sec4_epsStar_numeric.1) hκ⟩

/--
---
conclusion: Lax350013.LopsidedTriangleAlgorithms.corollary15
---
The corresponding upstream theorem about programs of the word RAM. Direct uses of other exposed machine-level statements appear as proof-network dependencies.
-/
theorem lax_wordRam_corollary_15 : Lax350013.LopsidedTriangleAlgorithms.Corollary_15 :=
  wordRam_corollary_15

/--
---
conclusion: Lax350013.LopsidedTriangleAlgorithms.corollary16
---
The corresponding upstream theorem about programs of the word RAM. Direct uses of other exposed machine-level statements appear as proof-network dependencies.
-/
theorem lax_wordRam_corollary_16 : Lax350013.LopsidedTriangleAlgorithms.Corollary_16 :=
  wordRam_corollary_16

/--
---
conclusion: Lax350013.IntegerAlgorithmBounds.theorem22_first
---
The corresponding upstream theorem about programs of the word RAM. Direct uses of other exposed machine-level statements appear as proof-network dependencies.
-/
theorem lax_wordRam_theorem_22_first : Lax350013.IntegerAlgorithmBounds.Theorem_22_first :=
  wordRam_theorem_22_first

/--
---
conclusion: Lax350013.IntegerAlgorithmBounds.theorem22_second
---
The corresponding upstream theorem about programs of the word RAM. Direct uses of other exposed machine-level statements appear as proof-network dependencies.
-/
theorem lax_wordRam_theorem_22_second : Lax350013.IntegerAlgorithmBounds.Theorem_22_second :=
  wordRam_theorem_22_second

/--
---
conclusion: Lax350013.IntegerAlgorithmBounds.theorem22_threeSum
---
The corresponding upstream theorem about programs of the word RAM. Direct uses of other exposed machine-level statements appear as proof-network dependencies.
-/
theorem lax_wordRam_theorem_22_threeSum : Lax350013.IntegerAlgorithmBounds.Theorem_22_threeSum :=
  wordRam_theorem_22_threeSum

/--
---
conclusion: Lax350013.IntegerAlgorithmBounds.theorem2
---
The corresponding upstream theorem about programs of the word RAM. Direct uses of other exposed machine-level statements appear as proof-network dependencies.
-/
theorem lax_wordRam_theorem_2 : Lax350013.IntegerAlgorithmBounds.Theorem_2 :=
  ⟨(show Items.Theorem_19 from Lax350013.IntegerAlgorithmBounds.theorem19).rounded.mono_exponent (by norm_num),
    (show Items.Theorem_22_second from Lax350013.IntegerAlgorithmBounds.theorem22_second).apsp.mono_exponent (by norm_num),
    (show Items.Theorem_22_second from Lax350013.IntegerAlgorithmBounds.theorem22_second).minPlus.mono_exponent (by norm_num),
    (show Items.Theorem_22_second from Lax350013.IntegerAlgorithmBounds.theorem22_second).threeSum⟩

/--
---
conclusion: Lax350013.WeightedCliqueAlgorithms.zeroWeight
---
The corresponding upstream theorem about programs of the word RAM. Direct uses of other exposed machine-level statements appear as proof-network dependencies.
-/
theorem lax_wordRam_corollary_39_zero : Lax350013.WeightedCliqueAlgorithms.Corollary_39_zero :=
  wordRam_corollary_39_zero

/--
---
conclusion: Lax350013.WeightedCliqueAlgorithms.minMax
---
The corresponding upstream theorem about programs of the word RAM. Direct uses of other exposed machine-level statements appear as proof-network dependencies.
-/
theorem lax_wordRam_corollary_39_min_max : Lax350013.WeightedCliqueAlgorithms.Corollary_39_min_max :=
  wordRam_corollary_39_min_max

/--
---
conclusion: Lax350013.HintedAlgorithms.explicitTimes
---
The corresponding upstream theorem about programs of the word RAM. Direct uses of other exposed machine-level statements appear as proof-network dependencies.
-/
theorem lax_wordRam_corollary_40_times : Lax350013.HintedAlgorithms.Corollary_40_times :=
  wordRam_corollary_40_times

/--
---
conclusion: Lax350013.HintedAlgorithms.generalTimes
---
The corresponding upstream theorem about programs of the word RAM. Direct uses of other exposed machine-level statements appear as proof-network dependencies.
-/
theorem lax_wordRam_corollary_40_general_times : Lax350013.HintedAlgorithms.Corollary_40_general_times :=
  wordRam_corollary_40_general_times

/--
---
conclusion: Lax350013.HintedAlgorithms.theorem4
---
The corresponding upstream theorem about programs of the word RAM. Direct uses of other exposed machine-level statements appear as proof-network dependencies.
-/
theorem lax_wordRam_theorem_4 : Lax350013.HintedAlgorithms.Theorem_4 :=
  ⟨(show Items.Corollary_40_times from Lax350013.HintedAlgorithms.explicitTimes), wordRam_corollary_40_fail.1,
    Corollary40.fail_mono (by norm_num) sec4_epsStar_numeric.1.le wordRam_corollary_40_fail.2⟩

end Lax350013Proofs.ThreeSumApsp
