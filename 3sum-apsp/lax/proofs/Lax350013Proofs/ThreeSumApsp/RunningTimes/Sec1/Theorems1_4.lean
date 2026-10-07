/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Modified for the independent Lax packaging by Édouard Bonnet, 2026.
Derived from 3sum-apsp/ThreeSumApsp/RunningTimes/Sec1/Theorems1_4.lean at upstream commit e1a4e6508154ea59f030480661590a9fe3018011.
Changes: Lax module/namespace layout, separated concepts and proofs, archive
annotations, and compatibility with the archive Lean/mathlib environment.
See NOTICE and README.md in the submission root for provenance and scope.
-/

import Lax350013Proofs.ThreeSumApsp.RunningTimes.Sec3.Theorem19.GraphsLayout
import Lax350013Proofs.ThreeSumApsp.RunningTimes.Sec3.Theorem22
import Lax350013Proofs.ThreeSumApsp.RunningTimes.Sec4.Corollary26
import Lax350013Proofs.ThreeSumApsp.RunningTimes.Sec4.Corollary31_32
import Lax350013Proofs.ThreeSumApsp.RunningTimes.Sec5.Corollary40
import Lax350013.HintedAlgorithms
import Lax350013.IntegerAlgorithmBounds
import Lax350013.MatrixPreprocessing
import Lax350013.SparseMatrixProduct

namespace Lax350013Proofs

/-!
# Theorems 1 to 4 on the word RAM

The theorems of the introduction restate later items.

* Theorem 1: the last sentence of Corollary 26 with `|W| ≤ N²/√D` (`corollary_26_W`), and Theorem
  25 without its logarithms (`dataStructureBelow_wantedBelow_epsStar`), for `ε < 0.1204 < ε*`.
* Theorem 2, the deterministic sentence: the last bound of Theorem 19 and the bounds of Theorem 22
  using Corollary 26, where `2.9995` is above `2.99942` (`SolvedInTime.mono_exponent`).  Its first
  line is printed for `n`-vertex graphs: "an instance on an arbitrary `n`-vertex graph reduces to
  this form by taking three copies of the vertex set" (Section 3.2), which is one more program
  (`Light.Sec3.Theorem2.graphs_of`).
* Theorem 3: Corollary 26, and Theorem 24 without its logarithms (the same lemma), for
  `ε < 0.1204 < ε*`.
* Theorem 4: Corollary 40.
-/

section

open ThreeSumApsp.WordRam

namespace ThreeSumApsp

/-- **Theorem 1**, on the word RAM. -/
theorem wordRam_theorem_1 : Items.Theorem_1 :=
  ⟨fun c₀ => exists_solves_of_dominated ((show Items.Corollary_26_wanted from Lax350013.SparseMatrixProduct.corollary26_wanted) c₀)
      (fun x ⟨hD, hthin, _, hU⟩ => ⟨hD, hthin, hU⟩)
      (.of_le_const_mul zero_le_two fun x ⟨hD, _, hW, _⟩ =>
        corollary_26_W x.N x.D x.W.length hD hW),
    fun ε κ hε hκ =>
      dataStructureBelow_wantedBelow_epsStar.2 ε κ (hε.trans sec4_epsStar_numeric.1) hκ⟩

/-- **Theorem 2**, the four deterministic lines, on the word RAM. -/
theorem wordRam_theorem_2 : Items.Theorem_2 :=
  ⟨(show Items.Theorem_19 from Lax350013.IntegerAlgorithmBounds.theorem19).rounded.mono_exponent (by norm_num),
    (show Items.Theorem_22_second from Lax350013.IntegerAlgorithmBounds.theorem22_second).apsp.mono_exponent (by norm_num),
    (show Items.Theorem_22_second from Lax350013.IntegerAlgorithmBounds.theorem22_second).minPlus.mono_exponent (by norm_num),
    (show Items.Theorem_22_second from Lax350013.IntegerAlgorithmBounds.theorem22_second).threeSum⟩

/-- **Theorem 2**, first line for `n`-vertex graphs, on the word RAM. -/
theorem wordRam_theorem_2_graphs : Items.Theorem_2_graphs :=
  Light.Sec3.Theorem2.graphs_of
    (exactTriangleIn_of_explicit _ Lax350013.IntegerAlgorithmBounds.callableExactTriangleSecond)

/-- **Theorem 3**, on the word RAM. -/
theorem wordRam_theorem_3 : Items.Theorem_3 :=
  ⟨(show Items.Corollary_26 from Lax350013.MatrixPreprocessing.corollary26), fun ε q hε hq =>
    dataStructureBelow_wantedBelow_epsStar.1 ε q (hε.trans sec4_epsStar_numeric.1) hq⟩

/-- **Theorem 4**, on the word RAM. -/
theorem wordRam_theorem_4 : Items.Theorem_4 :=
  ⟨(show Items.Corollary_40_times from Lax350013.HintedAlgorithms.explicitTimes), wordRam_corollary_40_fail.1,
    Corollary40.fail_mono (by norm_num) sec4_epsStar_numeric.1.le wordRam_corollary_40_fail.2⟩

end ThreeSumApsp
end

end Lax350013Proofs
