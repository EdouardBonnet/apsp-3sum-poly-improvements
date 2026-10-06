/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Modified for the independent Lax packaging by Édouard Bonnet, 2026.
Derived from 3sum-apsp/ThreeSumApsp/Programs/Sec3/Theorem19/BruteForceClaim.lean at upstream commit e1a4e6508154ea59f030480661590a9fe3018011.
Changes: Lax module/namespace layout, separated concepts and proofs, archive
annotations, and compatibility with the archive Lean/mathlib environment.
See NOTICE and README.md in the submission root for provenance and scope.
-/

import Lax350013Proofs.ThreeSumApsp.Programs.LightModel
import Lax350013Proofs.ThreeSumApsp.Programs.Sec3.Theorem17.Witnesses.BruteForce

namespace Lax350013Proofs

/-!
# The running time of brute force (the proof of Theorem 19)

The `100 n³ + 100` steps of brute are within the form `C n³ (1 + log u)` in which the running times
for Exact Triangle with weights of absolute value at most `u` are stated (`claim_bruteForce`).
-/

section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-- "Smaller instances are solved by brute force" (proof of Theorem 19): Exact Triangle is
solved in time `C n³ (1 + log u)`, where `u` bounds the absolute values of the weights.  The factor
`1 + log u` is not needed here; it belongs to the form of the running times for this problem. -/
theorem claim_bruteForce : Claim.BruteForce lightModel := by
  refine ⟨200, [bruteBody 1, scanBody], 0, fun n _ => tBrute n, bruteNeed, ⟨2, 1, fun n U => ?_⟩,
    brute_solves, fun n U u hn _ _ => ?_⟩
  · have hbound : polyBound 2 1 [n, U] = 4 * ((n + 1) * (U + 1)) := by simp [polyBound]
    have hU : U + 1 ≤ (n + 1) * (U + 1) := Nat.le_mul_of_pos_left _ (by omega)
    rw [hbound]
    simp only [bruteNeed]
    exact ⟨by omega, by omega, by omega⟩
  · have hlog : 0 ≤ logU u := Real.log_nonneg (le_trans (by norm_num) (le_max_right u 2))
    have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast hn)
    calc ((tBrute n : ℕ) : ℝ) = 100 * (n : ℝ) ^ 3 + 100 := by rw [tBrute]; push_cast; rfl
      _ ≤ 200 * ((n : ℝ) ^ 3 * 1) := by linarith
      _ ≤ 200 * ((n : ℝ) ^ 3 * (1 + logU u)) := by gcongr; linarith

end Light.Sec3
end

end Lax350013Proofs
