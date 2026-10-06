/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Modified for the independent Lax packaging by Édouard Bonnet, 2026.
Derived from 3sum-apsp/ThreeSumApsp/Spec/Sec3/Theorem17/ClassStarts.lean at upstream commit e1a4e6508154ea59f030480661590a9fe3018011.
Changes: Lax module/namespace layout, separated concepts and proofs, archive
annotations, and compatibility with the archive Lean/mathlib environment.
See NOTICE and README.md in the submission root for provenance and scope.
-/

import Lax350013Proofs.ThreeSumApsp.Spec.Sec3.Theorem17.Chunks

namespace Lax350013Proofs

/-!
# Pure facts about the starts of the classes and the table of chunks

Proof of Theorem 17.  The `n²` pairs `(a, b)` are listed class after class, where the class
of a residue `ϱ < p` holds the pairs whose weight is congruent to `ϱ` modulo the prime `p`, and each
class is cut into chunks of at most `cap` pairs.  The list of the starts of the classes has `p + 1`
entries, none above `n²`; the table of chunks has at most `n² + p` entries.
-/

section

namespace ThreeSumApsp.Spec

/-- The list of the starts of the classes has one entry for each residue, and one more for the
end. -/
theorem length_classStarts (n p : ℕ) (RAB : List ℕ) : (classStarts n p RAB).length = p + 1 := by
  simp [classStarts]

/-- A class starts at a place of the list of all n² pairs, or at its end. -/
theorem classStart_le_sq (n : ℕ) (RAB : List ℕ) (rho : ℕ) : classStart n RAB rho ≤ n * n := by
  rw [classStart_eq_length_filter]
  exact (List.length_filter_le _ _).trans (List.length_range).le

/-- No entry of the list of the starts of the classes is above n². -/
theorem le_of_mem_classStarts {n p : ℕ} {RAB : List ℕ} {x : ℕ} (hx : x ∈ classStarts n p RAB) :
    x ≤ n * n := by
  obtain ⟨rho, -, rfl⟩ := List.mem_map.1 hx
  exact classStart_le_sq n RAB rho

/-- If `cap ≥ 1` and every residue is below `p`, the table of chunks has at most `n² + p` entries.
This is the number of cells that the host procedure of Theorem 17 reserves for each of its three
components. -/
theorem length_chunkTab_le_add {n p cap : ℕ} {RAB : List ℕ} (hcap : 1 ≤ cap)
    (hlt : ∀ i < n * n, RAB.getD i 0 < p) : (chunkTab n p cap RAB).length ≤ n * n + p := by
  have hlen := length_chunkTab_le hcap hlt
  have hdiv := Nat.div_le_self (n * n) cap
  omega

end ThreeSumApsp.Spec
end

end Lax350013Proofs
