/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Modified for the independent Lax packaging by Édouard Bonnet, 2026.
Derived from 3sum-apsp/ThreeSumApsp/Programs/Sec3/Theorem17/Hashing/ZOrderFacts.lean at upstream commit e1a4e6508154ea59f030480661590a9fe3018011.
Changes: Lax module/namespace layout, separated concepts and proofs, archive
annotations, and compatibility with the archive Lean/mathlib environment.
See NOTICE and README.md in the submission root for provenance and scope.
-/

import Lax350013Proofs.ThreeSumApsp.Lang.Lib.Seg
import Lax350013Proofs.ThreeSumApsp.Spec.Sec3.Theorem17.ZOrder
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Lax350013Proofs

/-!
# The table of `spread`: small facts

`spread i` is the number whose digits in base 4 are the binary digits of i; the place of the entry
(a, c) of a matrix in Z-order is 2 spread a + spread c.  The routines that write matrices in Z-order
and the routine that reads the count off their product look `spread` up in a table,
`spreadList n`, the list of spread 0, …, spread (n - 1).  Here are the facts on the table that both
use: a bound on its entries, how it grows, and what a cell of it holds.
-/

section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-- The number whose digits in base 4 are the binary digits of i is at most i². -/
theorem spread_le_sq (i : ℕ) : spread i ≤ i * i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [spread_zero]
    · have h := ih (i / 2) (by omega)
      rw [spread_eq]
      obtain ⟨q, b, hb, rfl⟩ : ∃ q b, b < 2 ∧ i = 2 * q + b :=
        ⟨i / 2, i % 2, Nat.mod_lt _ (by norm_num), by omega⟩
      rw [show (2 * q + b) / 2 = q by omega] at h ⊢
      rw [show (2 * q + b) % 2 = b by omega]
      nlinarith

theorem spreadList_succ (i : ℕ) : spreadList (i + 1) = spreadList i ++ [((spread i : ℕ) : ℤ)] := by
  simp [spreadList, List.range_succ]

theorem length_spreadList (i : ℕ) : (spreadList i).length = i := by simp [spreadList]

/-- A cell of the table. -/
theorem seg_spreadList_get {μ : ℕ → ℤ} {a n i : ℕ} (h : Seg μ a (spreadList n)) (hi : i < n) :
    μ (a + i) = (spread i : ℕ) := by
  have := h i (by rw [length_spreadList]; exact hi)
  simpa [spreadList] using this

end Light.Sec3
end

end Lax350013Proofs
