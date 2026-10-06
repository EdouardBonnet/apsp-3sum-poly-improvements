/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Modified for the independent Lax packaging by Édouard Bonnet, 2026.
Derived from 3sum-apsp/ThreeSumApsp/Programs/Sec4/Theorem30/RoutineFacts.lean at upstream commit e1a4e6508154ea59f030480661590a9fe3018011.
Changes: Lax module/namespace layout, separated concepts and proofs, archive
annotations, and compatibility with the archive Lean/mathlib environment.
See NOTICE and README.md in the submission root for provenance and scope.
-/

import Lax350013Proofs.ThreeSumApsp.Programs.Sec4.Theorem30.Contracts

namespace Lax350013Proofs

/-!
# What outDigits writes is the output string of the position

Nothing here is about programs.  The digits of the output string of a position are those that
outDigits writes (`digitsO_outStrOfPos`): both lists are the `L` digits of the code of the string
(`digitList_ofDigitList`, `digitList_outCodeOfPos`).
-/

section

open ThreeSumApsp

namespace Light.Sec4

open ThreeSumApsp.Spec

/-! ## The digits of the output string of a position -/

/-- The digits of the output string of the position (I, J), for the computable layout. -/
theorem digitsO_outStrOfPos {L m : ℕ} (hmL : m ≤ L) (I J : ℕ) :
    digitsO (outStrOfPos (stdLayout hmL) I J) = outDigitsOfPos L m I J := by
  have hdigits := digitList_ofDigitList _ (digitsO_lt (outStrOfPos (stdLayout hmL) I J))
  rw [length_digitsO, ofDigitList_digitsO, codeO_outStrOfPos, digitList_outCodeOfPos] at hdigits
  exact hdigits.symm

end Light.Sec4
end

end Lax350013Proofs
