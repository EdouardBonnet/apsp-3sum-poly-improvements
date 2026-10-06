/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Modified for the independent Lax packaging by Édouard Bonnet, 2026.
Derived from 3sum-apsp/ThreeSumApsp/RunningTimes/Sec3/Theorem19.lean at upstream commit e1a4e6508154ea59f030480661590a9fe3018011.
Changes: Lax module/namespace layout, separated concepts and proofs, archive
annotations, and compatibility with the archive Lean/mathlib environment.
See NOTICE and README.md in the submission root for provenance and scope.
-/

import Lax350013Proofs.ThreeSumApsp.Programs.Sec3.Theorem17.ClaimAtParameters
import Lax350013Proofs.ThreeSumApsp.Programs.Sec3.Theorem19.BruteForceClaim
import Lax350013Proofs.ThreeSumApsp.Programs.Sec3.Theorem19.ChooseBySize
import Lax350013Proofs.ThreeSumApsp.RunningTimes.Sec3.Corollary15_16
import Lax350013Proofs.ThreeSumApsp.RunningTimes.Sec3.Theorem19.Layout
import Lax350013Proofs.ThreeSumApsp.TimeClaims.Sec3.Theorem19

namespace Lax350013Proofs

/-!
# Theorem 19 on the word RAM

The route, as in the paper.  Theorem 17 reduces Exact Triangle to instances of the lopsided triangle
problem.  With the parameters `D` and `g` of Section 3.3 and Corollary 15 for the instances the
total is `O(n^{3−1/648} log² n)` (`claim_theorem_19_usingTheorem5`); with Corollary 16 it is
`O(n^{3−ε'} log n)`, `ε' = 0.00175` (`claim_theorem_19_usingCorollary26`).  Both are claims about
programs of the light language that keep the dependence on `κ`.  The outermost procedure for the
input layout and the compiler (`Light.Sec3.realized_exactTriangle`) carry them to the word RAM.
The third bound of the theorem, `O(n^{3−ε_T})`, follows from the second, so it rests on Corollary 16
and not on Corollary 15.

Section 3.4 needs the two bounds for all numbers of vertices and all bounds on the weights:
`claim_exactTriangleUniform_usingTheorem5`, `claim_exactTriangleUniform_usingCorollary26`.  They
combine the program with brute force below a threshold, as in the proof ("smaller instances are
solved by brute force").
-/

section

open ThreeSumApsp ThreeSumApsp.WordRam

namespace Light.Sec3

/-- Theorem 19, the bound using Theorem 5, for programs of the light language. -/
theorem claim_theorem_19_usingTheorem5 : Claim.Theorem_19_explicit lightModel (1 / 648) 2 :=
  Theorem19.explicit_of_theorem_17_corollary_15 _ claim_theorem_17₅ claim_corollary_15_first

/-- Theorem 19, the bound using Corollary 26, for programs of the light language. -/
theorem claim_theorem_19_usingCorollary26 : Claim.Theorem_19_explicit lightModel 0.00175 1 :=
  Theorem19.explicit_of_theorem_17_corollary_16 _ claim_theorem_17₂₆ claim_corollary_16

/-- A program that solves Exact Triangle in time `T` solves it in every larger time. -/
private theorem closure_monoExactTriangle : Closure.MonoExactTriangle lightModel :=
  fun _ _ hle hT => SolvedIn.mono hT hle

/-- The bound using Theorem 5, for all numbers of vertices and all bounds on the weights. -/
theorem claim_exactTriangleUniform_usingTheorem5 :
    Claim.ExactTriangleUniform lightModel (1 / 648) 2 :=
  exactTriangleUniform_of_explicit _ 2 (by norm_num) (by norm_num) claim_theorem_19_usingTheorem5
    claim_bruteForce closure_chooseBySize closure_monoExactTriangle

/-- The bound using Corollary 26, for all numbers of vertices and all bounds on the weights. -/
theorem claim_exactTriangleUniform_usingCorollary26 :
    Claim.ExactTriangleUniform lightModel 0.00175 1 :=
  exactTriangleUniform_of_explicit _ 1 (by norm_num) (by norm_num) claim_theorem_19_usingCorollary26
    claim_bruteForce closure_chooseBySize closure_monoExactTriangle

end Light.Sec3

namespace ThreeSumApsp

/-- **Theorem 19**, on the word RAM. -/
theorem wordRam_theorem_19 : Items.Theorem_19 :=
  FromClaims.Theorem19.of_claim Light.lightModel Light.Sec3.realized_exactTriangle
    (Theorem19.first_of_explicit _ Light.Sec3.claim_theorem_19_usingTheorem5)
    (Theorem19.second_of_explicit _ Light.Sec3.claim_theorem_19_usingCorollary26)

/-- The third bound of the theorem, `O(n^{3−ε_T})`. -/
theorem WordRam.Items.Theorem_19.rounded (h : Items.Theorem_19) :
    SolvedInTime EndStatement.ExactTriangle (3 - 0.0017) 0 :=
  h.2.2

end ThreeSumApsp
end

end Lax350013Proofs
