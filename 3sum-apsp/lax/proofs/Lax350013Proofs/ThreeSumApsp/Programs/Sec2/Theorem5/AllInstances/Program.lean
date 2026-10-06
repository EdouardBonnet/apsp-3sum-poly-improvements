/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Modified for the independent Lax packaging by Édouard Bonnet, 2026.
Derived from 3sum-apsp/ThreeSumApsp/Programs/Sec2/Theorem5/AllInstances/Program.lean at upstream commit e1a4e6508154ea59f030480661590a9fe3018011.
Changes: Lax module/namespace layout, separated concepts and proofs, archive
annotations, and compatibility with the archive Lean/mathlib environment.
See NOTICE and README.md in the submission root for provenance and scope.
-/

import Lax350013Proofs.ThreeSumApsp.Programs.Sec2.Theorem5.AllInstances.Solver
import Lax350013Proofs.ThreeSumApsp.Programs.Sec2.Theorem5.Program

namespace Lax350013Proofs

/-!
# The running-time claim "Theorem 5" for the light model, for the program of Theorem 5

programThin is program5 followed by regimeBody (the test whether an instance is in the regime of
Theorem 5), thinBruteBody (the brute force, for the instances outside it) and thinBody (the solver
for all instances). claim_theorem_5: it solves the thin matrix product on all instances, and for D ≥
4 a power of four, N ≥ D^18, w ≤ N²/√D and entries of at most N^c its time is at most a constant
times N² log² D / D^{1/18}. This is thin_claim for the program and the solver of Theorem 5.
-/

section

namespace Light.Sec2

open ThreeSumApsp

/-- The program of the thin matrix product on all instances. -/
def programThin : Program := program5 ++ [regimeBody, thinBruteBody, thinBody]

/-- **Theorem 5**, for programs of the light language. -/
theorem claim_theorem_5 : Claim.Theorem_5 lightModel :=
  thin_claim length_program5 rfl fun R => thm5_spec (mainCallees_of_prefix R)

end Light.Sec2
end

end Lax350013Proofs
