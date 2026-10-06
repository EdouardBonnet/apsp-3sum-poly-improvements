/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Modified for the independent Lax packaging by Édouard Bonnet, 2026.
Derived from 3sum-apsp/ThreeSumApsp/Machine/Realized.lean at upstream commit e1a4e6508154ea59f030480661590a9fe3018011.
Changes: Lax module/namespace layout, separated concepts and proofs, archive
annotations, and compatibility with the archive Lean/mathlib environment.
See NOTICE and README.md in the submission root for provenance and scope.
-/

import Lax350013Proofs.ThreeSumApsp.Machine.Solving

namespace Lax350013Proofs

/-!
# A running time that is realized on the word RAM

The deductions between running-time claims are made for an arbitrary reading `M : DetTimeModel` of
"is solved by a deterministic algorithm in time T".  `RealizedWithin` is the link to programs: the
problem is solved on the word RAM, in its input layout, within `c T + c` steps.
-/

section

open EndStatement (Instr)

namespace ThreeSumApsp.WordRam

/-- For every exponent `κ` some program solves the problem `prob` on all instances in `dom` of size
`n ≥ 1` whose numbers are bounded by `U = n^κ`, within `c T + c` steps for some constant `c ≥ 0`.

On the machine every number occupies one cell, and the slope of the word size is chosen after the
exponent `κ`.  The running-time claims allow for numbers that take several words; their bounds are
correspondingly larger, and hold all the more when a number fits into one word. -/
def RealizedWithin (prob : Problem) (size bound : prob.Inst → ℕ) (dom : prob.Inst → Prop)
    (T : prob.Inst → ℝ) : Prop :=
  ∀ κ : ℕ, ∃ (P : List Instr) (b : ℕ) (c : ℝ), 0 ≤ c ∧
    Solves prob P b (fun x => dom x ∧ 1 ≤ size x ∧ bound x = size x ^ κ) (fun x => c * T x + c)

/-- `RealizedWithin` for a problem of the form of `EndStatement.lean`, on the instances of all
sizes, 0 included: for every exponent `κ` some program solves all instances whose numbers are
bounded by `U = n^κ`, within `c max(T, 0) + c` steps. (A running time `T n U` says nothing at
`n = 0`.) -/
def Realized (Q : EndStatement.Problem) (T : ℕ → ℝ → ℝ) : Prop :=
  ∀ κ : ℕ, ∃ (P : List Instr) (b : ℕ) (c : ℝ), 0 ≤ c ∧
    Solves (ofEnd Q) P b (fun x => x.U = x.n ^ κ) (fun x => c * max (T x.n x.U) 0 + c)

end ThreeSumApsp.WordRam
end

end Lax350013Proofs
