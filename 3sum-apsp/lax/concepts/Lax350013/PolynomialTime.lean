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

import Lax350013.WordRAM

/-!
---
title: Uniform polynomial time on the word RAM
type: definition
---
For each fixed input-magnitude exponent $\kappa$, one program, one word-size coefficient and one time bound work for every input size and every admissible word size. The input integers have absolute value at most $n^\kappa$ and the words have at least $b(\lfloor\log_2 n\rfloor+1)$ bits. The verdict and the output cells must both be correct. Rational exponents are expressed using integer powers.
-/

namespace Lax350013.PolynomialTime

open Lax350013.WordRAM

/-- `T(n) = O(n^r)`, both sides raised to the power `r.den`: core Lean has no fractional powers. For `r = 1.9992 =
2499/1250` it says `T(n)^1250 ≤ K n^2499`. -/
def BigO (T : Nat → Nat) (r : Rat) : Prop :=
  ∃ K : Nat, ∀ n ≥ 2, T n ^ r.den ≤ K * n ^ r.num.toNat

/-- `yes`: when to accept (always, if not given). `output`: a condition on the cells after the input, read as signed. -/
structure Problem where
  Instance : Nat → Type
  input {n : Nat} : Instance n → List Int
  yes {n : Nat} : Instance n → Prop := fun _ => True
  output {n : Nat} : Instance n → (Nat → Int) → Prop := fun _ _ => True

/-- One run: with `n` in cell 0 and the input after it, `P` halts within `t` steps with the right verdict and output. -/
def Problem.SolvedBy (Q : Problem) {n : Nat} (x : Q.Instance n) (P : List Instr) (W t : Nat) : Prop :=
  ∃ verdict m, exec P t 0 (loadWords W ((n : Int) :: Q.input x)) = some (verdict, m) ∧
    (verdict = true ↔ Q.yes x) ∧ Q.output x fun a => (m (1 + (Q.input x).length + a : Nat)).toInt

/-- Theorem 2: «a word RAM with O(log n)-bit words», «all numbers in the input are integers of absolute value
n^O(1)»: for every `κ`, one `P`, `b`, `T` for all instances, correct at every `W ≥ b(⌊log₂ n⌋ + 1)`. -/
def Problem.SolvedInTime (Q : Problem) (r : Rat) : Prop :=
  ∀ κ : Nat, ∃ (P : List Instr) (b : Nat) (T : Nat → Nat), BigO T r ∧
    ∀ (n : Nat) (x : Q.Instance n), (∀ a ∈ Q.input x, a.natAbs ≤ n ^ κ) → ∀ W ≥ b * (Nat.log2 n + 1),
      Q.SolvedBy x P W (T n)

def rowByRow {n : Nat} (w : Fin n → Fin n → Int) : List Int :=
  (List.ofFn fun u => List.ofFn fun v => w u v).flatten

end Lax350013.PolynomialTime
