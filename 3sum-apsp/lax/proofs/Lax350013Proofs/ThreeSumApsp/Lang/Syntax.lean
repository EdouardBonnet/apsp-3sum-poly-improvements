/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Modified for the independent Lax packaging by Édouard Bonnet, 2026.
Derived from 3sum-apsp/ThreeSumApsp/Lang/Syntax.lean at upstream commit e1a4e6508154ea59f030480661590a9fe3018011.
Changes: Lax module/namespace layout, separated concepts and proofs, archive
annotations, and compatibility with the archive Lean/mathlib environment.
See NOTICE and README.md in the submission root for provenance and scope.
-/

import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Lax350013.StructuredPrograms

namespace Lax350013Proofs

/-!
# The light language

A small imperative language with procedures and recursion, in which the paper's procedures can be
written almost as printed.  It is a proof device: a program of this language is compiled
(`compileProgram`) to the word RAM of the end statement, and the compiler is proved to keep results
and, up to a constant factor that depends on the program text only, step counts.

* A program is a finite piece of data: a list of procedure bodies.  It contains no Lean functions.
* The memory is an array of integers addressed by natural numbers.  Each running procedure has local
  variables 0, 1, 2, ….
* Arithmetic: +, −, ×.  There is no division.  Comparisons (<, =) occur as the tests of if and
  while.
* Every executed operation costs one step: each constant, variable, operation and load of an
  expression, each comparison, assignment, store, branch, call and return.
* A run is subject to limits: it forms no value of absolute value above `word`, touches no cell at
  an address ≥ `space`, and nests calls at most `depth` deep.  A run that would break a limit does
  not exist.
-/

section

namespace Light

/- The operations on two words. -/
export Lax350013.StructuredPrograms (Op Op.add Op.sub Op.mul)

/- The result of an operation. -/
export Lax350013.StructuredPrograms (Op.eval)

/- Expressions: constants, local variables, operations, and the content of the memory cell at an
address. -/
export Lax350013.StructuredPrograms (Expr Expr.const Expr.var Expr.op Expr.load)

/- Tests. -/
export Lax350013.StructuredPrograms (Cond Cond.lt Cond.eq)

/- Statements.  `call p args x` runs procedure number p on the values of args and puts its result
into x. -/
export Lax350013.StructuredPrograms (Stmt Stmt.skip Stmt.set Stmt.store Stmt.seq Stmt.ite Stmt.while Stmt.call)

/- A program: the bodies of its procedures, numbered from 0. -/
export Lax350013.StructuredPrograms (Program)

/- What a running procedure sees: its local variables and the memory. -/
export Lax350013.StructuredPrograms (State State.mk State.loc State.mem)

/- The limits on a run: largest absolute value of a word, number of memory cells, nesting depth of
calls. -/
export Lax350013.StructuredPrograms (Limits Limits.mk Limits.word Limits.space Limits.depth)

/- The value of an expression. -/
export Lax350013.StructuredPrograms (Expr.val)

/- The number of steps that evaluating an expression takes: one for each of its constants,
variables, operations, loads. -/
export Lax350013.StructuredPrograms (Expr.cost)

/- An address within the limits. -/
export Lax350013.StructuredPrograms (Limits.Addr)

/- The evaluation of an expression stays within the limits: every value that is formed fits in a
word, and every address that is read is within the memory. -/
export Lax350013.StructuredPrograms (Expr.Safe)

/- Whether a test holds. -/
export Lax350013.StructuredPrograms (Cond.Holds)

/- The number of steps of a test: its two sides and the comparison. -/
export Lax350013.StructuredPrograms (Cond.cost)

/- The evaluation of a test stays within the limits. -/
export Lax350013.StructuredPrograms (Cond.Safe)

/- The local variables of a procedure that has just been called: the arguments in 0, 1, …, and 0 in
all others. -/
export Lax350013.StructuredPrograms (frame)

/- The memory that holds the list ws in the cells 0, 1, 2, … and 0 elsewhere. -/
export Lax350013.StructuredPrograms (memOf)

/- `Exec lim P d s σ σ' c`: within the limits lim, and at nesting depth d of calls, the statement
s of the program P, started in the state σ, ends in the state σ' after exactly c steps. -/
export Lax350013.StructuredPrograms (Exec Exec.skip Exec.set Exec.store Exec.seq Exec.iteTrue Exec.iteFalse Exec.whileFalse Exec.whileTrue Exec.call)

/- Everything held in a variable or in a cell fits in a word. -/
export Lax350013.StructuredPrograms (State.Bounded)

end Light
end

end Lax350013Proofs
