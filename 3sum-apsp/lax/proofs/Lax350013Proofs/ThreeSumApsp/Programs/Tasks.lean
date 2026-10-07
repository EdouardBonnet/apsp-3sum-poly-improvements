/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Modified for the independent Lax packaging by Édouard Bonnet, 2026.
Derived from 3sum-apsp/ThreeSumApsp/Programs/Tasks.lean at upstream commit e1a4e6508154ea59f030480661590a9fe3018011.
Changes: Lax module/namespace layout, separated concepts and proofs, archive
annotations, and compatibility with the archive Lean/mathlib environment.
See NOTICE and README.md in the submission root for provenance and scope.
-/

import Lax350013Proofs.ThreeSumApsp.Lang.Lib.ArrayAt
import Lax350013Proofs.ThreeSumApsp.Lang.Tactics
import Lax350013Proofs.ThreeSumApsp.Lang.Tasks
import Lax350013Proofs.ThreeSumApsp.Spec.Sec3.Problems
import Lax350013Proofs.ThreeSumApsp.Util.Flag
import Lax350013.CallableProblems

namespace Lax350013Proofs

/-!
# The problems of the paper as tasks

* The problems for Section 3.4 have a size and a bound (`Task`).
* The problems of Theorem 5 and of Section 3.1 have the parameters `N`, `D`, `w` and `U` (`TaskN`).
  The calling convention is the same: sizes, the bound, the addresses of the arrays, the address of
  the output, and the free pointer last.  The three tasks: the wanted entries of a thin matrix
  product (`thinTask`; Theorem 5 and Corollary 26), #Lop-AE-SparseTri (`lopCountTask`;
  Definition 14) and Lop-AE-SparseTri (`lopDetectTask`; Definition 13).  All three have the same
  instances (`ThinInst`).
* What "solved in time `T`" means for them: `ThinSolvedIn`, `LopSolvedIn`.
-/

section

open ThreeSumApsp

namespace Light

open ThreeSumApsp.Spec

/-! ## The problems for Section 3.4 -/

/- Three `n × n` matrices of weights in the memory. -/
export Lax350013.CallableProblems (TriInst TriInst.mk TriInst.n TriInst.U TriInst.ab TriInst.bc TriInst.ac TriInst.AB TriInst.BC TriInst.AC)

/- The three matrices lie below the free pointer, and their entries are bounded by `U`. -/
export Lax350013.CallableProblems (TriInst.Pre TriInst.Pre.mk TriInst.Pre.n_pos TriInst.Pre.U_pos TriInst.Pre.lenAB TriInst.Pre.lenBC TriInst.Pre.lenAC TriInst.Pre.segAB TriInst.Pre.segBC TriInst.Pre.segAC TriInst.Pre.leAB TriInst.Pre.leBC TriInst.Pre.leAC TriInst.Pre.belowAB TriInst.Pre.belowBC TriInst.Pre.belowAC)

/-- An instance stays where it is if no cell below the free pointer changes. -/
theorem TriInst.Pre.keep {x : TriInst} {μ μ' : ℕ → ℤ} {fr : ℕ} (h : x.Pre μ fr)
    (hs : Kept μ μ' fr := by light_keep) : x.Pre μ' fr := by
  light_facts h
  exact { h with segAB := h.segAB.keep, segBC := h.segBC.keep, segAC := h.segAC.keep }

with_weak_namespace _root_.Lax350013.CallableProblems.TriInst.Pre export _root_.Lax350013Proofs.Light.TriInst.Pre («keep»)

/-- The free pointer may grow. -/
theorem TriInst.Pre.mono {x : TriInst} {μ : ℕ → ℤ} {fr fr' : ℕ} (h : x.Pre μ fr) (hfr : fr ≤ fr') :
    x.Pre μ fr' :=
  { h with
    belowAB := h.belowAB.trans hfr
    belowBC := h.belowBC.trans hfr
    belowAC := h.belowAC.trans hfr }

with_weak_namespace _root_.Lax350013.CallableProblems.TriInst.Pre export _root_.Lax350013Proofs.Light.TriInst.Pre («mono»)

/-- Three matrices one after the other, with the free pointer behind them, are an instance. -/
theorem triPre_of_arrays {n U base : ℕ} {AB BC AC : List ℤ} {μ : ℕ → ℤ} (hn : 1 ≤ n) (hU : 1 ≤ U)
    (hAB : ArrayAt μ base AB (n * n) U (base + 3 * (n * n)))
    (hBC : ArrayAt μ (base + n * n) BC (n * n) U (base + 3 * (n * n)))
    (hAC : ArrayAt μ (base + 2 * (n * n)) AC (n * n) U (base + 3 * (n * n))) :
    (⟨n, U, base, base + n * n, base + 2 * (n * n), AB, BC, AC⟩ : TriInst).Pre μ
      (base + 3 * (n * n)) :=
  ⟨hn, hU, hAB.len, hBC.len, hAC.len, hAB.seg, hBC.seg, hAC.seg, hAB.bound, hBC.bound, hAC.bound,
    hAB.below, hBC.below, hAC.below⟩

/-- **Exact Triangle**: et(n, U, ab, bc, ac, fr) returns 1 if there is a zero triangle and 0 if not.
-/
noncomputable def etTask : Task where
  Inst := TriInst
  size x := x.n
  bound x := x.U
  args x := [x.n, x.U, x.ab, x.bc, x.ac]
  Pre := TriInst.Pre
  Post x μ fr r μ' := r = flag (triOf x.n x.AB x.BC x.AC).HasZeroTriangle ∧ Kept μ μ' fr

/-- **Negative Triangle**: nt(n, U, ab, bc, ac, fr) returns 1 if there is a negative triangle and 0
if not. -/
noncomputable def ntTask : Task where
  Inst := TriInst
  size x := x.n
  bound x := x.U
  args x := [x.n, x.U, x.ab, x.bc, x.ac]
  Pre := TriInst.Pre
  Post x μ fr r μ' := r = flag (triOf x.n x.AB x.BC x.AC).HasNegativeTriangle ∧ Kept μ μ' fr

/- A list of `N` numbers in the memory. -/
export Lax350013.CallableProblems (VecInst VecInst.mk VecInst.N VecInst.U VecInst.a VecInst.X)

/- The list lies below the free pointer, and its entries are bounded by `U`. -/
export Lax350013.CallableProblems (VecInst.Pre VecInst.Pre.mk VecInst.Pre.N_pos VecInst.Pre.U_pos VecInst.Pre.len VecInst.Pre.seg VecInst.Pre.le VecInst.Pre.below)

/-- **Convolution-3SUM**: c3(N, U, x, fr) returns 1 if `x_i + x_j = x_{i+j}` for some `i`, `j`, and
0 if not. -/
noncomputable def c3Task : Task where
  Inst := VecInst
  size x := x.N
  bound x := x.U
  args x := [x.N, x.U, x.a]
  Pre := VecInst.Pre
  Post x μ fr r μ' := r = flag (Convolution3SUM (vecOf x.N x.X)) ∧ Kept μ μ' fr

/-- **3SUM**: s3(n, U, x, fr) returns 1 if three of the numbers, at different positions, sum to 0,
and 0 if not. -/
noncomputable def s3Task : Task where
  Inst := VecInst
  size x := x.N
  bound x := x.U
  args x := [x.N, x.U, x.a]
  Pre := VecInst.Pre
  Post x μ fr r μ' := r = flag (ThreeSum (vecOf x.N x.X)) ∧ Kept μ μ' fr

/- Two `n × n` matrices in the memory, and the place for a third. -/
export Lax350013.CallableProblems (MatInst MatInst.mk MatInst.n MatInst.U MatInst.a MatInst.b MatInst.c MatInst.A MatInst.B)

/- The two matrices and the place for the product lie below the free pointer; the place for the
product does not meet the two matrices. -/
export Lax350013.CallableProblems (MatInst.Pre MatInst.Pre.mk MatInst.Pre.n_pos MatInst.Pre.U_pos MatInst.Pre.lenA MatInst.Pre.lenB MatInst.Pre.segA MatInst.Pre.segB MatInst.Pre.leA MatInst.Pre.leB MatInst.Pre.belowA MatInst.Pre.belowB MatInst.Pre.belowC MatInst.Pre.apartA MatInst.Pre.apartB)

/-- **The (min,+)-product**: mp(n, U, a, b, c, fr) writes the product of the matrices at `a` and `b`
to `c`. -/
def mpTask : Task where
  Inst := MatInst
  size x := x.n
  bound x := x.U
  args x := [x.n, x.U, x.a, x.b, x.c]
  Pre := MatInst.Pre
  Post x μ fr _ μ' := Seg μ' x.c (minPlusList x.n x.A x.B) ∧ KeptBut μ μ' fr x.c (x.n * x.n)

/- A directed graph in the memory: adjacency matrix and weights, and the place for the `2n²` cells
of the answer. -/
export Lax350013.CallableProblems (GraphInst GraphInst.mk GraphInst.n GraphInst.U GraphInst.adj GraphInst.w GraphInst.out GraphInst.ADJ GraphInst.W)

/- The graph and the place for the answer lie below the free pointer; the graph has no negative
cycle. -/
export Lax350013.CallableProblems (GraphInst.Pre GraphInst.Pre.mk GraphInst.Pre.n_pos GraphInst.Pre.U_pos GraphInst.Pre.lenADJ GraphInst.Pre.lenW GraphInst.Pre.segADJ GraphInst.Pre.segW GraphInst.Pre.zeroOne GraphInst.Pre.leW GraphInst.Pre.belowADJ GraphInst.Pre.belowW GraphInst.Pre.belowOut GraphInst.Pre.apartADJ GraphInst.Pre.apartW GraphInst.Pre.noNegativeCycle)

/-- **APSP**: ap(n, U, adj, w, out, fr) writes two cells for each pair `(i, j)`, at
`out + 2 (i n + j)`: 1 and the distance from `i` to `j` if `j` can be reached from `i`, and 0 in the
first cell if not. -/
def apTask : Task where
  Inst := GraphInst
  size x := x.n
  bound x := x.U
  args x := [x.n, x.U, x.adj, x.w, x.out]
  Pre := GraphInst.Pre
  Post x μ fr _ μ' :=
    (∃ dist : Fin x.n → Fin x.n → WithTop ℤ, IsDistanceMatrix (graphOf x.n x.ADJ x.W) dist ∧
    ∀ i j : Fin x.n,
      (dist i j = ⊤ → μ' (x.out + 2 * (i.val * x.n + j.val)) = 0) ∧
      ∀ z : ℤ, dist i j = (z : WithTop ℤ) →
        μ' (x.out + 2 * (i.val * x.n + j.val)) = 1 ∧
          μ' (x.out + 2 * (i.val * x.n + j.val) + 1) = z) ∧
    KeptBut μ μ' fr x.out (2 * (x.n * x.n))

/-! ## The thin matrix product and the lopsided triangle problems -/

/- Matrices `X` (`N × D`) and `Y` (`D × N`), row by row, `w` wanted positions (rows in `WI`,
columns in `WJ`), and the place for `w` answers. -/
export Lax350013.CallableProblems (ThinInst ThinInst.mk ThinInst.N ThinInst.D ThinInst.w ThinInst.U ThinInst.x ThinInst.y ThinInst.wi ThinInst.wj ThinInst.out ThinInst.X ThinInst.Y ThinInst.WI ThinInst.WJ)

/- Everything lies below the free pointer, the entries are bounded by `U`, the positions are
distinct positions of an `N × N` matrix, and the place for the answers meets none of the inputs. -/
export Lax350013.CallableProblems (ThinInst.Pre ThinInst.Pre.mk ThinInst.Pre.N_pos ThinInst.Pre.D_pos ThinInst.Pre.U_pos ThinInst.Pre.lenX ThinInst.Pre.lenY ThinInst.Pre.lenWI ThinInst.Pre.lenWJ ThinInst.Pre.segX ThinInst.Pre.segY ThinInst.Pre.segWI ThinInst.Pre.segWJ ThinInst.Pre.leX ThinInst.Pre.leY ThinInst.Pre.ltWI ThinInst.Pre.ltWJ ThinInst.Pre.nodup ThinInst.Pre.belowX ThinInst.Pre.belowY ThinInst.Pre.belowWI ThinInst.Pre.belowWJ ThinInst.Pre.belowOut ThinInst.Pre.apartX ThinInst.Pre.apartY ThinInst.Pre.apartWI ThinInst.Pre.apartWJ)

/-! The ten arguments of a procedure for one of these tasks, as local variables. -/

namespace ThinArg

/-- N. -/
abbrev Rows : ℕ := 0
/-- D. -/
abbrev Cols : ℕ := 1
/-- The number w of wanted positions. -/
abbrev Wanted : ℕ := 2
/-- The bound U on the entries. -/
abbrev Bound : ℕ := 3
/-- The address of X. -/
abbrev AdrX : ℕ := 4
/-- The address of Y. -/
abbrev AdrY : ℕ := 5
/-- The address of the rows of the wanted positions. -/
abbrev AdrWI : ℕ := 6
/-- The address of their columns. -/
abbrev AdrWJ : ℕ := 7
/-- The address of the output. -/
abbrev AdrOut : ℕ := 8
/-- The free pointer. -/
abbrev Free : ℕ := 9

end ThinArg

/-- The entries of both matrices are 0 or 1. -/
def ThinInst.ZeroOne (x : ThinInst) : Prop := (∀ v ∈ x.X, v = 0 ∨ v = 1) ∧ ∀ v ∈ x.Y, v = 0 ∨ v = 1

/-- The entry `(XY)[I, J]`. -/
def thinEntry (N D : ℕ) (X Y : List ℤ) (I J : ℕ) : ℤ :=
  ((List.range D).map fun k => X.getD (I * D + k) 0 * Y.getD (k * N + J) 0).sum

/-- The wanted entries, in the order of the positions. -/
def thinOut (N D : ℕ) (X Y : List ℤ) (WI WJ : List ℕ) : List ℤ :=
  (WI.zip WJ).map fun q => thinEntry N D X Y q.1 q.2

/-- **The wanted entries of a thin matrix product** (Theorem 5, Corollary 26):
`thin(N, D, w, U, x, y, wi, wj, out, fr)`. -/
def thinTask : TaskN where
  Inst := ThinInst
  pars x := [x.N, x.D, x.w, x.U]
  args x := [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out]
  Pre := ThinInst.Pre
  Post x μ fr _ μ' := Seg μ' x.out (thinOut x.N x.D x.X x.Y x.WI x.WJ) ∧ KeptBut μ μ' fr x.out x.w

/-- **#Lop-AE-SparseTri** (Definition 14), the graph given by its two biadjacency matrices: the same
call with `U = 1` on matrices of zeros and ones; the answers are the numbers of common
neighbours. -/
def lopCountTask : TaskN where
  Inst := ThinInst
  pars x := [x.N, x.D, x.w]
  args x := [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out]
  Pre x μ fr := x.Pre μ fr ∧ x.ZeroOne ∧ x.U = 1
  Post x μ fr _ μ' := Seg μ' x.out (thinOut x.N x.D x.X x.Y x.WI x.WJ) ∧ KeptBut μ μ' fr x.out x.w

/-- **Lop-AE-SparseTri** (Definition 13): the answer is 1 if the pair has a common neighbour and 0
if not. -/
def lopDetectTask : TaskN where
  Inst := ThinInst
  pars x := [x.N, x.D, x.w]
  args x := [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out]
  Pre x μ fr := x.Pre μ fr ∧ x.ZeroOne ∧ x.U = 1
  Post x μ fr _ μ' :=
    Seg μ' x.out ((thinOut x.N x.D x.X x.Y x.WI x.WJ).map fun v => if v = 0 then 0 else 1) ∧
      KeptBut μ μ' fr x.out x.w

/-- "The thin matrix product is solved in time `T N D w' u`", where `w'` is an upper bound on the
number `w` of wanted positions and `u` one on the bound `U`. -/
def ThinSolvedIn (T : ℕ → ℕ → ℕ → ℝ → ℝ) : Prop :=
  ∃ (P : Program) (p : ℕ) (Tn : List ℕ → ℕ) (need : List ℕ → Need), PolyNeedN need ∧
    SolvesN thinTask P p Tn need ∧
    ∀ (N D w w' U : ℕ) (u : ℝ), 1 ≤ N → 1 ≤ D → 1 ≤ U → w ≤ w' → (U : ℝ) ≤ u →
      (Tn [N, D, w, U] : ℝ) ≤ T N D w' u

/-- "The task (one of the two lopsided triangle problems) is solved in time `T n D w'`", where `w'`
is an upper bound on the number `w` of query pairs. -/
def LopSolvedIn (task : TaskN) (T : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∃ (P : Program) (p : ℕ) (Tn : List ℕ → ℕ) (need : List ℕ → Need), PolyNeedN need ∧
    SolvesN task P p Tn need ∧
    ∀ (n D w w' : ℕ), 1 ≤ n → 1 ≤ D → w ≤ w' → (Tn [n, D, w] : ℝ) ≤ T n D w'

end Light
end

end Lax350013Proofs
