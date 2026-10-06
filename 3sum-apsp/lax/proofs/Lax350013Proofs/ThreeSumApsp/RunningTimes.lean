/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Modified for the independent Lax packaging by Édouard Bonnet, 2026.
Derived from 3sum-apsp/ThreeSumApsp/RunningTimes.lean at upstream commit e1a4e6508154ea59f030480661590a9fe3018011.
Changes: Lax module/namespace layout, separated concepts and proofs, archive
annotations, and compatibility with the archive Lean/mathlib environment.
See NOTICE and README.md in the submission root for provenance and scope.
-/

import Lax350013Proofs.ThreeSumApsp.RunningTimes.FromClaims
import Lax350013Proofs.ThreeSumApsp.RunningTimes.FromClaims.Bounds
import Lax350013Proofs.ThreeSumApsp.RunningTimes.Sec1.Theorems1_4
import Lax350013Proofs.ThreeSumApsp.RunningTimes.Sec2.Theorem5
import Lax350013Proofs.ThreeSumApsp.RunningTimes.Sec3.Corollary15_16
import Lax350013Proofs.ThreeSumApsp.RunningTimes.Sec3.Corollary15_16.Layout
import Lax350013Proofs.ThreeSumApsp.RunningTimes.Sec3.Theorem19
import Lax350013Proofs.ThreeSumApsp.RunningTimes.Sec3.Theorem19.GraphsLayout
import Lax350013Proofs.ThreeSumApsp.RunningTimes.Sec3.Theorem19.Layout
import Lax350013Proofs.ThreeSumApsp.RunningTimes.Sec3.Theorem22
import Lax350013Proofs.ThreeSumApsp.RunningTimes.Sec3.Theorem22.ApspLayout
import Lax350013Proofs.ThreeSumApsp.RunningTimes.Sec3.Theorem22.MinPlusLayout
import Lax350013Proofs.ThreeSumApsp.RunningTimes.Sec3.Theorem22.ThreeSumLayout
import Lax350013Proofs.ThreeSumApsp.RunningTimes.Sec3.Theorem22.ThreeSumPolylog
import Lax350013Proofs.ThreeSumApsp.RunningTimes.Sec4.Corollary26
import Lax350013Proofs.ThreeSumApsp.RunningTimes.Sec4.Corollary31_32
import Lax350013Proofs.ThreeSumApsp.RunningTimes.Sec4.Corollary31_32.Arithmetic
import Lax350013Proofs.ThreeSumApsp.RunningTimes.Sec4.Theorem24_25
import Lax350013Proofs.ThreeSumApsp.RunningTimes.Sec4.Theorem30
import Lax350013Proofs.ThreeSumApsp.RunningTimes.Sec5.Corollary39
import Lax350013Proofs.ThreeSumApsp.RunningTimes.Sec5.Corollary39.MinMaxWeight
import Lax350013Proofs.ThreeSumApsp.RunningTimes.Sec5.Corollary39.ZeroWeight
import Lax350013Proofs.ThreeSumApsp.RunningTimes.Sec5.Corollary39.ZeroWeightLayout
import Lax350013Proofs.ThreeSumApsp.RunningTimes.Sec5.Corollary40
import Lax350013Proofs.ThreeSumApsp.RunningTimes.Sec5.Corollary40.ColumnTimes
import Lax350013Proofs.ThreeSumApsp.RunningTimes.Sec5.Corollary40.MvHintedTimes
import Lax350013Proofs.ThreeSumApsp.RunningTimes.Sec5.Corollary40.ToMachine
import Lax350013Proofs.ThreeSumApsp.RunningTimes.Sec5.Corollary40.UMvHintedTimes
import Lax350013Proofs.ThreeSumApsp.RunningTimes.Sec5.Corollary40.VHintedTimes

namespace Lax350013Proofs

/-!
# The running times on the word RAM

All files of `ThreeSumApsp/RunningTimes/`.
-/

end Lax350013Proofs
