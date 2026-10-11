/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.StepOneValue

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology Manifold
universe u
namespace Hironaka.StepOneValue
open Hironaka BlowupSequences BlowupTowers MarkedIdeals
variable {n : ℕ} {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X)

/-- The divisor of `J̄` is that of `𝔍`. -/
theorem barMarked_E : (barMarked 𝔍).E = 𝔍.E := rfl

/-- `J̄` has the submanifold of `𝔍`. -/
theorem barMarked_N : (barMarked 𝔍).N = 𝔍.N := rfl

end Hironaka.StepOneValue
