/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupTowerTransforms

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.BlowupTowerTransforms
open Hironaka BlowupTowers
variable {n : ℕ} {X : CMfd.{u} n}

theorem length_restrict (U : Opens X) : {Y : CMfd.{u} n} → (T : BlowupTower X Y) →
    (restrict U T).length = T.length
  | _, .refl => rfl
  | _, .step T _ _ _ => congrArg (· + 1) (length_restrict U T)

end Hironaka.BlowupTowerTransforms
