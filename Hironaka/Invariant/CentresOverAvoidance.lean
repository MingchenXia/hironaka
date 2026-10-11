/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.RestrictEmptyTower

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.RestrictEmptyTower
open Hironaka BlowupSequences BlowupTowers
noncomputable section
variable {n : ℕ} {X : CMfd.{u} n}
/-- **Centres over a set disjoint from the open set avoid it.** -/
theorem centresAvoid_of_centresOver (U : Opens X) {F : Set X} (hUF : Disjoint (U : Set X) F) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), CentresOver F T → CentresAvoid U T
  | _, .refl, _ => trivial
  | _, .step T _ _ _, h =>
    ⟨centresAvoid_of_centresOver U hUF T h.1,
      Set.disjoint_left.mpr fun _ hyC hyU => Set.disjoint_left.mp hUF hyU (h.2 hyC)⟩

end
end Hironaka.RestrictEmptyTower
