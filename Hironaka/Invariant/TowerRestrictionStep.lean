/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupTowerTransforms

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.TowerPreimageCompact
open Hironaka BlowupSequences BlowupTowers BlowupTowerTransforms
noncomputable section
variable {n : ℕ} {X : CMfd.{u} n}

/-- **Restriction of a one-step extension**: the restriction to `U` of `T` followed by a blowup is the restriction of `T`
followed by a blowup (along the trace of the centre); so restricted growing sequences are growing. -/
theorem exists_restrict_step (U : Opens X) {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) :
    ∃ (π' : openPreimage (.step T C π hπ) U → openPreimage T U)
      (hπ' : IsBlowupAlong n ((Subtype.val : openPreimage T U → Y) ⁻¹' C) π'),
      restrict U (.step T C π hπ) = .step (restrict U T) ((Subtype.val : openPreimage T U → Y) ⁻¹' C) π' hπ' :=
  ⟨_, _, rfl⟩

end
end Hironaka.TowerPreimageCompact
