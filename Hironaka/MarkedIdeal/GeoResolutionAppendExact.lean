/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.MarkedIdeals.MarkedIdeal
open Hironaka Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
noncomputable section
variable {n : ℕ} {X Y Z : CMfd.{u} n}
variable (𝔪 : MarkedIdeal n X)
theorem IsGeoResolution.append {T : BlowupTower X Y} {S : BlowupTower Y Z}
    (hT : IsGeoTestTower 𝔪 T) (hS : IsGeoResolution (geoTransformAlong 𝔪 T) S) :
    IsGeoResolution 𝔪 (T.append S) :=
  ⟨(isGeoTestTower_append_iff 𝔪 T S).mpr ⟨hT, hS.1⟩, by rw [geoTransformAlong_append]; exact hS.2⟩

end
end Hironaka.MarkedIdeals.MarkedIdeal
