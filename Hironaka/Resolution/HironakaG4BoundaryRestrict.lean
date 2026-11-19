import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.HomogenizedGlueingTower

/-! Geometric boundary fields commute with open restriction independently of ideals. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4BoundaryRestrict
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupStrictSubmanifold HomogenizedGlueingTower MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealRestrictOpen MarkedIdealBiholomorphism

variable {n : ℕ} {X : CMfd.{u} n}

/-- The boundary of the restricted transform is the restricted boundary, without
assuming that either marked ideal is well formed or that the tower tests it. -/
theorem boundary_geoTransformAlong_restrict (D : MarkedIdeal n X) (U : Opens X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) D) (restrict U T)).E =
        (geoTransformAlong D T).E.map ((Subtype.val : openPreimage T U → Y) ⁻¹' ·)
  | _, .refl => rfl
  | _, .step T C π hπ => by
    rw [show (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) D)
      (restrict U (.step T C π hπ))).E =
        ((geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) D) (restrict U T)).E.map
          (geoStrictTransform _ ((Subtype.val : openPreimage T U → _) ⁻¹' C))) ++ [_] from rfl]
    rw [boundary_geoTransformAlong_restrict D U T]
    simp only [geoTransformAlong, MarkedIdeal.geoTransform, List.map_append, List.map_map,
      List.map_cons, List.map_nil]
    congr 1
    apply List.map_congr_left
    intro H _
    exact geoStrictTransform_restrict (openPreimage T U) _ H

end
end Hironaka.HironakaG4BoundaryRestrict
