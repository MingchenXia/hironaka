import Hironaka.Resolution.HironakaG3EmptyAwareFullBoundary
import Hironaka.Resolution.HironakaG4BoundaryRestrict
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3BoundaryRestrictInitialList
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaG3EmptyAwareFullBoundary HironakaG4BoundaryRestrict MarkedIdealBiholomorphism

theorem boundary_eq_of_initial_eq {n : ℕ} {X Y : CMfd.{0} n}
    (A B : MarkedIdeal n X) (hE : A.E = B.E) (T : BlowupTower X Y) :
    (geoTransformAlong A T).E = (geoTransformAlong B T).E := by
  rw [boundary_decomp,boundary_decomp,hE]

theorem boundary_restrict_of_initial_eq {n : ℕ} {X Y : CMfd.{0} n}
    (A : MarkedIdeal n X) (U : Opens X) (B : MarkedIdeal n (CMfd.of (n := n) U))
    (hE : B.E = A.E.map ((Subtype.val : U → X) ⁻¹' ·)) (T : BlowupTower X Y) :
    (geoTransformAlong B (restrict U T)).E =
      (geoTransformAlong A T).E.map ((Subtype.val : openPreimage T U → Y) ⁻¹' ·) := by
  rw [boundary_eq_of_initial_eq B (MarkedIdeal.pullback (Subtype.val : U → X) A) hE]
  exact boundary_geoTransformAlong_restrict A U T
end
end Hironaka.HironakaG3BoundaryRestrictInitialList
