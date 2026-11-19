import Hironaka.Resolution.HironakaG4FullBoundaryLocalizedTest
import Hironaka.Resolution.HironakaG4LocalizedSliceIdentity
import Hironaka.Resolution.HironakaG34LowerCleanupLift

/-! A full-boundary admissible centre gives a protected window directly. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4DirectLocalProtectedWindow
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupStrictSubmanifold HomogenizedGlueingTower MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealOpenBiholomorphism MarkedIdealRestrictOpen BlowupRestrictOpen RelativePrincipalizationSpan
  NormalCrossings NormalCrossingsInvariance HironakaG4BoundaryRestrict
  HironakaG4LocalizedSliceIdentity HironakaG34LowerCleanupLift

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- A locally well-formed test, the source slice identity, and actual centre
normal crossings with the transformed full boundary directly produce the
protected certificate. -/
theorem protected_window_of_local_test_and_full_centre
    (D : MarkedIdeal n X) (U : Opens X)
    (hD : (MarkedIdeal.pullback (Subtype.val : U → X) D).IsWellFormed)
    (T : BlowupTower X Y)
    (hTest : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) D) (restrict U T))
    (i : Fin D.E.length) (S : Set X)
    (hSlice : (Subtype.val : U → X) ⁻¹' S =
      (Subtype.val : U → X) ⁻¹' (D.N ∩ D.E.get i))
    {F : List (Set Y)} {C : Set Y} {x : Y} (hxU : T.proj x ∈ U)
    (hBoundary : (geoTransformAlong D T).E = strictAlong T (D.E.get i) :: F)
    (hC : HasNormalCrossings n C (geoTransformAlong D T).E) :
    ProtectedWindowAt (strictAlong T D.N) (strictAlong T S) F C x := by
  let V : Opens Y := openPreimage T U
  have hident := locally_presented_slice_identity_on_open_preimage D U hD T hTest i S hSlice
  have hwell := isWellFormed_geoTransformAlong hD (restrict U T) hTest
  have hE : (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) D) (restrict U T)).E =
      ((Subtype.val : V → Y) ⁻¹' (strictAlong T (D.E.get i))) ::
        F.map ((Subtype.val : V → Y) ⁻¹' ·) := by
    rw [boundary_geoTransformAlong_restrict,hBoundary]
    rfl
  have hN : (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) D) (restrict U T)).N =
      (Subtype.val : V → Y) ⁻¹' (strictAlong T D.N) := by
    rw [N_geoTransformAlong]
    exact strictAlong_restrict U T D.N
  refine ⟨V,hxU,(Subtype.val : V → Y) ⁻¹' (strictAlong T (D.E.get i)),?_,?_,?_,?_⟩
  · exact hident
  · simpa only [hE] using hwell.isSNCDivisor
  · simpa only [hE,hN] using hwell.isTransverse
  · have hh := hasNormalCrossings_preimage (pullsBackCoordinates_val V) hC
    simpa only [hBoundary,List.map_cons] using hh

end
end Hironaka.HironakaG4DirectLocalProtectedWindow
