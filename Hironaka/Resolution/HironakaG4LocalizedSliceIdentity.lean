import Hironaka.Resolution.HironakaG4LocalizedEnlargedTest
import Hironaka.Invariant.MemberInterTowerAlong

/-! Restricted testness preserves the selected slice over the window. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4LocalizedSliceIdentity
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupStrictSubmanifold HomogenizedGlueingTower MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism BoundaryCount

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- A restricted enlarged test gives the slice equality on the whole inverse
image of the base window, without requiring ambient enlarged testness. -/
theorem slice_identity_on_open_preimage
    (D : MarkedIdeal n X) (U : Opens X)
    (hD : (MarkedIdeal.pullback (Subtype.val : U → X) D).IsWellFormed)
    (T : BlowupTower X Y)
    (hTest : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) D) (restrict U T))
    (i : Fin D.E.length) :
    (Subtype.val : openPreimage T U → Y) ⁻¹' strictAlong T (D.N ∩ D.E.get i) =
      (Subtype.val : openPreimage T U → Y) ⁻¹' (strictAlong T D.N ∩ strictAlong T (D.E.get i)) := by
  let DU := MarkedIdeal.pullback (Subtype.val : U → X) D
  let iU : Fin DU.E.length := ⟨i.val, by simp [DU, MarkedIdeal.pullback]⟩
  have hi : DU.E.get iU = (Subtype.val : U → X) ⁻¹' D.E.get i := by
    simp [DU, MarkedIdeal.pullback, iU, List.get_eq_getElem]
  have hinter : memberInter DU.E {iU} = DU.E.get iU := by
    ext y
    simp [memberInter]
  have h := MemberInterTowerAlong.strictAlong_inter_memberInter DU (show DU.IsWellFormed from hD)
    ({iU} : Finset (Fin DU.E.length)) (restrict U T) hTest
  rw [hinter, hi, N_geoTransformAlong] at h
  simp only [Finset.mem_singleton, forall_eq] at h
  rw [hi] at h
  change strictAlong (restrict U T) ((Subtype.val : U → X) ⁻¹' D.N ∩
      (Subtype.val : U → X) ⁻¹' D.E.get i) =
        strictAlong (restrict U T) ((Subtype.val : U → X) ⁻¹' D.N) ∩
          strictAlong (restrict U T) ((Subtype.val : U → X) ⁻¹' D.E.get i) at h
  rw [← preimage_inter, strictAlong_restrict, strictAlong_restrict, strictAlong_restrict] at h
  simpa only [Set.preimage_inter] using h

/-- A slice given only by its equation on the original window has the same
intersection description on the inverse-image window after the actual test. -/
theorem locally_presented_slice_identity_on_open_preimage
    (D : MarkedIdeal n X) (U : Opens X)
    (hD : (MarkedIdeal.pullback (Subtype.val : U → X) D).IsWellFormed)
    (T : BlowupTower X Y)
    (hTest : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) D) (restrict U T))
    (i : Fin D.E.length) (S : Set X)
    (hSlice : (Subtype.val : U → X) ⁻¹' S =
      (Subtype.val : U → X) ⁻¹' (D.N ∩ D.E.get i)) :
    (Subtype.val : openPreimage T U → Y) ⁻¹' strictAlong T S =
      (Subtype.val : openPreimage T U → Y) ⁻¹' (strictAlong T D.N ∩ strictAlong T (D.E.get i)) := by
  calc
    _ = strictAlong (restrict U T) ((Subtype.val : U → X) ⁻¹' S) := (strictAlong_restrict U T S).symm
    _ = strictAlong (restrict U T) ((Subtype.val : U → X) ⁻¹' (D.N ∩ D.E.get i)) := by rw [hSlice]
    _ = (Subtype.val : openPreimage T U → Y) ⁻¹' strictAlong T (D.N ∩ D.E.get i) :=
      strictAlong_restrict U T _
    _ = _ := slice_identity_on_open_preimage D U hD T hTest i

end
end Hironaka.HironakaG4LocalizedSliceIdentity
