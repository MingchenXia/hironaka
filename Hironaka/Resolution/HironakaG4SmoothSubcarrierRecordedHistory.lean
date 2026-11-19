import Hironaka.Resolution.HironakaG4SmoothSubcarrierResidualStep
import Hironaka.Invariant.MemberInterTowerAlong

/-! The literal selected reduced subcarrier along ONE actual recorded history.
Source-first complete chapter: hironaka-g4-smooth-subcarrier-recorded-history.tex.
Only the selected-carrier native geometry test is required. -/

set_option autoImplicit false

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4SmoothSubcarrierRecordedHistory

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers HomogenizedGlueingTower MemberInterTowerAlong NormalCrossings
  HironakaG4SmoothSubcarrierResidualStep HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpActualChronologicalStrictStep RelativePrincipalizationSpan RestrictedIdealExtension
  InvertibleIdealQuotient IdealWeightPowers MarkedIdeals MarkedIdeals.MarkedIdeal

variable {n : ℕ} {X : CMfd.{u} n}


/-- ONE genuine selected-carrier geometry test internally tracks its WHOLE
reduced ideal and the smooth nested parent along the SAME actual finite tower. -/
theorem actual_recorded_smooth_subcarrier_dictionary (hn : 0 < n) {N Z : Set X}
    (hN : IsClosedSubmanifold n N) (hZ : IsClosedSubmanifold n Z) (hZN : Z ⊆ N) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsGeoTestTower (geometricTemplate Z []) T →
      let A := chronologicalMarked (originalRelativeMemberMarked N Z) T
      IsClosedSubmanifold n (strictAlong T N) ∧ IsClosedSubmanifold n (strictAlong T Z) ∧
        strictAlong T Z ⊆ strictAlong T N ∧ A.N=strictAlong T N ∧
        A.ideal=vanishingIdeal (n := n) (strictAlong T Z)
  | _,.refl,_hT => by
    refine ⟨hN,hZ,hZN,rfl,?_⟩
    change restrictOn n N (vanishingIdeal (n := n) Z)=vanishingIdeal (n := n) Z
    ext x g
    exact ⟨fun hg => MemberTraceIdealAlong.mem_vanishingIdeal_of_isInSpanOnAt hZN hg.1 hg.2,
      fun hg => ⟨hg.1,IsInSpanAt.restrict (isInSpanAt_self hg hg.1)⟩⟩
  | _,.step T C π hπ,hT => by
    obtain ⟨hNS,hZS,hSub,hChronoN,hIdeal⟩ :=
      actual_recorded_smooth_subcarrier_dictionary hn hN hZ hZN T hT.1
    have hZField : (geoTransformAlong (geometricTemplate Z []) T).N=strictAlong T Z :=
      N_geoTransformAlong (geometricTemplate Z []) T
    have hCZ : C ⊆ strictAlong T Z := by
      rw [←hZField]
      exact hT.2.subset_N
    have hCN : C ⊆ strictAlong T N := hCZ.trans hSub
    have hParent : IsClosedSubmanifold n (strictAlong (.step T C π hπ) N) :=
      BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hNS hCN
    have hStep := actual_smooth_subcarrier_relative_strict hn hNS hZS hSub hπ hCZ
    have hNextN : (chronologicalMarked (originalRelativeMemberMarked N Z) (.step T C π hπ)).N=
        strictAlong (.step T C π hπ) N := by
      calc
        _ = (geoTransformAlong (geometricTemplate N []) (.step T C π hπ)).N :=
          (chronologicalMarked_geometric_fields (originalRelativeMemberMarked N Z) (.step T C π hπ)).1
        _ = _ := N_geoTransformAlong (geometricTemplate N []) (.step T C π hπ)
    refine ⟨hParent,hStep.1,strictAlong_mono (.step T C π hπ) hZN,hNextN,?_⟩
    change nextRelativeStrict (chronologicalMarked (originalRelativeMemberMarked N Z) T).N
      (chronologicalMarked (originalRelativeMemberMarked N Z) T).ideal C π=
        vanishingIdeal (n := n) (BlowupStrictSubmanifold.geoStrictTransform π C (strictAlong T Z))
    rw [hChronoN,hIdeal]
    exact hStep.2

end
end Hironaka.HironakaG4SmoothSubcarrierRecordedHistory
