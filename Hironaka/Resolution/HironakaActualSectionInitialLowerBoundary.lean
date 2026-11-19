import Hironaka.Resolution.HironakaActualSectionInitialBoundaryMask

/-! Exact original positive-level lowerMarkedM initial records under the actual zero section. Induction on actual lower values and chronological history remains separate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualSectionInitialLowerBoundary
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers
  HironakaActualOpenZeroSectionDifferentials HironakaActualSectionInitialBoundaryRegime
  HironakaActualSectionMemberRestriction HironakaActualSectionInitialBoundaryMask
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionOrderedChoiceImageTrace
  InvDomainMemberRestriction HomogenizedIdealAlong
variable {n : ℕ} {U : TopologicalSpace.Opens (ComplexModel n)}

theorem markedPullback_section_bar_memberRestrict
    (A : Set U) (hA : IsClosedSubmanifold n A) (E E₀ : List (Set U))
    (J : GermIdeal (n+1) (productOpen U)) (hJ : J.IsCoherent) (d : ℕ) (x : U) :
    let M : MarkedIdeal (n+1) (CMfd.of (n := n+1) (productOpen U)):=
      ⟨liftedCarrier A,E.map (projection U ⁻¹' ·),J,d⟩
    let B : MarkedIdeal n (CMfd.of (n := n) U):=⟨A,E,GermIdeal.pullback (m := n) (zeroSection U) J,d⟩
    markedPullback (m := n) (zeroSection U)
      (memberRestrict (StepOneValue.barMarked M)
        (membersThrough (StepOneValue.barMarked M).E (E₀.map (projection U ⁻¹' ·)) (zeroSection U x))) =
      memberRestrict (StepOneValue.barMarked B) (membersThrough (StepOneValue.barMarked B).E E₀ x) := by
  let M : MarkedIdeal (n+1) (CMfd.of (n := n+1) (productOpen U)):=
    ⟨liftedCarrier A,E.map (projection U ⁻¹' ·),J,d⟩
  let B : MarkedIdeal n (CMfd.of (n := n) U):=⟨A,E,GermIdeal.pullback (m := n) (zeroSection U) J,d⟩
  have hc : (StepOneValue.barMarked M).ideal.IsCoherent :=
    isCoherent_coeffMarkedAlong (isCoherent_homMarkedAlong (𝔪 := M) hJ (liftedCarrier_closed_submanifold hA))
      (liftedCarrier_closed_submanifold hA)
  have hNative : (⟨A,E,GermIdeal.pullback (m := n) (zeroSection U) (StepOneValue.barMarked M).ideal,
      (StepOneValue.barMarked M).d⟩ : MarkedIdeal n U)=StepOneValue.barMarked B := by
    apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    · rfl
    · rfl
    · exact bar_ideal_section A hA E J hJ d
    · rfl
  have h := markedPullback_section_memberRestrict_membersThrough A hA E E₀
    (StepOneValue.barMarked M).ideal hc (StepOneValue.barMarked M).d x
  rw [hNative] at h
  exact h

def maskASection (A : Set U) (hA : IsClosedSubmanifold n A)
    (E : List (Set U)) (J : GermIdeal (n+1) (productOpen U)) (hJ : J.IsCoherent) (d : ℕ) (x : U) :
    StepOneValue.maskA (X := CMfd.of (n := n) U)
      (⟨A,E,GermIdeal.pullback (m := n) (zeroSection U) J,d⟩ : MarkedIdeal n U) .refl x →
    StepOneValue.maskA (X := CMfd.of (n := n+1) (productOpen U))
      (⟨liftedCarrier A,E.map (projection U ⁻¹' ·),J,d⟩ : MarkedIdeal (n+1) (productOpen U)) .refl (zeroSection U x) :=
  fun y => ⟨zeroSection U y.val,by
    have hmask := baseMask_maskA A hA E J hJ d x
    have hy : y.val∈HironakaActualMaskSectionRepresentative.baseMask U
        (StepOneValue.maskA (X := CMfd.of (n := n+1) (productOpen U))
          (⟨liftedCarrier A,E.map (projection U ⁻¹' ·),J,d⟩ : MarkedIdeal (n+1) (productOpen U)) .refl (zeroSection U x)) := by
      rw [hmask]
      exact y.property
    exact hy⟩

theorem maskASection_contMDiff (A : Set U) (hA : IsClosedSubmanifold n A)
    (E : List (Set U)) (J : GermIdeal (n+1) (productOpen U)) (hJ : J.IsCoherent) (d : ℕ) (x : U) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (n+1)) ∞ (maskASection A hA E J hJ d x) := by
  apply (ContMDiff.subtypeVal_comp_iff _ _).mp
  exact (zeroSection_contMDiff U).comp contMDiff_subtype_val

theorem markedPullback_section_lowerMarkedM_succ_refl
    (A : Set U) (hA : IsClosedSubmanifold n A) (E : List (Set U))
    (J : GermIdeal (n+1) (productOpen U)) (hJ : J.IsCoherent) (d s : ℕ) (x : U) :
    let M : MarkedIdeal (n+1) (CMfd.of (n := n+1) (productOpen U)):=
      ⟨liftedCarrier A,E.map (projection U ⁻¹' ·),J,d⟩
    let B : MarkedIdeal n (CMfd.of (n := n) U):=⟨A,E,GermIdeal.pullback (m := n) (zeroSection U) J,d⟩
    markedPullback (m := n) (maskASection A hA E J hJ d x)
      (StepOneValueMasked.lowerMarkedM M (s+1) .refl (zeroSection U x)) =
      StepOneValueMasked.lowerMarkedM B (s+1) .refl x := by
  let M : MarkedIdeal (n+1) (CMfd.of (n := n+1) (productOpen U)):=
    ⟨liftedCarrier A,E.map (projection U ⁻¹' ·),J,d⟩
  let B : MarkedIdeal n (CMfd.of (n := n) U):=⟨A,E,GermIdeal.pullback (m := n) (zeroSection U) J,d⟩
  let OS := StepOneValue.maskA M .refl (zeroSection U x)
  let OB := StepOneValue.maskA B .refl x
  let σ := maskASection A hA E J hJ d x
  let MS := memberRestrict (StepOneValue.barMarked M)
    (membersThrough (StepOneValue.barMarked M).E M.E (zeroSection U x))
  let MB := memberRestrict (StepOneValue.barMarked B)
    (membersThrough (StepOneValue.barMarked B).E B.E x)
  have hcBar : (StepOneValue.barMarked M).ideal.IsCoherent :=
    isCoherent_coeffMarkedAlong (isCoherent_homMarkedAlong (𝔪 := M) hJ (liftedCarrier_closed_submanifold hA))
      (liftedCarrier_closed_submanifold hA)
  have hcMS : MS.ideal.IsCoherent :=
    isCoherent_coeffMarkedAlong hcBar (liftedCarrier_closed_submanifold hA)
  have hs := maskASection_contMDiff A hA E J hJ d x
  have hDict : markedPullback (m := n) (zeroSection U) MS=MB :=
    markedPullback_section_bar_memberRestrict A hA E E J hJ d x
  have hOrigM : StepOneValue.origMembers M .refl=M.E := by
    change M.E.take M.E.length=M.E
    exact List.take_length
  have hOrigB : StepOneValue.origMembers B .refl=B.E := by
    change B.E.take B.E.length=B.E
    exact List.take_length
  change markedPullback (m := n) σ
    (StepOneValueMasked.lowerMarkedM M (s+1) .refl (zeroSection U x)) =
      StepOneValueMasked.lowerMarkedM B (s+1) .refl x
  simp only [StepOneValueMasked.lowerMarkedM_succ,StepOneValue.lowerMarked,
    MarkedIdeal.geoTransformAlong,hOrigM,hOrigB]
  change markedPullback (m := n) σ (markedPullback (m := n+1) (Subtype.val : OS→productOpen U) MS) =
    markedPullback (m := n) (Subtype.val : OB→U) MB
  rw [←whole_markedPullback_comp contMDiff_subtype_val hs MS hcMS]
  have hsq : (Subtype.val : OS→productOpen U) ∘ σ=zeroSection U ∘ (Subtype.val : OB→U) := rfl
  rw [hsq,whole_markedPullback_comp (zeroSection_contMDiff U) contMDiff_subtype_val MS hcMS,hDict]

end
end Hironaka.HironakaActualSectionInitialLowerBoundary

