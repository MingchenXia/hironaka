import Hironaka.Resolution.HironakaActualSectionInitialBoundaryRegime

/-! The original coefficient record and positive-level member restriction commute with the actual zero section, with the original ordered filter. This is not an all-index or historical value comparison. -/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualSectionMemberRestriction
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences MarkedIdeals
  HironakaActualOpenZeroSectionDifferentials HironakaRelativeNormalIdeal
  HironakaActualCentreJointJets HironakaActualIntrinsicStableAmbientIso
  IdealWeightPowers RelativePrincipalizationSpan GermIdealPullbackCalculus
  HomogenizedIdealAlong DerivativeIdealAlong DerivativeIdealAlongCoherent CoefficientIdeal
  HironakaSmoothSubmersionCoefficientIdeals InvDomainMemberRestriction InvDomainRebase
  BlowupTowers GermIdealOrder HomogenizedEquivalence HomogenizedGlueing GiraudAlong
variable {n : ℕ} {U : TopologicalSpace.Opens (ComplexModel n)}

private theorem projection_section (x : U) : projection U (zeroSection U x)=x := by
  apply Subtype.ext
  exact tangentProjection_tangentInclusion n 1 x

private theorem whole_boundary_section (E : List (Set U)) :
    (E.map (projection U ⁻¹' ·)).map (zeroSection U ⁻¹' ·)=E := by
  rw [List.map_map]
  have hf : (fun H : Set U => zeroSection U ⁻¹' (projection U ⁻¹' H))=id := by
    funext H
    ext y
    simp only [Set.mem_preimage,projection_section,id_eq]
  change List.map (fun H => zeroSection U ⁻¹' (projection U ⁻¹' H)) E=E
  rw [hf,List.map_id]

private theorem mem_of_projection_preimage_mem_map {H : Set U} {E : List (Set U)}
    (h : projection U ⁻¹' H ∈ E.map (projection U ⁻¹' ·)) : H ∈ E := by
  obtain ⟨H₀,hH₀,he⟩ := List.mem_map.mp h
  have hEq : H₀=H := by
    ext y
    have hy := congrArg (fun A : Set (productOpen U) => zeroSection U y ∈ A) he
    simpa only [Set.mem_preimage,projection_section] using Iff.of_eq hy
  exact hEq ▸ hH₀

theorem markedPullback_section_coeffMarkedAlong (A : Set U) (hA : IsClosedSubmanifold n A)
    (E : List (Set U)) (J : GermIdeal (n+1) (productOpen U)) (hJ : J.IsCoherent) (d : ℕ) :
    let M : MarkedIdeal (n+1) (productOpen U):=⟨liftedCarrier A,E.map (projection U ⁻¹' ·),J,d⟩
    let B : MarkedIdeal n U:=⟨A,E,GermIdeal.pullback (m := n) (zeroSection U) J,d⟩
    markedPullback (m := n) (zeroSection U) (coeffMarkedAlong M)=coeffMarkedAlong B := by
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · ext y
    change (projection U (zeroSection U y)∈A ∧ _=0) ↔ y∈A
    simp only [projection_section]
    simp [zeroSection]
  · exact whole_boundary_section E
  · change GermIdeal.pullback (m := n) (zeroSection U)
      (finSumIdeal (fun i => idealPow (iterDerivIdealAlong (liftedCarrier A) J i)
        (sumExp (fun j => d-j) d i)) d)=
      finSumIdeal (fun i => idealPow (iterDerivIdealAlong A (GermIdeal.pullback (m := n) (zeroSection U) J) i)
        (sumExp (fun j => d-j) d i)) d
    rw [HironakaActualNonregularCoefficientNaturality.pullback_finSumIdeal (zeroSection_contMDiff U) _ _
      (fun _ _ {_ _} hg => holomorphicAt_of_mem_idealPow hg)]
    apply finSumIdeal_congr
    intro i _
    rw [HironakaActualNonregularCoefficientNaturality.pullback_idealPow (zeroSection_contMDiff U)
      (fun {_ _} hg => holomorphicAt_of_mem_iterDerivIdealAlong
        (N := liftedCarrier A) (fun _ _ hj => GermIdeal.IsCoherent.holomorphicAt_mem hJ hj) i _ _ hg),
      zero_section_iterDerivIdealAlong U hA J hJ i]
  · rfl

theorem markedPullback_section_memberRestrict_membersThrough
    (A : Set U) (hA : IsClosedSubmanifold n A) (E E₀ : List (Set U))
    (J : GermIdeal (n+1) (productOpen U)) (hJ : J.IsCoherent) (d : ℕ) (x : U) :
    let M : MarkedIdeal (n+1) (productOpen U):=⟨liftedCarrier A,E.map (projection U ⁻¹' ·),J,d⟩
    let B : MarkedIdeal n U:=⟨A,E,GermIdeal.pullback (m := n) (zeroSection U) J,d⟩
    markedPullback (m := n) (zeroSection U)
      (memberRestrict M (membersThrough M.E (E₀.map (projection U ⁻¹' ·)) (zeroSection U x))) =
      memberRestrict B (membersThrough B.E E₀ x) := by
  classical
  let M : MarkedIdeal (n+1) (productOpen U):=⟨liftedCarrier A,E.map (projection U ⁻¹' ·),J,d⟩
  let B : MarkedIdeal n U:=⟨A,E,GermIdeal.pullback (m := n) (zeroSection U) J,d⟩
  have hCoeff := markedPullback_section_coeffMarkedAlong A hA E J hJ d
  have hI := congrArg MarkedIdeal.ideal hCoeff
  have hD := congrArg MarkedIdeal.d hCoeff
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · change (zeroSection U) ⁻¹' (memberRestrict M
        (membersThrough M.E (E₀.map (projection U ⁻¹' ·)) (zeroSection U x))).N =
      (memberRestrict B (membersThrough B.E E₀ x)).N
    rw [memberRestrict_membersThrough_N,memberRestrict_membersThrough_N]
    ext y
    change (zeroSection U y∈liftedCarrier A ∧
      ∀ H∈E.map (projection U ⁻¹' ·), H∈E₀.map (projection U ⁻¹' ·) →
        zeroSection U x∈H → zeroSection U y∈H) ↔
      (y∈A ∧ ∀ H∈E, H∈E₀ → x∈H → y∈H)
    have hN : zeroSection U y∈liftedCarrier A ↔ y∈A := by
      change (projection U (zeroSection U y)∈A ∧ _=0) ↔ y∈A
      simp only [projection_section]
      simp [zeroSection]
    rw [hN]
    apply and_congr_right
    intro _
    constructor
    · intro hw H hH hH₀ hxH
      have hz := hw (projection U ⁻¹' H) (List.mem_map_of_mem hH)
        (List.mem_map_of_mem hH₀) (by simpa only [Set.mem_preimage,projection_section] using hxH)
      simpa only [Set.mem_preimage,projection_section] using hz
    · intro hw K hK hK₀ hxK
      obtain ⟨H,hH,rfl⟩ := List.mem_map.mp hK
      have hH₀ := mem_of_projection_preimage_mem_map hK₀
      have hz := hw H hH hH₀ (by simpa only [Set.mem_preimage,projection_section] using hxK)
      simpa only [Set.mem_preimage,projection_section] using hz
  · change ((memberRestrict M
        (membersThrough M.E (E₀.map (projection U ⁻¹' ·)) (zeroSection U x))).E).map (zeroSection U ⁻¹' ·) =
      (memberRestrict B (membersThrough B.E E₀ x)).E
    rw [memberRestrict_membersThrough_E,memberRestrict_membersThrough_E]
    change ((E.map (projection U ⁻¹' ·)).filter
        (fun H => decide ¬(H∈E₀.map (projection U ⁻¹' ·) ∧ zeroSection U x∈H))).map (zeroSection U ⁻¹' ·) =
      E.filter (fun H => decide ¬(H∈E₀ ∧ x∈H))
    rw [filter_map_members (y := x) (y' := zeroSection U x)
      (fun H _ => by simp only [Set.mem_preimage,projection_section])
      (fun _ _ _ h => mem_of_projection_preimage_mem_map h)]
    exact whole_boundary_section _
  · exact hI
  · exact hD

end
end Hironaka.HironakaActualSectionMemberRestriction

