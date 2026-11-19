import Hironaka.Resolution.HironakaActualSectionInitialLowerBoundary

/-! Full boundary-kept initial contact records under the actual zero section. Actual lower-domain construction is separate from all-index value and history comparison. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualSectionContactKept
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers
  HironakaActualOpenZeroSectionDifferentials HironakaRelativeNormalIdeal
  HironakaActualCentreJointJets HironakaActualIntrinsicStableAmbientIso
  HironakaActualSectionInitialValues HironakaActualSectionInitialBoundaryRegime
  HironakaActualSectionMemberRestriction HironakaActualSectionInitialBoundaryMask
  HironakaActualSectionInitialLowerBoundary HironakaActualMaskSectionRepresentative
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionOrderedChoiceImageTrace
  HomogenizedIdealAlong ContactStageKept TangentDirectionAlong CodimOneSupportAlong
  HomogenizedGlueingTower CoefficientIdealRestriction RelativePrincipalizationSpan GermIdealOrder
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {U : TopologicalSpace.Opens (ComplexModel n)}

private theorem projection_section (x : U) : projection U (zeroSection U x)=x := by
  apply Subtype.ext
  exact tangentProjection_tangentInclusion n 1 x

private theorem global_contact_record (A : Set U) (hA : IsClosedSubmanifold n A)
    (E : List (Set U)) (J : GermIdeal (n+1) (productOpen U)) (hJ : J.IsCoherent) (d : ℕ)
    (u : productOpen U→ℂ) :
    let M : MarkedIdeal (n+1) (CMfd.of (n := n+1) (productOpen U)):=
      ⟨liftedCarrier A,E.map (projection U ⁻¹' ·),J,d⟩
    let B : MarkedIdeal n (CMfd.of (n := n) U):=⟨A,E,GermIdeal.pullback (m := n) (zeroSection U) J,d⟩
    markedPullback (m := n) (zeroSection U)
      (withN (coeffMarkedAlong (StepOneValue.barMarked M)) (M.N∩{z | u z=0})) =
      withN (coeffMarkedAlong (StepOneValue.barMarked B)) (B.N∩{y | u (zeroSection U y)=0}) := by
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
  have hCoeff := markedPullback_section_coeffMarkedAlong A hA E
    (StepOneValue.barMarked M).ideal hc (StepOneValue.barMarked M).d
  rw [hNative] at hCoeff
  have hE := congrArg (fun K : MarkedIdeal n U => K.E) hCoeff
  have hI := congrArg (fun K : MarkedIdeal n U => K.ideal) hCoeff
  have hD := congrArg (fun K : MarkedIdeal n U => K.d) hCoeff
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · ext y
    change ((projection U (zeroSection U y)∈A ∧ _=0) ∧ u (zeroSection U y)=0) ↔
      (y∈A ∧ u (zeroSection U y)=0)
    simp only [projection_section]
    simp [zeroSection]
  · exact hE
  · exact hI
  · exact hD

theorem markedPullback_section_contactMarkedKept_refl
    (A : Set U) (hA : IsClosedSubmanifold n A) (E : List (Set U))
    (J : GermIdeal (n+1) (productOpen U)) (hJ : J.IsCoherent) (d : ℕ)
    (u : productOpen U→ℂ) (O : TopologicalSpace.Opens (productOpen U)) :
    let M : MarkedIdeal (n+1) (CMfd.of (n := n+1) (productOpen U)):=
      ⟨liftedCarrier A,E.map (projection U ⁻¹' ·),J,d⟩
    let B : MarkedIdeal n (CMfd.of (n := n) U):=⟨A,E,GermIdeal.pullback (m := n) (zeroSection U) J,d⟩
    markedPullback (m := n) (sectionToMask U O) (contactMarkedKept M u .refl O)=
      contactMarkedKept B (u ∘ zeroSection U) .refl (baseMask U O) := by
  let M : MarkedIdeal (n+1) (CMfd.of (n := n+1) (productOpen U)):=
    ⟨liftedCarrier A,E.map (projection U ⁻¹' ·),J,d⟩
  let B : MarkedIdeal n (CMfd.of (n := n) U):=⟨A,E,GermIdeal.pullback (m := n) (zeroSection U) J,d⟩
  let MS := withN (coeffMarkedAlong (StepOneValue.barMarked M)) (M.N∩{z | u z=0})
  let MB := withN (coeffMarkedAlong (StepOneValue.barMarked B)) (B.N∩{y | u (zeroSection U y)=0})
  have hcBar : (StepOneValue.barMarked M).ideal.IsCoherent :=
    isCoherent_coeffMarkedAlong (isCoherent_homMarkedAlong (𝔪 := M) hJ (liftedCarrier_closed_submanifold hA))
      (liftedCarrier_closed_submanifold hA)
  have hcMS : MS.ideal.IsCoherent := isCoherent_coeffMarkedAlong hcBar (liftedCarrier_closed_submanifold hA)
  have hs : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (n+1)) ∞ (sectionToMask U O) := by
    apply (ContMDiff.subtypeVal_comp_iff O _).mp
    exact (zeroSection_contMDiff U).comp contMDiff_subtype_val
  have hDict : markedPullback (m := n) (zeroSection U) MS=MB :=
    global_contact_record A hA E J hJ d u
  change markedPullback (m := n) (sectionToMask U O)
      (markedPullback (m := n+1) (Subtype.val : O→productOpen U) MS) =
    markedPullback (m := n) (Subtype.val : baseMask U O→U) MB
  rw [←whole_markedPullback_comp contMDiff_subtype_val hs MS hcMS]
  have hsq : (Subtype.val : O→productOpen U) ∘ sectionToMask U O =
      zeroSection U ∘ (Subtype.val : baseMask U O→U) := rfl
  rw [hsq,whole_markedPullback_comp (zeroSection_contMDiff U) contMDiff_subtype_val MS hcMS,hDict]


theorem exists_actual_zero_contact_lower_domains
    (q : ℕ) (A : Set U) (E : List (Set U))
    (J : GermIdeal (n+1) (productOpen U)) (d : ℕ)
    (hM : IsInvDomain (q+1)
      (⟨liftedCarrier A,E.map (projection U ⁻¹' ·),J,d⟩ : MarkedIdeal (n+1) (productOpen U)))
    (hB : IsInvDomain (q+1)
      (⟨A,E,GermIdeal.pullback (m := n) (zeroSection U) J,d⟩ : MarkedIdeal n U))
    (hMax : IsMaximalOrderAlong (liftedCarrier A) J d) (x : U)
    (hx : x∈(⟨A,E,GermIdeal.pullback (m := n) (zeroSection U) J,d⟩ : MarkedIdeal n U).cosupp)
    (hReg : StepOneValue.stepRegime (X := CMfd.of (n := n) U)
      (⟨A,E,GermIdeal.pullback (m := n) (zeroSection U) J,d⟩ : MarkedIdeal n U) 0 .refl x) :
    let M : MarkedIdeal (n+1) (CMfd.of (n := n+1) (productOpen U)):=
      ⟨liftedCarrier A,E.map (projection U ⁻¹' ·),J,d⟩
    let B : MarkedIdeal n (CMfd.of (n := n) U):=⟨A,E,GermIdeal.pullback (m := n) (zeroSection U) J,d⟩
    let u : productOpen U→ℂ:=(StepOneValue.tangentChoice M (zeroSection U x)).2
    ∃ (V : TopologicalSpace.Opens U) (O : TopologicalSpace.Opens (productOpen U)),
      x∈V ∧ zeroSection U x∈O ∧ O≤StepOneValue.maskB M .refl (zeroSection U x) ∧
      (baseMask U O : Set U)⊆V ∧
      IsTangentDirectionAlong A (GermIdeal.pullback (m := n) (zeroSection U) J) d V (u ∘ zeroSection U) ∧
      IsInvDomain q (contactMarkedKept M u .refl O) ∧
      IsInvDomain q (contactMarkedKept B (u ∘ zeroSection U) .refl (baseMask U O)) := by
  let M : MarkedIdeal (n+1) (CMfd.of (n := n+1) (productOpen U)):=
    ⟨liftedCarrier A,E.map (projection U ⁻¹' ·),J,d⟩
  let B : MarkedIdeal n (CMfd.of (n := n) U):=⟨A,E,GermIdeal.pullback (m := n) (zeroSection U) J,d⟩
  let u : productOpen U→ℂ:=(StepOneValue.tangentChoice M (zeroSection U x)).2
  have hA:=hB.isWellFormed.isClosedSubmanifold_N
  have hJ:=hM.isWellFormed.isCoherent
  have hJhol : ∀z g,J.mem z g → HolomorphicAt (n+1) g z :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hJ hg
  have hSM : zeroSection U x∈M.cosupp := by
    change zeroSection U x∈cosupport (n+1) (liftedCarrier A) J d
    rw [source_cosupport_eq_lifted A J hJhol d]
    refine ⟨?_,?_⟩
    · rw [projection_section]
      exact hx
    · simp [zeroSection]
  have hBarM : zeroSection U x∈(StepOneValue.barMarked M).cosupp := by
    rw [StepOneLowerDomain.cosupp_barMarked M hM.isWellFormed hM.one_le_d]
    exact hSM
  have hLM : StepOneValue.level M .refl (zeroSection U x)=0 :=
    (level_section_refl A E J d x).trans hReg.1
  have hnsM : ¬StepOneValue.IsSpecial M .refl (zeroSection U x) :=
    fun h => hReg.2 ((isSpecial_section_refl_iff A hA E J hJ d x).mp h)
  have hLower := StepOneValueMasked.mem_lowerMask_and_isInvDomain_M M hM.isWellFormed
    hM.one_le_d (Nat.succ_pos n) hMax hM.dimLE .refl trivial hBarM
    (show StepOneValue.stepRegime M 0 .refl (zeroSection U x) from ⟨hLM,hnsM⟩)
  have hMaskM:=hLower.1
  change zeroSection U x∈StepOneValue.maskB M .refl (zeroSection U x) at hMaskM
  have hxChosen : zeroSection U x∈(StepOneValue.tangentChoice M (zeroSection U x)).1 :=
    (interior_subset hMaskM).1
  have hu:=StepOneCompare.tangentChoice_spec_of_mem M hxChosen
  have hu0 : u (zeroSection U x)=0 :=
    TangentDirectionAlong.apply_eq_zero_of_mem_cosupport hJhol hM.one_le_d hSM (hu.mem _ hxChosen)
  obtain ⟨V,hxV,_hVsub,hBaseU,_hContactBase,_hContactEq⟩ :=
    open_section_regular_contact A hA J hJ hu x hx.1 hxChosen hu0
  let O0:=StepOneValue.maskB M .refl (zeroSection U x)
  let O : TopologicalSpace.Opens (productOpen U):=
    O0 ⊓ ⟨projection U ⁻¹' V,V.isOpen.preimage (projection_contMDiff U).continuous⟩
  have hxO : zeroSection U x∈O := by
    refine ⟨hMaskM,?_⟩
    change projection U (zeroSection U x)∈V
    rwa [projection_section]
  let W:=baseMask U O
  have hWV : (W:Set U)⊆V := by
    intro y hy
    have hp : projection U (zeroSection U y)∈V:=hy.2
    rwa [projection_section] at hp
  let VS : TopologicalSpace.Opens (productOpen U):=
    ⟨(StepOneValue.tangentChoice M (zeroSection U x)).1,hu.isOpen⟩
  have hSourceDomain : IsInvDomain q (contactMarkedKept M u .refl O) := by
    exact ContactStageInvDomain.isInvDomain_stage_coeffHomAlong_of_le M hM.isWellFormed
      hM.one_le_d hM.dimLE VS hu .refl trivial O
      (fun z hz => (interior_subset hz.1).1)
      (fun z hz _hcontact => (interior_subset hz.1).2.2)
      (fun H hH z hz _hcontact => (interior_subset hz.1).2.1 H hH)
  have hcBar : (StepOneValue.barMarked M).ideal.IsCoherent :=
    isCoherent_coeffMarkedAlong (isCoherent_homMarkedAlong (𝔪 := M) hJ (liftedCarrier_closed_submanifold hA))
      (liftedCarrier_closed_submanifold hA)
  have hBaseDomain : IsInvDomain q (contactMarkedKept B (u ∘ zeroSection U) .refl W) := by
    apply ContactStageInvDomain.isInvDomain_stage_coeffHomAlong_of_le B hB.isWellFormed
      hB.one_le_d hB.dimLE V hBaseU .refl trivial W
      (fun y hy => hWV hy)
    · intro y hy _hcontact hyZ
      have hyO : zeroSection U y∈O0:=hy.1
      have hyNotZ := (interior_subset hyO).2.2
      have hC:=section_codimOnePart_iff A (StepOneValue.barMarked M).ideal
        (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hcBar hg) y (StepOneValue.barMarked M).d
      rw [bar_ideal_section A hA E J hJ d] at hC
      exact hyNotZ (hC.mpr hyZ)
    · intro H hH y hy _hcontact hyH
      change H∈E.take E.length at hH
      rw [List.take_length] at hH
      have hSourceMem : projection U ⁻¹' H∈StepOneValue.origMembers M .refl := by
        change projection U ⁻¹' H∈(E.map (projection U ⁻¹' ·)).take (E.map (projection U ⁻¹' ·)).length
        rw [List.take_length]
        exact List.mem_map_of_mem hH
      have hyO : zeroSection U y∈O0:=hy.1
      apply (interior_subset hyO).2.1 (projection U ⁻¹' H) hSourceMem
      simpa only [Set.mem_preimage,projection_section] using hyH
  exact ⟨V,O,hxV,hxO,inf_le_left,hWV,hBaseU,hSourceDomain,hBaseDomain⟩

end
end Hironaka.HironakaActualSectionContactKept

