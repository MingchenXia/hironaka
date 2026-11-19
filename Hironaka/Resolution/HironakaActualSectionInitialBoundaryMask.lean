import Hironaka.Resolution.HironakaActualSectionMemberRestriction

/-! Exact original initial maskA and whole bar-record transport on the actual zero section. These initial data do not compare chronological lower runs. -/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualSectionInitialBoundaryMask
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BoundaryCount
  HironakaActualOpenZeroSectionDifferentials HironakaRelativeNormalIdeal
  HironakaActualCentreJointJets HironakaActualIntrinsicStableAmbientIso
  HironakaActualSectionInitialBoundaryRegime HironakaActualSectionMemberRestriction
  HironakaActualMaskSectionRepresentative HironakaSmoothSubmersionCoefficientIdeals
  CodimOneSupportAlong

theorem preimage_interior_of_retraction
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (s : X → Y) (p : Y → X) (hs : Continuous s) (hp : Continuous p)
    (hps : ∀ x, p (s x)=x) (P : Set Y) (Q : Set X)
    (hsect : ∀ x, s x∈P ↔ x∈Q) (hproj : p ⁻¹' Q ⊆ P) :
    s ⁻¹' interior P = interior Q := by
  apply Set.Subset.antisymm
  · exact interior_maximal (fun x hx => (hsect x).mp (interior_subset hx))
      (isOpen_interior.preimage hs)
  · have hinc : p ⁻¹' interior Q ⊆ interior P :=
      interior_maximal ((Set.preimage_mono interior_subset).trans hproj)
        (isOpen_interior.preimage hp)
    intro x hx
    apply hinc
    change p (s x)∈interior Q
    rwa [hps]

variable {n : ℕ} {U : TopologicalSpace.Opens (ComplexModel n)}

private theorem projection_section (x : U) : projection U (zeroSection U x)=x := by
  apply Subtype.ext
  exact tangentProjection_tangentInclusion n 1 x

private theorem section_projection (A : Set U) (z : productOpen U) (hz : z∈liftedCarrier A) :
    zeroSection U (projection U z)=z := by
  apply Subtype.ext
  change tangentInclusion n 1 (tangentProjection n 1 z.val)=z.val
  simpa only [HironakaActualIntrinsicStableAmbientIso.join,hz.2,map_zero,add_zero]
    using join_projections (n := n) (m := 1) z.val

theorem markedPullback_section_barMarked (A : Set U) (hA : IsClosedSubmanifold n A)
    (E : List (Set U)) (J : GermIdeal (n+1) (productOpen U)) (hJ : J.IsCoherent) (d : ℕ) :
    let M : MarkedIdeal (n+1) (productOpen U):=⟨liftedCarrier A,E.map (projection U ⁻¹' ·),J,d⟩
    let B : MarkedIdeal n U:=⟨A,E,GermIdeal.pullback (m := n) (zeroSection U) J,d⟩
    markedPullback (m := n) (zeroSection U)
      (StepOneValue.barMarked (X := CMfd.of (n := n+1) (productOpen U)) M)=
      StepOneValue.barMarked (X := CMfd.of (n := n) U) B := by
  have hCoeff := markedPullback_section_coeffMarkedAlong A hA E J hJ d
  have hN := congrArg (fun K : MarkedIdeal n U => K.N) hCoeff
  have hE := congrArg (fun K : MarkedIdeal n U => K.E) hCoeff
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · exact hN
  · exact hE
  · exact bar_ideal_section A hA E J hJ d
  · rfl

theorem baseMask_maskA (A : Set U) (hA : IsClosedSubmanifold n A)
    (E : List (Set U)) (J : GermIdeal (n+1) (productOpen U)) (hJ : J.IsCoherent) (d : ℕ) (x : U) :
    let M : MarkedIdeal (n+1) (productOpen U):=⟨liftedCarrier A,E.map (projection U ⁻¹' ·),J,d⟩
    let B : MarkedIdeal n U:=⟨A,E,GermIdeal.pullback (m := n) (zeroSection U) J,d⟩
    baseMask U (StepOneValue.maskA (X := CMfd.of (n := n+1) (productOpen U))
      M .refl (zeroSection U x)) =
      StepOneValue.maskA (X := CMfd.of (n := n) U) B .refl x := by
  classical
  let M : MarkedIdeal (n+1) (CMfd.of (n := n+1) (productOpen U)):=
    ⟨liftedCarrier A,E.map (projection U ⁻¹' ·),J,d⟩
  let B : MarkedIdeal n (CMfd.of (n := n) U):=⟨A,E,GermIdeal.pullback (m := n) (zeroSection U) J,d⟩
  have hOrigM : StepOneValue.origMembers M .refl=E.map (projection U ⁻¹' ·) := by
    change (E.map (projection U ⁻¹' ·)).take (E.map (projection U ⁻¹' ·)).length=_
    exact List.take_length
  have hOrigB : StepOneValue.origMembers B .refl=E := by
    change E.take E.length=E
    exact List.take_length
  have hLevel (z : productOpen U) : StepOneValue.level M .refl z=StepOneValue.level B .refl (projection U z) := by
    unfold StepOneValue.level
    rw [hOrigM,hOrigB,boundaryCount_map]
    rfl
  have hLevelX : StepOneValue.level M .refl (zeroSection U x)=StepOneValue.level B .refl x := by
    simpa only [projection_section] using hLevel (zeroSection U x)
  have hSpecial (z : productOpen U) (hz : StepOneValue.IsSpecial M .refl z) :
      StepOneValue.IsSpecial B .refl (projection U z) := by
    have hzN : z∈liftedCarrier A := by
      rcases hz with ⟨_hl,hZ⟩ | ⟨_hl,hL⟩
      · exact (codimOnePartAlong_subset hZ).1
      · exact hL.1.1
    have he := section_projection A z hzN
    apply (isSpecial_section_refl_iff A hA E J hJ d (projection U z)).mp
    rw [he]
    exact hz
  let P : Set (productOpen U) := {z |
    (∀ H∈E.map (projection U ⁻¹' ·),z∈H → zeroSection U x∈H) ∧
      ¬(StepOneValue.level M .refl z=StepOneValue.level M .refl (zeroSection U x) ∧
        StepOneValue.IsSpecial M .refl z)}
  let Q : Set U := {y |
    (∀ H∈E,y∈H → x∈H) ∧
      ¬(StepOneValue.level B .refl y=StepOneValue.level B .refl x ∧ StepOneValue.IsSpecial B .refl y)}
  have hBoundary (z : productOpen U) :
      (∀ H∈E.map (projection U ⁻¹' ·),z∈H → zeroSection U x∈H) ↔
      (∀ H∈E,projection U z∈H → x∈H) := by
    constructor
    · intro h H hH hzH
      have hh := h (projection U ⁻¹' H) (List.mem_map_of_mem hH) hzH
      simpa only [Set.mem_preimage,projection_section] using hh
    · intro h K hK hzK
      obtain ⟨H,hH,rfl⟩ := List.mem_map.mp hK
      simpa only [Set.mem_preimage,projection_section] using h H hH hzK
  have hSect : ∀ y : U,zeroSection U y∈P ↔y∈Q := by
    intro y
    simp only [P,Q,Set.mem_ofPred_eq]
    rw [hBoundary,projection_section,level_section_refl A E J d y,hLevelX,
      isSpecial_section_refl_iff A hA E J hJ d y]
  have hProj : projection U ⁻¹' Q ⊆ P := by
    intro z hz
    refine ⟨(hBoundary z).mpr hz.1,?_⟩
    rintro ⟨hl,hsp⟩
    apply hz.2
    exact ⟨(hLevel z).symm.trans (hl.trans hLevelX),hSpecial z hsp⟩
  have hMaskM : (StepOneValue.maskA M .refl (zeroSection U x) : Set (productOpen U))=interior P := by
    change interior {z |
      (∀ H∈StepOneValue.origMembers M .refl,z∈H → zeroSection U x∈H) ∧
        ¬(StepOneValue.level M .refl z=StepOneValue.level M .refl (zeroSection U x) ∧
          StepOneValue.IsSpecial M .refl z)}=interior P
    rw [hOrigM]
  have hMaskB : (StepOneValue.maskA B .refl x : Set U)=interior Q := by
    change interior {y |
      (∀ H∈StepOneValue.origMembers B .refl,y∈H → x∈H) ∧
        ¬(StepOneValue.level B .refl y=StepOneValue.level B .refl x ∧
          StepOneValue.IsSpecial B .refl y)}=interior Q
    rw [hOrigB]
  apply TopologicalSpace.Opens.ext
  change zeroSection U ⁻¹' (StepOneValue.maskA M .refl (zeroSection U x) : Set (productOpen U)) =
    (StepOneValue.maskA B .refl x : Set U)
  rw [hMaskM,hMaskB]
  exact preimage_interior_of_retraction (zeroSection U) (projection U)
    (zeroSection_contMDiff U).continuous (projection_contMDiff U).continuous
    (projection_section (U := U)) P Q hSect hProj

end
end Hironaka.HironakaActualSectionInitialBoundaryMask

