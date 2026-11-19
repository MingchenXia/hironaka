import Hironaka.Resolution.HironakaActualNativeSectionStepOneHistory

/-! The actual ORIGINAL positive Step One mask at every original native
prefix. Its interior is transported from the support of the excluded
special locus and the actual open boundary-avoidance condition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualNativeSectionPositiveMask
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  SubmanifoldChartedSpace NormalCrossings StepOneValue StepOneRegime BoundaryCount
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionOrderHistory
  HironakaActualNativeSectionInitialBar HironakaActualNativeSectionStepOneHistory
  HironakaActualOpenZeroSectionDifferentials
variable {n : ℕ}

/-- Subtype restriction commutes with the interior of the complement of
a subset actually supported on that subtype. -/
theorem interior_supported_complement {X : Type*} [TopologicalSpace X]
    (W A : Set X) (hA : A⊆W) :
    (Subtype.val : W→X) ⁻¹' interior Aᶜ=
      interior ((Subtype.val : W→X) ⁻¹' Aᶜ) := by
  have hImage : (Subtype.val : W→X) '' ((Subtype.val : W→X) ⁻¹' A)=A:=by
    ext x
    constructor
    · rintro ⟨p,hp,rfl⟩;exact hp
    · intro hx;exact ⟨⟨x,hA hx⟩,hx,rfl⟩
  have hClosure:=Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image
    ((Subtype.val : W→X) ⁻¹' A)
  rw [hImage] at hClosure
  simp only [preimage_compl,interior_compl,hClosure]

private theorem open_avoidance {X : Type*} [TopologicalSpace X]
    (E : List (Set X)) (hE : ∀H∈E,IsClosed H) (p : X) :
    IsOpen {z | ∀H∈E,z∈H → p∈H} := by
  classical
  have heq : {z | ∀H∈E,z∈H → p∈H}=
      ⋂H∈{H | H∈E},{z | z∈H → p∈H}:=by ext; simp
  rw [heq]
  apply (List.finite_toSet E).isOpen_biInter
  intro H hH
  by_cases hp : p∈H
  · simpa only [hp,implies_true,ofPred_true] using isOpen_univ (X:=X)
  · have heq : {z | z∈H → p∈H}=Hᶜ:=by ext z; simp [hp]
    rw [heq]
    exact (hE H hH).isOpen_compl

private theorem zeroPlane_closed (U : Opens (ComplexModel n)) : IsClosed (zeroPlane U) :=
  (liftedCarrier_closed_submanifold
    (HomogenizedGlueingTower.isClosedSubmanifold_univ (n:=n) (M:=U))).1

/-- Exact ORIGINAL maskA at every original prefix, on the unchanged native
model. No interior pullback law or mask comparison is assumed. -/
theorem actual_section_maskA
    (U : Opens (ComplexModel n)) (A : Set U) (hA : IsClosedSubmanifold n A)
    (E : List (Set U)) (hE : IsSNCDivisor n E)
    (J : GermIdeal (n+1) (productOpen U)) (hJ : J.IsCoherent) (d : ℕ)
    {Y : CMfd.{0} (n+1)} {T : BlowupTower (CMfd.of (n:=n+1) (productOpen U)) Y}
    {V : Set Y} {hVc : IsClosed V} {hV : ∀y∈V,RegularAtDim (n:=n+1) V y n}
    {Q : BlowupTower (nativeManifold (Y:=CMfd.of (n:=n+1) (productOpen U))
        (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U))
      (nativeManifold (Nat.le_succ n) V hV)}
    (h : Lift (Nat.le_succ n) (zeroPlane U) (zeroPlane_closed U) (zeroPlane_regular U)
      (E.map (projection U ⁻¹' ·)) T V hVc hV Q)
    (p : nativeManifold (Nat.le_succ n) V hV) :
    let M : MarkedIdeal (n+1) (CMfd.of (n:=n+1) (productOpen U)):=
      ⟨liftedCarrier A,E.map (projection U ⁻¹' ·),J,d⟩
    let B:=nativePullback (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) M
    (Subtype.val : V→Y) ⁻¹' (maskA M T p.val : Set Y)=
      (maskA B Q p : Set (nativeManifold (Nat.le_succ n) V hV)) := by
  let M : MarkedIdeal (n+1) (CMfd.of (n:=n+1) (productOpen U)):=
    ⟨liftedCarrier A,E.map (projection U ⁻¹' ·),J,d⟩
  let B:=nativePullback (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) M
  obtain ⟨_hRec,hOrig,hLS,_hReg,_hRun⟩:=actual_section_step_one_chronology U A hA E hE J hJ d h
  let C : Set Y:={z | ∀H∈origMembers M T,z∈H → p.val∈H}
  let S : Set Y:={z | level M T z=level M T p.val ∧ IsSpecial M T z}
  have hMN : M.N⊆zeroPlane U:=fun _ hx=>⟨mem_univ _,hx.2⟩
  have hSub : (geoTransformAlong (barMarked M) T).N⊆V:=
    Lift.current_carrier_subset h (barMarked M) hMN
  have hSS : S⊆V:=by
    intro z hz
    rcases hz.2 with hzero|hpos
    · exact hSub ((geoTransformAlong (barMarked M) T).cosupp_subset_N
        (CodimOneSupportAlong.codimOnePartAlong_subset hzero.2))
    · exact hSub ((geoTransformAlong (barMarked M) T).cosupp_subset_N hpos.2.1)
  have hE' :=HironakaActualSectionBoundaryGeometry.isSNCDivisor_preimage_projection (U:=U) E hE
  have hC : IsOpen C:=open_avoidance (origMembers M T)
    (StepOneLowerDomain.isClosed_of_mem_origMembers M hE'.1 T) p.val
  have hSC :=interior_supported_complement V S hSS
  have hPre : (Subtype.val : V→Y) ⁻¹' (C∩Sᶜ)=
      {z | (∀H∈origMembers B Q,z∈H → p∈H) ∧
        ¬(level B Q z=level B Q p ∧ IsSpecial B Q z)}:=by
    ext z
    change ((∀H∈origMembers M T,z.val∈H → p.val∈H) ∧
        ¬(level M T z.val=level M T p.val ∧ IsSpecial M T z.val)) ↔ _
    rw [←hOrig]
    simp only [List.mem_map,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂,mem_preimage]
    rw [(hLS z).1,(hLS p).1,(hLS z).2]
    rfl
  change (Subtype.val : V→Y) ⁻¹' interior (C∩Sᶜ)=_
  rw [interior_inter,hC.interior_eq,preimage_inter,hSC]
  rw [←(hC.preimage continuous_subtype_val).interior_eq,←interior_inter,←preimage_inter,hPre]
  rfl

end
end Hironaka.HironakaActualNativeSectionPositiveMask
