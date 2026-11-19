import Hironaka.Resolution.HironakaActualNativeSectionRegularity
import Hironaka.Resolution.HironakaActualSectionInitialBoundaryMask
import Hironaka.Analytic.SubmanifoldCodRestrict

/-! The actual original zero-section factors through its literal induced
native plane. This constructs the initial whole bar-record dictionary;
no desired initial comparison or native-model identity is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualNativeSectionInitialBar
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  SubmanifoldChartedSpace SubmanifoldCodRestrict
  HironakaActualOpenZeroSectionDifferentials HironakaActualSectionInitialValues
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionRegularity
  HironakaActualRawRecordPullbacks HironakaSmoothSubmersionCoefficientIdeals
  HironakaSmoothSubmersionOrderedChoiceImageTrace RelativePrincipalizationSpan
  HironakaActualNonregularCoefficientNaturality
  HironakaActualCentreJointJets HironakaRelativeNormalIdeal
variable {n : ℕ} (U : Opens (ComplexModel n))

def zeroPlane : Set (productOpen U):=liftedCarrier (univ : Set U)

private theorem projection_section (x : U) : projection U (zeroSection U x)=x := by
  apply Subtype.ext
  exact HironakaRelativeNormalIdeal.tangentProjection_tangentInclusion n 1 x

private theorem section_mem (A : Set U) (x : U) : zeroSection U x∈liftedCarrier A ↔ x∈A := by
  change (projection U (zeroSection U x)∈A ∧ actualJointNormalProjection n 1 (tangentInclusion n 1 x)=0) ↔ x∈A
  rw [projection_section]
  simp

private theorem section_projection (z : productOpen U) (hz : z∈zeroPlane U) :
    zeroSection U (projection U z)=z := by
  apply Subtype.ext
  change HironakaRelativeNormalIdeal.tangentInclusion n 1
    (HironakaRelativeNormalIdeal.tangentProjection n 1 z.val)=z.val
  simpa only [HironakaActualIntrinsicStableAmbientIso.join,hz.2,map_zero,add_zero] using
    (HironakaActualIntrinsicStableAmbientIso.join_projections (n:=n) (m:=1) z.val)

theorem zeroPlane_regular : ∀z∈zeroPlane U,RegularAtDim (n:=n+1) (zeroPlane U) z n := by
  intro z hz
  have h:= (regularAtDim_actual_section_iff (univ : Set U) (projection U z) (mem_univ _) n).mpr
    (AnalyticIrreducibleComponents.regularAtDim_univ (projection U z))
  rw [section_projection U z hz] at h
  exact h

def nativeZeroSectionEquiv :
    CMfd.of (n:=n) U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      nativeManifold (Y:=CMfd.of (n:=n+1) (productOpen U))
        (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) := by
  let := chartedSpace (Nat.le_succ n) (zeroPlane_regular U)
  have := isComplexManifold_chartedSpace (Nat.le_succ n) (zeroPlane_regular U)
  have hZero (x : U) : zeroSection U x∈zeroPlane U := by
    exact (section_mem U (univ : Set U) x).mpr (mem_univ _)
  refine ⟨⟨(fun x=>⟨zeroSection U x,hZero x⟩),(fun z=>projection U z.val),?_,?_⟩,?_,?_⟩
  · exact projection_section U
  · intro z
    exact Subtype.ext (section_projection U z.val z.property)
  · exact contMDiff_codRestrict (Nat.le_succ n) (zeroPlane_regular U) (zeroSection_contMDiff U) hZero
  · exact (projection_contMDiff U).comp (contMDiff_val (Nat.le_succ n) (zeroPlane_regular U))

private theorem native_closed_submanifold
    {r k : ℕ} {X : Type} [TopologicalSpace X]
    [ChartedSpace (ComplexModel r) X] [IsComplexManifold r X]
    {W N : Set X} (hk : k≤r) (hW : ∀x∈W,RegularAtDim (n:=r) W x k)
    (hN : IsClosedSubmanifold r N) (hNW : N⊆W) :
    letI := chartedSpace hk hW
    letI := isComplexManifold_chartedSpace hk hW
    IsClosedSubmanifold k ((Subtype.val : W→X) ⁻¹' N) := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  let A:=(Subtype.val : W→X) ⁻¹' N
  have hImage : (Subtype.val : W→X) '' A=N:=by
    ext x
    constructor
    · rintro ⟨p,hp,rfl⟩;exact hp
    · intro hx;exact ⟨⟨x,hNW hx⟩,hx,rfl⟩
  refine ⟨hN.1.preimage continuous_subtype_val,?_⟩
  intro p hp
  obtain ⟨j,hj⟩:=hN.2 p.val hp
  have h:=(regularAtDim_native_image_iff hk hW A p j)
  rw [hImage] at h
  exact ⟨j,h.mp hj⟩

private theorem pullback_biholo_injective
    {X Y : CMfd.{0} n}
    (F : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y)
    (A B : MarkedIdeal n Y) (hA : A.ideal.IsCoherent) (hB : B.ideal.IsCoherent)
    (h : MarkedIdeal.pullback F A=MarkedIdeal.pullback F B) : A=B := by
  have hInv (M : MarkedIdeal n Y) (hM : M.ideal.IsCoherent) :
      MarkedIdeal.pullback F.symm (MarkedIdeal.pullback F M)=M :=
    (marked_pullback_comp_hhol (fun _ _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem hM hg)
      F.contMDiff F.symm.contMDiff (d:=id) F.apply_symm_apply).trans
      (ContactCanonicalAlong.pullback_id M hM)
  have h':=congrArg (MarkedIdeal.pullback F.symm) h
  rwa [hInv A hA,hInv B hB] at h'

theorem nativePullback_section_barMarked
    (A : Set U) (hA : IsClosedSubmanifold n A) (E : List (Set U))
    (J : GermIdeal (n+1) (productOpen U)) (hJ : J.IsCoherent) (d : ℕ) :
    let M : MarkedIdeal (n+1) (CMfd.of (n:=n+1) (productOpen U)):=
      ⟨liftedCarrier A,E.map (projection U ⁻¹' ·),J,d⟩
    let B:=nativePullback (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) M
    nativePullback (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U)
      (StepOneValue.barMarked M)=StepOneValue.barMarked B := by
  let := chartedSpace (Nat.le_succ n) (zeroPlane_regular U)
  have := isComplexManifold_chartedSpace (Nat.le_succ n) (zeroPlane_regular U)
  let M : MarkedIdeal (n+1) (CMfd.of (n:=n+1) (productOpen U)):=
    ⟨liftedCarrier A,E.map (projection U ⁻¹' ·),J,d⟩
  let B:=nativePullback (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) M
  let B₀ : MarkedIdeal n (CMfd.of (n:=n) U):=
    ⟨A,E,GermIdeal.pullback (m:=n) (zeroSection U) J,d⟩
  let F:=nativeZeroSectionEquiv U
  have hMN : M.N⊆zeroPlane U:=fun _ hx=>⟨mem_univ _,hx.2⟩
  have hMc : IsClosedSubmanifold (n+1) M.N:=liftedCarrier_closed_submanifold hA
  have hBcoh : B.ideal.IsCoherent:=GermIdealPullbackCalculus.isCoherent_pullback
    (contMDiff_val (Nat.le_succ n) (zeroPlane_regular U)) hJ
  have hBN : IsClosedSubmanifold n B.N:=
    native_closed_submanifold (Nat.le_succ n) (zeroPlane_regular U) hMc hMN
  have hBarMc : (StepOneValue.barMarked M).ideal.IsCoherent:=StepOneValue.isCoherent_barMarked M hMc hJ
  have hBarBc : (StepOneValue.barMarked B).ideal.IsCoherent:=StepOneValue.isCoherent_barMarked B hBN hBcoh
  have hNativeBarc : (nativePullback (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U)
      (StepOneValue.barMarked M)).ideal.IsCoherent:=
    GermIdealPullbackCalculus.isCoherent_pullback
      (contMDiff_val (Nat.le_succ n) (zeroPlane_regular U)) hBarMc
  have hP (K : MarkedIdeal (n+1) (CMfd.of (n:=n+1) (productOpen U))) (hK : K.ideal.IsCoherent) :
      MarkedIdeal.pullback F (nativePullback (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) K)=
        markedPullback (m:=n) (zeroSection U) K := by
    exact (whole_markedPullback_comp
      (contMDiff_val (Nat.le_succ n) (zeroPlane_regular U)) F.contMDiff K hK).symm
  have hPraw : MarkedIdeal.pullback F B=B₀ := by
    rw [hP M hJ]
    apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    · ext x
      exact section_mem U A x
    · change (E.map (projection U ⁻¹' ·)).map (zeroSection U ⁻¹' ·)=E
      rw [List.map_map]
      change E.map (fun H=>zeroSection U ⁻¹' (projection U ⁻¹' H))=E
      have hFun : (fun H : Set U=>zeroSection U ⁻¹' (projection U ⁻¹' H))=id:=by
        funext H
        ext x
        change projection U (zeroSection U x)∈H ↔ x∈H
        rw [projection_section]
      rw [hFun,List.map_id]
    · rfl
    · rfl
  have hLoc : ∀x,∃ψ,DerivativeIdealAlongEtale.IsLocalInverseAt n F ψ x:=
    fun x=>⟨F.symm,HomogenizedIdealAlong.isLocalInverseAt_of_contMDiff
      F.contMDiff F.symm.contMDiff F.apply_symm_apply F.symm_apply_apply x⟩
  have hPbar : MarkedIdeal.pullback F (StepOneValue.barMarked B)=StepOneValue.barMarked B₀:=by
    rw [HironakaActualNonregularCoefficientNaturality.pullback_coeff_homMarkedAlong
      F.contMDiff hLoc B (fun _ _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem hBcoh hg),hPraw]
  apply pullback_biholo_injective F _ _ hNativeBarc hBarBc
  rw [hP (StepOneValue.barMarked M) hBarMc,hPbar]
  exact HironakaActualSectionInitialBoundaryMask.markedPullback_section_barMarked A hA E J hJ d

end
end Hironaka.HironakaActualNativeSectionInitialBar
