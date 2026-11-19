import Hironaka.Resolution.HironakaG8CuspDerivativeTrace
import Hironaka.Resolution.HironakaDisjointCoherentNormalRecoding
import Hironaka.Resolution.HironakaAnalyticBaseChangeQuotientModel
import Hironaka.Resolution.HironakaSmoothCentreRealDomainGraphDictionary
import Hironaka.Resolution.HironakaActualPointGeometricBennett

/-! Exact nonprincipal ambient initial tie obstruction under zero-section stabilization. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8EmbeddedCuspInitialTie

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec CanonicalCentres
  HironakaG8CuspDerivativeTrace HironakaG8SameHSCuspContact HironakaDisjointCoherentNormalRecoding
  HironakaAnalyticBaseChangeQuotientModel HironakaSmoothCentreRealDomainGraphDictionary
  HironakaActualPointGeometricBennett HironakaRelativeNormalDeformationInitialRelations
  HironakaHolomorphicJetRankLoci HironakaHolomorphicJetChartInvariance
  HironakaRelativeNormalIdeal HironakaActualZeroSectionStabilization HironakaActualZeroCoordinateContactSeed
  HironakaActualCentreJointJets HironakaActualIntrinsicStableAmbientIso
  GermIdealPullbackCalculus HolGerm RelativePrincipalizationSpan
  HironakaHolomorphicJetMonomialSpan HironakaActualFiniteCoefficientIdeals
  HironakaActualWholeStalkHolomorphicPullback AnalyticIrreducibleComponents
  DivisorExponentAlong GermIdealOrder IdealOrderArithmetic

private abbrev model (n : ℕ) : CMfd n := CMfd.of (n := n) (ComplexModel n)

private theorem on_zero_plane (n : ℕ) (z : ComplexModel n) :
    tangentInclusion n 1 z ∈ zeroPlane n := by
  change actualJointNormalProjection n 1 (tangentInclusion n 1 z) = 0
  ext i
  exact tangentInclusion_normal n 1 z i

private theorem zero_plane_retract {n : ℕ} {z : ComplexModel (n+1)} (hz : z ∈ zeroPlane n) :
    tangentInclusion n 1 (tangentProjection n 1 z) = z := by
  have hzero : actualJointNormalProjection n 1 z = 0 := hz
  simpa only [HironakaActualIntrinsicStableAmbientIso.join,hzero,map_zero,add_zero] using
    (join_projections (n := n) (m := 1) z)

private theorem zero_plane_coherent (n : ℕ) :
    (vanishingIdeal (n := n+1) (zeroPlane n)).IsCoherent :=
  CartanIrreducible.cartanCoherence _ (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
    (actualJointNormalProjection n 1).contMDiff
    (FibreDimensionLowerBound.isComplexAnalyticSubset_singleton (0 : ComplexModel 1)))

/-- The whole analytic vanishing stalk of the actual zero plane is exactly
the kernel of the actual holomorphic trace, hence the full normal ideal. -/
theorem zero_plane_origin_ideal (n : ℕ) :
    originalCoherentOriginIdeal (vanishingIdeal (n := n+1) (zeroPlane n)) = normalIdeal n 1 := by
  rw [normalIdeal_eq_ker_planeTrace]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨f,hf,hmem,rfl⟩
    change planeTrace n 1 (HolGerm.mk f hf) = 0
    unfold planeTrace
    rw [compAlgHom_mk, ← HolGerm.mk_zero]
    apply HolGerm.mk_eq_mk_iff.mpr
    have ht : Tendsto (tangentInclusion n 1) (𝓝 (0 : ComplexModel n)) (𝓝 (0 : ComplexModel (n+1))) := by
      simpa only [map_zero] using (tangentInclusion n 1).continuous.tendsto (0 : ComplexModel n)
    filter_upwards [ht.eventually hmem.2] with z hz
    exact hz (on_zero_plane n z)
  · intro g hg
    induction g using HolGerm.induction_on with
    | h f hf =>
      change planeTrace n 1 (HolGerm.mk f hf) = 0 at hg
      unfold planeTrace at hg
      rw [compAlgHom_mk, ← HolGerm.mk_zero] at hg
      have hEq := HolGerm.mk_eq_mk_iff.mp hg
      apply (mk_mem_originalCoherentOriginIdeal_iff _ (zero_plane_coherent n) hf).mpr
      refine ⟨hf.mono fun _ h => h.mdifferentiableAt,?_⟩
      have ht : Tendsto (tangentProjection n 1) (𝓝 (0 : ComplexModel (n+1))) (𝓝 (0 : ComplexModel n)) := by
        simpa only [map_zero] using (tangentProjection n 1).continuous.tendsto (0 : ComplexModel (n+1))
      filter_upwards [ht.eventually hEq] with z hz hzS
      change f (tangentInclusion n 1 (tangentProjection n 1 z)) = 0 at hz
      rwa [zero_plane_retract hzS] at hz

/-- The entire origin stalk of coherent functional stabilization is
precisely the existing zero-section stabilization of the original stalk. -/
theorem stabilized_origin_stalk {n : ℕ} (I : GermIdeal n (ComplexModel n)) (hI : I.IsCoherent) :
    wholeChartStalkIdeal (stabilizedIdeal I) 0 0
      (mem_chart_source (ComplexModel (n+1)) 0) =
    actualZeroSectionIdeal n 1 (wholeChartStalkIdeal I 0 0 (mem_chart_source (ComplexModel n) 0)) := by
  unfold stabilizedIdeal
  have hp := isCoherent_pullback (tangentProjection n 1).contMDiff hI
  rw [wholeChartStalkIdeal_sum _ _ hp (zero_plane_coherent n),
    wholeChartStalkIdeal_model_zero (GermIdeal.pullback (m := n+1) (tangentProjection n 1) I),
    wholeChartStalkIdeal_model_zero (vanishingIdeal (n := n+1) (zeroPlane n)),
    originalOriginIdeal_pullback_eq_of_holMem (tangentProjection n 1) I
      (fun f hf => (GermIdeal.IsCoherent.holomorphicAt_mem hI hf).mono
        (fun _ h => mdifferentiableAt_iff_differentiableAt.mp h)),
    zero_plane_origin_ideal, wholeChartStalkIdeal_model_zero I]
  rfl

/-- No original intrinsic Hilbert–Samuel jet is changed by functional
zero-section stabilization. -/
theorem stabilized_origin_hilbertSamuel {n : ℕ} (I : GermIdeal n (ComplexModel n)) (hI : I.IsCoherent) :
    hilbertSamuelAt (stabilizedIdeal I) 0 = hilbertSamuelAt I 0 := by
  funext l
  unfold hilbertSamuelAt
  rw [stabilized_origin_stalk I hI]
  exact hilbertSamuelValue_actualZeroSectionIdeal n 1 _ l

private theorem cusp_origin_stalk (p : ℕ) :
    wholeChartStalkIdeal (cuspIdeal p) 0 0 (mem_chart_source (ComplexModel 2) 0) =
      Ideal.span {cuspGerm p} := by
  let G : Fin 1 → ComplexModel 2 → ℂ := fun _ => cuspFunction p
  have hG : ∀ i, HolomorphicAt 2 (G i) 0 := fun _ =>
    Eventually.of_forall fun z =>
      ((((EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 2)).differentiableAt (x := z)).pow 2).sub
       (((EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 2)).differentiableAt (x := z)).pow p)).mdifferentiableAt
  have hGen (g : ComplexModel 2 → ℂ) :
      (cuspIdeal p).mem 0 g ↔ IsInSpanAt (n := 2) (· ∈ range G) 0 g := by
    change IsInSpanAt (n := 2) (· = cuspFunction p) 0 g ↔ _
    have h : range G = {cuspFunction p} := by ext g; simp [G]
    rw [h]
    rfl
  rw [wholeChartStalkIdeal_eq_actual_generator_span (cuspIdeal p) (0 : ComplexModel 2) G hG hGen]
  have hValue (i : Fin 1) :
      chartTranslatedGerm (0 : ComplexModel 2) 0 (mem_chart_source (ComplexModel 2) 0) (G i) (hG i) =
        cuspGerm p := by
    let x := fun z : ComplexModel 2 => z.ofLp 0
    let y := fun z : ComplexModel 2 => z.ofLp 1
    have hx : ∀ᶠ z in 𝓝 (0 : ComplexModel 2), DifferentiableAt ℂ x z :=
      Eventually.of_forall fun _ => (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 2)).differentiableAt
    have hy : ∀ᶠ z in 𝓝 (0 : ComplexModel 2), DifferentiableAt ℂ y z :=
      Eventually.of_forall fun _ => (EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 2)).differentiableAt
    have hxG : HolGerm.mk x hx = tangentPullback 1 1 (normalCoordinate 0 1 0) := by
      unfold tangentPullback normalCoordinate coordinateGerm
      rw [compAlgHom_mk]
      exact HolGerm.mk_eq_mk_iff.mpr (Eventually.of_forall fun _ => rfl)
    have hyG : HolGerm.mk y hy = normalCoordinate 1 1 0 := rfl
    change chartTranslatedGerm (0 : ComplexModel 2) 0 _ (G i) (hG i) =
      normalCoordinate 1 1 0 ^ 2 - tangentPullback 1 1 (normalCoordinate 0 1 0) ^ p
    rw [← hxG,← hyG,← HolGerm.mk_pow x hx p,← HolGerm.mk_pow y hy 2,← HolGerm.mk_sub]
    unfold chartTranslatedGerm translatedGerm
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => by simp [G,cuspFunction,x,y]
  congr 1
  rw [show (fun i : Fin 1 => chartTranslatedGerm (0 : ComplexModel 2) 0
    (mem_chart_source (ComplexModel 2) 0) (G i) (hG i)) = fun _ => cuspGerm p from funext hValue]
  ext g
  simp

private theorem cusp_mark_one_domain (p : ℕ) (hp : 2 < p) : IsInvDomain 2 (baseMarked (cuspIdeal p)) := by
  refine ⟨⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,cuspIdeal_coherent p,
    NormalCrossings.isSNCDivisor_nil,
    NormalCrossings.isTransverse_nil_of_isClosedSubmanifold HomogenizedGlueingTower.isClosedSubmanifold_univ⟩,
    fun x _ => ⟨2,le_rfl,regularAtDim_univ x⟩,le_rfl,?_⟩
  intro x _
  let f := cuspFunction p
  have hDiff : Differentiable ℂ f := by
    exact ((EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 2)).differentiable.pow 2).sub
      ((EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 2)).differentiable.pow p)
  have hMem : (cuspIdeal p).mem x f :=
    mem_actualPrincipalCoefficientIdeal 2 f univ isOpen_univ hDiff.mdifferentiable.mdifferentiableOn x (mem_univ x)
  refine ⟨f,hMem,Frequently.mono ?_ (fun z hz => ⟨mem_univ z,hz⟩)⟩
  by_contra h
  have hEq : f =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
    change ∀ᶠ z in 𝓝 x, f z = 0
    simpa using h
  have hAnal : AnalyticOnNhd ℂ f univ := fun z _ =>
    (((EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 2)).analyticAt z |>.pow 2).sub
      ((EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 2)).analyticAt z |>.pow p))
  have hAll := hAnal.eq_of_eventuallyEq analyticOnNhd_const hEq
  have hP := congrFun hAll (EuclideanSpace.single (1 : Fin 2) (1 : ℂ))
  simp [f,cuspFunction,zero_pow (by omega : p ≠ 0)] at hP

private theorem cusp_origin_cosupport (p : ℕ) (hp : 2 < p) :
    (0 : ComplexModel 2) ∈ (baseMarked (cuspIdeal p)).cosupp := by
  change (0 : ComplexModel 2) ∈ cosupport 2 univ (cuspIdeal p) 1
  apply cosupport_anti (by decide : 1 ≤ 2)
  rw [cusp_cosupport_two p hp.le]
  exact mem_singleton _

/-- The two genuine nonprincipal ambient mark-one records have the same
point Hilbert–Samuel profile but strictly different original invariant. -/
theorem embedded_cusp_three_five_same_HS_original_tie_fails :
    let g := stabilizedIdeal (cuspIdeal 3)
    let h := stabilizedIdeal (cuspIdeal 5)
    hilbertSamuelAt g 0 = hilbertSamuelAt h 0 ∧
    (∀ f : HolGerm (ComplexModel 3),
      wholeChartStalkIdeal g 0 0 (mem_chart_source (ComplexModel 3) 0) ≠ Ideal.span {f}) ∧
    (∀ f : HolGerm (ComplexModel 3),
      wholeChartStalkIdeal h 0 0 (mem_chart_source (ComplexModel 3) 0) ≠ Ideal.span {f}) ∧
    (canonicalInvariant 3).inv (stabilizedMarked (cuspIdeal 3)) (.refl : BlowupTower (model 3) (model 3)) 0 <
      (canonicalInvariant 3).inv (stabilizedMarked (cuspIdeal 5)) (.refl : BlowupTower (model 3) (model 3)) 0 := by
  intro g h
  have hProfile := cusp_three_five_same_HS_original_tie_fails
  refine ⟨?_,?_,?_,?_⟩
  · exact (stabilized_origin_hilbertSamuel _ (cuspIdeal_coherent 3)).trans
      (hProfile.1.trans (stabilized_origin_hilbertSamuel _ (cuspIdeal_coherent 5)).symm)
  · intro f hf
    change wholeChartStalkIdeal (stabilizedIdeal (cuspIdeal 3)) 0 0 _ = _ at hf
    rw [stabilized_origin_stalk _ (cuspIdeal_coherent 3), cusp_origin_stalk] at hf
    exact embeddedCusp_not_principal 3 (by decide) ⟨f,hf⟩
  · intro f hf
    change wholeChartStalkIdeal (stabilizedIdeal (cuspIdeal 5)) 0 0 _ = _ at hf
    rw [stabilized_origin_stalk _ (cuspIdeal_coherent 5), cusp_origin_stalk] at hf
    exact embeddedCusp_not_principal 5 (by decide) ⟨f,hf⟩
  · have h₃ := stabilized_initial_value (q := 2) (by decide : 0 < 2)
      (cusp_mark_one_domain 3 (by decide)) 0 (cusp_origin_cosupport 3 (by decide))
    have h₅ := stabilized_initial_value (q := 2) (by decide : 0 < 2)
      (cusp_mark_one_domain 5 (by decide)) 0 (cusp_origin_cosupport 5 (by decide))
    have e : tangentInclusion 2 1 (0 : ComplexModel 2) = 0 := map_zero _
    rw [e] at h₃ h₅
    change (invFamily (by decide : 0 < 3) 3).inv (stabilizedMarked (cuspIdeal 3))
        (.refl : BlowupTower (model 3) (model 3)) 0 <
      (invFamily (by decide : 0 < 3) 3).inv (stabilizedMarked (cuspIdeal 5))
        (.refl : BlowupTower (model 3) (model 3)) 0
    rw [h₃,h₅]
    exact (initialEmbedding 2).strictMono hProfile.2


end
end Hironaka.HironakaG8EmbeddedCuspInitialTie
