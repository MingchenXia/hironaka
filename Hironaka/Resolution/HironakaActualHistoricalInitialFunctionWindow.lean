import Hironaka.Resolution.HironakaActualHistoricalInitialNativePointWindow
import Hironaka.Resolution.HironakaActualHistoricalNativeFunctionSuccessor

/-! ONE original P/s/function family is fixed before EVERY moving initial
point. The literal row-scaled original PHS functions initialize the exact
anchored history with identity projection and common denominator ONE. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualHistoricalInitialFunctionWindow
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaActualHistoricalInitialNativePointWindow HironakaActualHistoricalNativeFunctionSuccessor
  HironakaActualHistoricalInitialAffineDictionary HironakaActualHistoricalSortedPrefixFrames
  HironakaActualHistoricalWholeJetFrames HironakaActualHistoricalPrefixJetFrames
  HironakaActualGeometricCurrentNeighborhoodHS HironakaActualRelativeNormalJetDivision
  HironakaActualFixedInheritedSelector HironakaActualInheritedNestedContactFlag
  HironakaActualNormalZeroAnalyticSaturation HironakaActualFormalInitialDiagram
  HironakaActualOriginalFormalHSTransfer HironakaActualInheritedSmallTails
  HironakaActualInheritedNeighborhoodStandardJets HironakaActualCauchyCoordinateDivision
  HironakaActualWeightedVertexSmallTails HironakaActualFiniteDegLexWeights
  HironakaActualCoefficientPresentationCentrePower HironakaActualCauchyMonomialDivision
  HironakaRelativeNormalMonomialBasis HironakaActualOriginalScaledAnalyticDivision
  HironakaActualOriginalInitialHSPhase HironakaActualHistoricalHSMarkedDomain
  HironakaSmoothSubmersionGermIdealColon HironakaHolomorphicJetRankLoci
  HironakaActualDiagonalTaylor HironakaHolomorphicJetChartInvariance

variable {n : ℕ} {I : Ideal (HolGerm (ComplexModel n))}
  {G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)}

private theorem scaled_native_function_holomorphic
    {A : GermIdeal n (ComplexModel n)} {R : ℕ → ℕ}
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R)
    (r : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I) → ℂ)
    (v) (x : presentationOpen PHS) :
    HolomorphicAt n (fun z : presentationOpen PHS=>r v*PHS.representatives v z.val) x := by
  have h : HolomorphicAt n (PHS.representatives v) x.val:=
    (PHS.holomorphicAt x.val x.property v).mono (fun _ hz=>hz.mdifferentiableAt)
  have hU : HolomorphicAt n (fun z : presentationOpen PHS=>PHS.representatives v z.val) x:=
    h.comp_contMDiff (Eventually.of_forall fun _=>(contMDiff_subtype_val (U:=presentationOpen PHS)).contMDiffAt)
  exact (holomorphicAt_const (r v)).mul hU

private theorem scaled_affine_member
    {A : GermIdeal n (ComplexModel n)} {R : ℕ → ℕ}
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R) (x : presentationOpen PHS)
    (c : Fin n → ℂ) (hc : ∀i,c i≠0)
    (r : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I) → ℂ) (v) :
    adaptedGerm x (actualInitialAffineChart (presentationOpen PHS) x c hc)
      (actual_initial_affine_chart_geometry (presentationOpen PHS) x c hc).2
      (fun z : presentationOpen PHS=>r v*PHS.representatives v z.val)
      (scaled_native_function_holomorphic PHS r v x)=
        HolGerm.constHom (r v)*actualDiagonalPullback c
          (translatedGerm x.val (PHS.representatives v) (PHS.holomorphicAt _ x.property v)) := by
  have h : HolomorphicAt n (PHS.representatives v) x.val:=
    (PHS.holomorphicAt x.val x.property v).mono (fun _ hz=>hz.mdifferentiableAt)
  have hU : HolomorphicAt n (fun z : presentationOpen PHS=>PHS.representatives v z.val) x:=
    h.comp_contMDiff (Eventually.of_forall fun _=>(contMDiff_subtype_val (U:=presentationOpen PHS)).contMDiffAt)
  have hMember:=actual_initial_affine_adapted_germ (presentationOpen PHS) x c hc _
    (PHS.holomorphicAt _ x.property v) hU
  rw [←hMember]
  unfold adaptedGerm
  rw [←HolGerm.mk_const,←HolGerm.mk_mul]

/-- The SAME original row-scaled PHS functions, chosen ONCE before every
point, initialize the true native original-function history with D=1. -/
theorem exists_actual_initial_native_original_function_window
    (B : Set (ComplexModel n)) {R : ℕ → ℕ}
    (hspan : Ideal.span (range G.germs)=I)
    (PHS : ActualGeometricInheritedNeighborhoodHS (vanishingIdeal (n:=n) B) I G R)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)))
    (hred : ∀r,ActualInheritedPrefixReducedAt G r)
    (hContact : ∀r,actualFixedSelectorContactAt S G.germs r)
    {M : Type*} (η : presentationOpen PHS → M) (E : List (Set M)) :
    ∃(P : ActualInheritedWeightedTailData G)(s : ℂ)(hs0 : s≠0)
      (_hs : s∈Metric.ball 0 P.radius)(δ : ℝ)
      (hBound : ∀j : Fin (actualVertexCount n I),normalExponentDegree
        (wordExponent (actualVertexWords n I j))≤P.germs.degreeBound),
      0<δ ∧ IsOpen (historicalNativeJetWindow P s hs0 δ) ∧
      (0 : ComplexModel n)∈historicalNativeJetWindow P s hs0 δ ∧
      historicalNativeJetWindow P s hs0 δ⊆PHS.neighborhood ∧
      let aFull : Fin (historicalDegreePrefixCount (actualVertexWords n I) P.germs.degreeBound) ≃
        actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I):=
        (historicalDegreeFullLabelEquiv (actualVertexWords n I) P.germs.degreeBound hBound).trans
          (actualVertexEnumeration n I)
      let wFull:=historicalDegreePrefixWords (actualVertexWords n I) P.germs.degreeBound
      let F₀:=fun (v : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I))
        (x : presentationOpen PHS)=>
        (s^weightedDegree (degLexWeight n P.germs.degreeBound) v.val)⁻¹*PHS.representatives v x.val
      (∀j,wordExponent (wFull j)=(aFull j).val) ∧
      (∀j,historicalOwner wFull (wordExponent (wFull j))=some j) ∧
      ∃hF₀ : ∀v x,HolomorphicAt n (F₀ v) x,
        ∀x : presentationOpen PHS,x.val∈historicalNativeJetWindow P s hs0 δ →
          (∀ℓ,hilbertSamuelAt
            (vanishingIdeal (n:=n) ((Subtype.val : presentationOpen PHS → ComplexModel n) ⁻¹' B)) x ℓ=R ℓ) →
          ActualHistoricalNativeFunctionPresentation S aFull wFull
            ((Subtype.val : presentationOpen PHS → ComplexModel n) ⁻¹' B)
            (initialWeightedRecord PHS η E) F₀ hF₀ id contMDiff_id x := by
  obtain ⟨P,s,hs0,hs,δ,hBound,hδ,hOpen,hZero,hSubset,hWords,hOwn,hPoints⟩:=
    exists_actual_initial_native_five_law_window B hspan PHS S hred hContact η E
  let aFull : Fin (historicalDegreePrefixCount (actualVertexWords n I) P.germs.degreeBound) ≃
      actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I):=
    (historicalDegreeFullLabelEquiv (actualVertexWords n I) P.germs.degreeBound hBound).trans
      (actualVertexEnumeration n I)
  let wFull:=historicalDegreePrefixWords (actualVertexWords n I) P.germs.degreeBound
  let r : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I) → ℂ:=
    fun v=>(s^weightedDegree (degLexWeight n P.germs.degreeBound) v.val)⁻¹
  let F₀:=fun v (x : presentationOpen PHS)=>r v*PHS.representatives v x.val
  have hF₀ : ∀v x,HolomorphicAt n (F₀ v) x:=scaled_native_function_holomorphic PHS r
  refine ⟨P,s,hs0,hs,δ,hBound,hδ,hOpen,hZero,hSubset,hWords,hOwn,hF₀,?_⟩
  intro x hx hHS
  obtain ⟨p,hp,hpx⟩:=historicalNativeJetWindow_coverage P s hs0 δ x.val hx
  obtain ⟨hdom,hu,hMembers,hSpan,hCompression,hFive⟩:=hPoints p hp
  let x' : presentationOpen PHS:=⟨scaledOriginalPoint P s p,hu⟩
  have hxx : x'=x:=Subtype.ext hpx
  let c:=fun i=>s^(degLexWeight n P.germs.degreeBound i)
  have hc : ∀i,c i≠0:=fun i=>pow_ne_zero _ hs0
  let Φ:=actualInitialAffineChart (presentationOpen PHS) x' c hc
  let hΦ0:=(actual_initial_affine_chart_geometry (presentationOpen PHS) x' c hc).2
  let Γ : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I) →
      HolGerm (ComplexModel n):=
    fun v=>actualInheritedTranslatedGerm P hs p hdom ((actualVertexEnumeration n I).symm v)
  have hProfile : ∀ℓ,hilbertSamuelAt
      (vanishingIdeal (n:=n) ((Subtype.val : presentationOpen PHS → ComplexModel n) ⁻¹' B)) x' ℓ=R ℓ := by
    rw [hxx]
    exact hHS
  have hAt : ActualHistoricalNativeFunctionPresentation S aFull wFull
      ((Subtype.val : presentationOpen PHS → ComplexModel n) ⁻¹' B)
      (initialWeightedRecord PHS η E) F₀ hF₀ id contMDiff_id x' := by
    refine ⟨Φ,(actual_initial_affine_chart_geometry (presentationOpen PHS) x' c hc).1,hΦ0,Γ,1,
      hFive hProfile,?_,hCompression,one_ne_zero,?_⟩
    · exact (congrArg Ideal.span (aFull.surjective.range_comp Γ)).trans hSpan
    · intro v
      rw [one_pow,one_mul]
      exact (scaled_affine_member PHS x' c hc r v).trans (hMembers v).symm
  exact hxx ▸ hAt

end
end Hironaka.HironakaActualHistoricalInitialFunctionWindow
