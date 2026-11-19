import Hironaka.Resolution.HironakaActualHistoricalInitialAffineDictionary
import Hironaka.Resolution.HironakaActualHistoricalInitialFiveLawWindow
import Hironaka.Resolution.HironakaActualHistoricalNativeStageStep

/-! The actual initial native moving base, using ONE original P/s/family,
fixed sorted original words and the LITERAL original weighted record.
Both entire native W/Q ideals are derived from SAME source functions.
This does not assert original function/unit histories or GIVEN-Q CAN
embedding compatibility; the finite-phase open restriction is separate. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualHistoricalInitialNativePointWindow
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaActualHistoricalInitialAffineDictionary HironakaActualHistoricalInitialFiveLawWindow
  HironakaActualHistoricalNativeStageStep HironakaActualHistoricalSortedPrefixFrames
  HironakaActualHistoricalWholeJetFrames HironakaActualHistoricalPrefixJetFrames
  HironakaActualHistoricalNormalizedWeakPresentation HironakaActualHistoricalFormalSupportedDivision
  HironakaActualHistoricalMovingPrefixSupport HironakaActualHistoricalMovingSelectedContact
  HironakaActualGeometricCurrentNeighborhoodHS HironakaActualRelativeNormalJetDivision
  HironakaActualFixedInheritedSelector HironakaActualInheritedNestedContactFlag
  HironakaActualNormalZeroAnalyticSaturation HironakaActualFormalInitialDiagram
  HironakaActualOriginalFormalHSTransfer HironakaActualInheritedSmallTails
  HironakaActualInheritedNeighborhoodStandardJets HironakaActualCauchyCoordinateDivision
  HironakaActualWeightedVertexSmallTails HironakaActualFiniteDegLexWeights
  HironakaActualCoefficientPresentationCentrePower HironakaActualCauchyMonomialDivision
  HironakaRelativeNormalMonomialBasis HironakaActualOriginalScaledAnalyticDivision
  HironakaActualOriginalInitialHSPhase HironakaActualHistoricalHSMarkedDomain
  HironakaActualNativeSourceChartComposition HironakaSmoothSubmersionGermIdealColon
  HironakaActualWeightedCoefficientCompression HironakaActualVanishingIntrinsicHSTransport
  HironakaHolomorphicJetRankLoci HironakaActualDiagonalTaylor
  HironakaHolomorphicJetChartInvariance HironakaRelativeNormalDeformationInitialRelations
  HironakaRelativeNormalCoherentTranslatedJets HironakaSmoothCentreCoherentDomain

variable {n : ℕ} {I : Ideal (HolGerm (ComplexModel n))}
  {G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)}

/-- ORIGINAL whole source data produce the same literal native W/Q
ideals and ALL FIVE moving laws on ONE actual initial source window. -/
theorem exists_actual_initial_native_five_law_window
    (B : Set (ComplexModel n)) {R : ℕ → ℕ}
    (hspan : Ideal.span (range G.germs)=I)
    (PHS : ActualGeometricInheritedNeighborhoodHS (vanishingIdeal (n:=n) B) I G R)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)))
    (hred : ∀r,ActualInheritedPrefixReducedAt G r)
    (hContact : ∀r,actualFixedSelectorContactAt S G.germs r)
    {M : Type*} (η : presentationOpen PHS → M) (E : List (Set M)) :
    ∃(P : ActualInheritedWeightedTailData G)(s : ℂ)(hs0 : s≠0)
      (hs : s∈Metric.ball 0 P.radius)(δ : ℝ)
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
      (∀j,wordExponent (wFull j)=(aFull j).val) ∧
      (∀j,historicalOwner wFull (wordExponent (wFull j))=some j) ∧
      ∀p∈Metric.ball (0 : CoordinateSpace n) δ,
        ∃hdom : MapsTo (fun z=>p+z) (Metric.ball 0 (P.radius/2)) (Metric.ball 0 P.radius),
        ∃hu : scaledOriginalPoint P s p∈PHS.neighborhood,
          let x : presentationOpen PHS:=⟨scaledOriginalPoint P s p,hu⟩
          let c:=fun i=>s^(degLexWeight n P.germs.degreeBound i)
          let hc : ∀i,c i≠0:=fun _i=>pow_ne_zero _ hs0
          let Φ:=actualInitialAffineChart (presentationOpen PHS) x c hc
          let hΦ0:=(actual_initial_affine_chart_geometry (presentationOpen PHS) x c hc).2
          let Γ : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I) →
            HolGerm (ComplexModel n):=
            fun v=>actualInheritedTranslatedGerm P hs p hdom ((actualVertexEnumeration n I).symm v)
          (∀v,Γ v=HolGerm.constHom ((s^weightedDegree (degLexWeight n P.germs.degreeBound) v.val)⁻¹)*
            actualDiagonalPullback c (translatedGerm x.val (PHS.representatives v)
              (PHS.holomorphicAt _ hu v))) ∧
          Ideal.span (range Γ)=originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
            (actualFlattenedOriginalSheaf
              (vanishingIdeal (n:=n) ((Subtype.val : presentationOpen PHS → ComplexModel n) ⁻¹' B)) x Φ) 0) ∧
          adaptedIdeal (initialWeightedRecord PHS η E).ideal x Φ hΦ0=
            weightedCompression (fun v : actualInitialVertices MonomialOrder.degLex
              (analyticZeroTaylorIdeal n I)=>normalExponentDegree v.val) Γ ∧
          ((∀ℓ,hilbertSamuelAt
            (vanishingIdeal (n:=n) ((Subtype.val : presentationOpen PHS → ComplexModel n) ⁻¹' B)) x ℓ=R ℓ) →
            ActualHistoricalFivePointLaws S aFull wFull Γ) := by
  obtain ⟨P,s,hs0,hs,δ,hBound,hδ,hOpen,hZero,hSubset,hWords,hOwn,hPoints⟩:=
    exists_actual_initial_five_law_moving_window hspan PHS S hred hContact
  refine ⟨P,s,hs0,hs,δ,hBound,hδ,hOpen,hZero,hSubset,hWords,hOwn,?_⟩
  intro p hp
  obtain ⟨hdom,hu,hCov,_hFormal,hFive⟩:=hPoints p hp
  let x : presentationOpen PHS:=⟨scaledOriginalPoint P s p,hu⟩
  let c:=fun i=>s^(degLexWeight n P.germs.degreeBound i)
  have hc : ∀i,c i≠0:=fun i=>pow_ne_zero _ hs0
  let r : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I) → ℂ:=
    fun v=>(s^weightedDegree (degLexWeight n P.germs.degreeBound) v.val)⁻¹
  have hr : ∀v,r v≠0:=fun v=>inv_ne_zero (pow_ne_zero _ hs0)
  let Φ:=actualInitialAffineChart (presentationOpen PHS) x c hc
  let hΦ0:=(actual_initial_affine_chart_geometry (presentationOpen PHS) x c hc).2
  let Γ : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I) →
      HolGerm (ComplexModel n):=
    fun v=>actualInheritedTranslatedGerm P hs p hdom ((actualVertexEnumeration n I).symm v)
  let e0 : Fin (actualVertexCount n I) ≃
      actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I):=actualVertexEnumeration n I
  have hΓ (v) : Γ v=HolGerm.constHom (r v)*actualDiagonalPullback c
      (translatedGerm x.val (PHS.representatives v) (PHS.holomorphicAt _ hu v)) := by
    have h:=hCov (e0.symm v)
    change Γ v=HolGerm.constHom (r (e0 (e0.symm v)))*
      actualDiagonalPullback c (translatedGerm x.val
        (PHS.representatives (e0 (e0.symm v)))
        (PHS.holomorphicAt _ hu _)) at h
    simpa only [e0.apply_symm_apply] using h
  have hΓEq:=funext hΓ
  have hNative : (vanishingIdeal (n:=n)
      ((Subtype.val : presentationOpen PHS → ComplexModel n) ⁻¹' B)).IsCoherent := by
    rw [←SmoothCentreHomogeneity.pullback_val_vanishingIdeal]
    exact actual_initial_presentation_native_coherent PHS
  have hSpan:=actual_initial_affine_presentation_span PHS x c hc r hr
  rw [SmoothCentreHomogeneity.pullback_val_vanishingIdeal] at hSpan
  have hOrigin:=actual_original_translated_flattened_vanishing_origin_eq_adapted x Φ
    (actual_initial_affine_chart_geometry (presentationOpen PHS) x c hc).1 hΦ0 _ hNative
  have hQ:=(actual_initial_affine_weighted_record PHS η E x c hc r hr).1
  refine ⟨hdom,hu,hΓ,?_,?_,?_⟩
  · exact (congrArg Ideal.span (congrArg range hΓEq)).trans (hSpan.trans hOrigin.symm)
  · exact hQ.trans (congrArg (weightedCompression
      (fun v : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)=>
        normalExponentDegree v.val)) hΓEq.symm)
  · intro hHS
    apply hFive
    intro ℓ
    exact (hilbertSamuelAt_vanishing_actual_open_any (presentationOpen PHS) B x ℓ).symm.trans (hHS ℓ)

/-- Every actual point in ONE original window with the original entire
native HS profile has the real native stage point data for the SAME Q. -/
theorem exists_actual_initial_native_point_window
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
      (∀j,wordExponent (wFull j)=(aFull j).val) ∧
      (∀j,historicalOwner wFull (wordExponent (wFull j))=some j) ∧
      ∀x : presentationOpen PHS,x.val∈historicalNativeJetWindow P s hs0 δ →
        (∀ℓ,hilbertSamuelAt
          (vanishingIdeal (n:=n) ((Subtype.val : presentationOpen PHS → ComplexModel n) ⁻¹' B)) x ℓ=R ℓ) →
        ActualHistoricalNativePointPresentation S aFull wFull
          ((Subtype.val : presentationOpen PHS → ComplexModel n) ⁻¹' B)
          (initialWeightedRecord PHS η E) x := by
  obtain ⟨P,s,hs0,hs,δ,hBound,hδ,hOpen,hZero,hSubset,hWords,hOwn,hPoints⟩:=
    exists_actual_initial_native_five_law_window B hspan PHS S hred hContact η E
  let aFull : Fin (historicalDegreePrefixCount (actualVertexWords n I) P.germs.degreeBound) ≃
      actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I):=
    (historicalDegreeFullLabelEquiv (actualVertexWords n I) P.germs.degreeBound hBound).trans
      (actualVertexEnumeration n I)
  let wFull:=historicalDegreePrefixWords (actualVertexWords n I) P.germs.degreeBound
  refine ⟨P,s,hs0,hs,δ,hBound,hδ,hOpen,hZero,hSubset,hWords,hOwn,?_⟩
  intro x hx hHS
  obtain ⟨p,hp,hpx⟩:=historicalNativeJetWindow_coverage P s hs0 δ x.val hx
  obtain ⟨hdom,hu,_hMembers,hSpan,hCompression,hFive⟩:=hPoints p hp
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
  have hAt : ActualHistoricalNativePointPresentation S aFull wFull
      ((Subtype.val : presentationOpen PHS → ComplexModel n) ⁻¹' B)
      (initialWeightedRecord PHS η E) x' := by
    refine ⟨Φ,(actual_initial_affine_chart_geometry (presentationOpen PHS) x' c hc).1,hΦ0,Γ,
      hFive hProfile,?_,hCompression⟩
    exact (congrArg Ideal.span (aFull.surjective.range_comp Γ)).trans hSpan
  exact hxx ▸ hAt

end
end Hironaka.HironakaActualHistoricalInitialNativePointWindow
