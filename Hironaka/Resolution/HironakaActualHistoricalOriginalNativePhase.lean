import Hironaka.Resolution.HironakaActualHistoricalInitialFunctionWindow
import Hironaka.Resolution.HironakaActualHistoricalNativeFunctionTower
import Hironaka.Resolution.HironakaActualCompactHSMaximalProfile
import Hironaka.Analytic.AnalyticSubsetPreimage

/-! Original-only finite native HS phase. The true source open is chosen
inside BOTH the actual initial all-five window and actual original HS upper
window BEFORE the finite canonical tower. The LITERAL original whole Q,
ALL boundary positions and fixed original F0/words/selector are retained.
Every GIVEN Q-test history is anchored and every GIVEN Q-resolution lowers
the original entire HS profile. Uniform successor windows/embedding and
many-phase smooth termination are explicitly separate. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualHistoricalOriginalNativePhase
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
  HironakaActualHistoricalInitialFunctionWindow HironakaActualHistoricalNativeFunctionTower
  HironakaActualHistoricalNativeFunctionSuccessor HironakaActualHistoricalNativeGivenTower
  HironakaActualHistoricalNativeStageStep HironakaActualHistoricalSortedPrefixFrames
  HironakaActualHistoricalWholeJetFrames HironakaActualHistoricalPrefixJetFrames
  HironakaActualGeometricCurrentNeighborhoodHS HironakaActualRelativeNormalJetDivision
  HironakaActualFixedInheritedSelector HironakaActualInheritedNestedContactFlag
  HironakaActualNormalZeroAnalyticSaturation HironakaActualFormalInitialDiagram
  HironakaActualInheritedSmallTails HironakaActualWeightedVertexSmallTails
  HironakaActualFiniteDegLexWeights HironakaActualCoefficientPresentationCentrePower
  HironakaActualCauchyMonomialDivision HironakaRelativeNormalMonomialBasis
  HironakaActualOriginalInitialHSPhase HironakaActualHistoricalHSMarkedDomain
  HironakaActualPrescribedCentreRebasing HironakaActualFixedFlatteningHSComparison
  HironakaSmoothCentreCoherentDomain HironakaRelativeNormalDeformationInitialRelations
  HironakaHolomorphicJetChartInvariance HironakaActualVanishingIntrinsicHSTransport
  HironakaActualCompactHSMaximalProfile HironakaSmoothSubmersionGermIdealColon
  HironakaActualWeightedCoefficientCompression HironakaActualOriginalFormalHSTransfer
  HironakaActualOriginalScaledAnalyticDivision
  HironakaEmbeddedAnalytic BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec NormalCrossings

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- ONLY original whole geometry initializes the anchored native phase
on a true relatively compact open chosen BEFORE any canonical tower. -/
theorem exists_actual_original_native_anchored_hs_phase
    (W : Set M) (hW : IsComplexAnalyticSubset (n:=n) W) (a₀ : M)
    (ha₀ : a₀∈singularSet (n:=n) W) (E : List (Set M)) (hE : IsSNCDivisor n E)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) a₀ a₀))
    (hΦsrc : Φ.source⊆(chartAt (ComplexModel n) a₀).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) a₀ a₀)=0) :
    ∃(Ψ : LocalHolomorphicEquivAt (n:=n) (0 : ComplexModel n))(hΨ0 : Ψ.toFun 0=0),
      let Ξ:=currentCoordinateFlattening a₀ Φ hΦ0 Ψ hΨ0
      let Bset:=actualFixedFlatteningSet a₀ Ξ W
      let I:=originalCoherentOriginIdeal (vanishingIdeal (n:=n) Bset)
      ∃(G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I))
        (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)))
        (PHS : ActualGeometricInheritedNeighborhoodHS (vanishingIdeal (n:=n) Bset) I G
          (fun ℓ=>hilbertSamuelAt (vanishingIdeal (n:=n) W) a₀ ℓ))
        (V : Opens M)(η : presentationOpen PHS ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ V),
        Ideal.span (range G.germs)=I ∧ PHS.neighborhood⊆Ξ.target ∧
        (∀z,(η z : M)=actualFlatteningInverseMap a₀ Ξ z.val) ∧
        ∃(P : ActualInheritedWeightedTailData G)(s : ℂ)(hs0 : s≠0)
          (_hs : s∈Metric.ball 0 P.radius)(δ : ℝ)
          (hBound : ∀j : Fin (actualVertexCount n I),normalExponentDegree
            (wordExponent (actualVertexWords n I j))≤P.germs.degreeBound),
          let aFull : Fin (historicalDegreePrefixCount (actualVertexWords n I) P.germs.degreeBound) ≃
            actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I):=
            (historicalDegreeFullLabelEquiv (actualVertexWords n I) P.germs.degreeBound hBound).trans
              (actualVertexEnumeration n I)
          let wFull:=historicalDegreePrefixWords (actualVertexWords n I) P.germs.degreeBound
          let F₀:=fun (v : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I))
            (x : presentationOpen PHS)=>
              (s^weightedDegree (degLexWeight n P.germs.degreeBound) v.val)⁻¹*PHS.representatives v x.val
          ∃hF₀ : ∀v x,HolomorphicAt n (F₀ v) x,
          ∃O : Opens (presentationOpen PHS),
            (⟨0,PHS.zero_mem⟩ : presentationOpen PHS)∈O ∧
            (∃K : Set (presentationOpen PHS),IsCompact K ∧ (O : Set (presentationOpen PHS))⊆K) ∧
            (∀x∈O,x.val∈historicalNativeJetWindow P s hs0 δ) ∧
            let ι : O → M:=fun x=>(η x.val : M)
            let Q:=MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : O → presentationOpen PHS)
              (initialWeightedRecord PHS (fun z=>(η z : M)) E)
            let Wphase:=(Subtype.val : O → presentationOpen PHS) ⁻¹'
              ((Subtype.val : presentationOpen PHS → ComplexModel n) ⁻¹' Bset)
            ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ ι ∧
            Topology.IsOpenEmbedding ι ∧ a₀∈range ι ∧
            IsInvDomain n Q ∧ Q.N=univ ∧ Q.E=E.map (ι ⁻¹' ·) ∧
            Q.d=weightedCommonMark (fun v : actualInitialVertices MonomialOrder.degLex
              (analyticZeroTaylorIdeal n I)=>normalExponentDegree v.val) ∧
            IsComplexAnalyticSubset (n:=n) Wphase ∧
            Q.cosupp={x | ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) Wphase) x ℓ=
              hilbertSamuelAt (vanishingIdeal (n:=n) W) a₀ ℓ} ∧
            (∀x ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) Wphase) x ℓ≤
              hilbertSamuelAt (vanishingIdeal (n:=n) W) a₀ ℓ) ∧
            (∃(Y : CMfd.{0} n)(T : BlowupTower (CMfd.of (n:=n) O) Y),
              IsCanonical Q ((CanonicalCentres.canonicalInvariant n).inv Q) T ∧ IsGeoResolution Q T) ∧
            (∀(Y : CMfd.{0} n)(T : BlowupTower (CMfd.of (n:=n) O) Y),IsGeoTestTower Q T →
              ActualNativeOriginalFunctionTowerHistory S aFull wFull Wphase Q F₀ hF₀
                (Subtype.val : O → presentationOpen PHS) contMDiff_subtype_val T) ∧
            (∀(Y : CMfd.{0} n)(T : BlowupTower (CMfd.of (n:=n) O) Y),IsGeoResolution Q T →
              ActualHistoricalNativeTowerCentres Wphase T ∧
              ∀z : Y,toLex (hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n T.proj Wphase)) z)<
                toLex (hilbertSamuelAt (vanishingIdeal (n:=n) W) a₀)) := by
  obtain ⟨Ψ,hΨ0,hΞsrc,hΞ0,G,S,PHS,hSpan,_hMem,hPositive,hRed,hContact,_hJac,hPHS,_hHS₀,
    V,η,_haV,hη,hCov,hDom,hCut,_hSing,_hZeroCut,hPhases⟩:=
    exists_original_initial_hs_phase W hW a₀ ha₀ E hE Φ hΦsrc hΦ0
  let Ξ:=currentCoordinateFlattening a₀ Φ hΦ0 Ψ hΨ0
  let Bset:=actualFixedFlatteningSet a₀ Ξ W
  let I:=originalCoherentOriginIdeal (vanishingIdeal (n:=n) Bset)
  let U₀:=presentationOpen PHS
  let Q₀:=initialWeightedRecord PHS (fun z=>(η z : M)) E
  let Wbase:=(Subtype.val : U₀ → ComplexModel n) ⁻¹' Bset
  let fMap : U₀ → M:=fun z=>(η z : M)
  have hMap : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ fMap:=
    contMDiff_subtype_val.comp η.contMDiff
  have hMapOpen : Topology.IsOpenEmbedding fMap:=
    V.isOpen.isOpenEmbedding_subtypeVal.comp η.toHomeomorph.isOpenEmbedding
  have hSet : Wbase=fMap ⁻¹' W := by
    ext z
    change (z.val∈Ξ.target ∧ actualFlatteningInverseMap a₀ Ξ z.val∈W) ↔ (η z : M)∈W
    rw [hη z]
    exact and_iff_right (hPHS z.property)
  have hWbase : IsComplexAnalyticSubset (n:=n) Wbase:=by
    rw [hSet]
    exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hMap hW
  let z₀ : U₀:=⟨0,PHS.zero_mem⟩
  have hMapZero : fMap z₀=a₀ := by
    change (η z₀ : M)=a₀
    rw [hη z₀]
    exact actualFlatteningInverseMap_zero a₀ Ξ hΞ0
  obtain ⟨P,s,hs0,hs,δ,hBound,_hδ,hWinOpen,hWinZero,_hWinSub,hWords,hOwn,hF₀,hInitialHistory⟩:=
    exists_actual_initial_native_original_function_window Bset hSpan PHS S hRed hContact fMap E
  let aFull : Fin (historicalDegreePrefixCount (actualVertexWords n I) P.germs.degreeBound) ≃
      actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I):=
    (historicalDegreeFullLabelEquiv (actualVertexWords n I) P.germs.degreeBound hBound).trans
      (actualVertexEnumeration n I)
  let wFull:=historicalDegreePrefixWords (actualVertexWords n I) P.germs.degreeBound
  let F₀:=fun (v : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)) (x : U₀)=>
    (s^weightedDegree (degLexWeight n P.germs.degreeBound) v.val)⁻¹*PHS.representatives v x.val
  obtain ⟨Uhs,haUhs,hUpperOriginal,_hLexUpper⟩:=exists_actual_entire_hs_pointwise_upper_window
    (vanishingIdeal (n:=n) W) (CartanIrreducible.cartanCoherence W hW) a₀
  let Allowed : Set U₀:=(Subtype.val : U₀ → ComplexModel n) ⁻¹' historicalNativeJetWindow P s hs0 δ ∩
    fMap ⁻¹' (Uhs : Set M)
  have hAllowedOpen : IsOpen Allowed:=
    (hWinOpen.preimage continuous_subtype_val).inter (Uhs.isOpen.preimage hMap.continuous)
  have hAllowedZero : z₀∈Allowed:=⟨hWinZero,by change fMap z₀∈Uhs;rw [hMapZero];exact haUhs⟩
  let : LocallyCompactSpace U₀:=U₀.isOpen.locallyCompactSpace
  obtain ⟨K,hKnhds,hK,_hKclosed⟩:=exists_mem_nhds_isCompact_isClosed z₀
  obtain ⟨Oset,hOsub,hOopen,hOzero⟩:=mem_nhds_iff.mp
    (inter_mem hKnhds (hAllowedOpen.mem_nhds hAllowedZero))
  let O : Opens U₀:=⟨Oset,hOopen⟩
  have hOK : (O : Set U₀)⊆K:=fun _ hx=>(hOsub hx).1
  have hOwindow : ∀x∈O,x.val∈historicalNativeJetWindow P s hs0 δ:=fun x hx=>(hOsub hx).2.1
  let Q:=MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : O → U₀) Q₀
  let Wphase:=(Subtype.val : O → U₀) ⁻¹' Wbase
  let ι : O → M:=fun x=>(η x.val : M)
  have hMapPhase : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ ι:=hMap.comp contMDiff_subtype_val
  have hOpenPhase : Topology.IsOpenEmbedding ι:=hMapOpen.comp O.isOpen.isOpenEmbedding_subtypeVal
  have haImage : a₀∈range ι:=⟨⟨z₀,hOzero⟩,hMapZero⟩
  have hDomPhase : IsInvDomain n Q:=InvDomainTowerAlong.isInvDomain_pullback_val O hDom
  have hQI : Q.ideal.IsCoherent:=hDomPhase.isWellFormed.isCoherent
  have hQN : Q.N=univ:=by change (Subtype.val : O → U₀) ⁻¹' univ=univ;exact preimage_univ
  have hQMark : Q.d=weightedCommonMark
      (fun v : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)=>normalExponentDegree v.val):=rfl
  have hBoundary : Q.E=E.map (ι ⁻¹' ·) := by
    change (E.map (fMap ⁻¹' ·)).map ((Subtype.val : O → U₀) ⁻¹' ·)=E.map (ι ⁻¹' ·)
    rw [List.map_map]
    rfl
  have hWphase : IsComplexAnalyticSubset (n:=n) Wphase:=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage contMDiff_subtype_val hWbase
  have hHSPhase (x : O) (ℓ : ℕ) : hilbertSamuelAt (vanishingIdeal (n:=n) Wphase) x ℓ=
      hilbertSamuelAt (vanishingIdeal (n:=n) W) (ι x) ℓ:=
    (hilbertSamuelAt_vanishing_actual_open_any O Wbase x ℓ).trans
      ((hilbertSamuelAt_vanishing_actual_open_any U₀ Bset x.val ℓ).trans (hCov x.val ℓ))
  have hCutPhase : Q.cosupp={x | ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) Wphase) x ℓ=
      hilbertSamuelAt (vanishingIdeal (n:=n) W) a₀ ℓ} := by
    change (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : O → U₀) Q₀).cosupp=_
    rw [MarkedIdealRestrictOpen.cosupp_pullback_val Q₀
      (fun _ _ hg=>holomorphicAt_of_mem_coherent Q₀.ideal hDom.isWellFormed.isCoherent hg) O,hCut]
    ext x
    change (∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) W) (ι x) ℓ=
      hilbertSamuelAt (vanishingIdeal (n:=n) W) a₀ ℓ) ↔
        ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) Wphase) x ℓ=
          hilbertSamuelAt (vanishingIdeal (n:=n) W) a₀ ℓ
    simp only [hHSPhase]
  have hUpperPhase (x : O) (ℓ : ℕ) : hilbertSamuelAt (vanishingIdeal (n:=n) Wphase) x ℓ≤
      hilbertSamuelAt (vanishingIdeal (n:=n) W) a₀ ℓ := by
    rw [hHSPhase]
    exact hUpperOriginal (ι x) (hOsub x.property).2.2 ℓ
  have hAnchored (x : O) (hx : x∈Q.cosupp) :
      ActualHistoricalNativeFunctionPresentation S aFull wFull Wphase Q F₀ hF₀
        (Subtype.val : O → U₀) contMDiff_subtype_val x := by
    have hProfilePhase : ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) Wphase) x ℓ=
        hilbertSamuelAt (vanishingIdeal (n:=n) W) a₀ ℓ := by
      rw [hCutPhase] at hx
      exact hx
    have hProfileBase : ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) Wbase) x.val ℓ=
        hilbertSamuelAt (vanishingIdeal (n:=n) W) a₀ ℓ:=fun ℓ=>
      (hilbertSamuelAt_vanishing_actual_open_any O Wbase x ℓ).symm.trans (hProfilePhase ℓ)
    have hAtBase:=hInitialHistory x.val (hOwindow x.val x.property) hProfileBase
    exact actual_native_original_function_open_restriction S aFull wFull Wbase
      (CartanIrreducible.cartanCoherence Wbase hWbase) Q₀ hDom.isWellFormed.isCoherent O x
        F₀ hF₀ id contMDiff_id hAtBase
  have hPoint (x : O) (hx : x∈Q.cosupp) : ActualHistoricalNativePointPresentation S aFull wFull Wphase Q x := by
    obtain ⟨Θ,hΘsrc,hΘ0,Γ,_d,hFive,hSpanAt,hCompAt,_hd,_hEq⟩:=hAnchored x hx
    exact ⟨Θ,hΘsrc,hΘ0,Γ,hFive,hSpanAt,hCompAt⟩
  obtain ⟨Y,T,hCan,hRes⟩:=hPhases K hK O hOK
  refine ⟨Ψ,hΨ0,G,S,PHS,V,η,hSpan,hPHS,hη,P,s,hs0,hs,δ,hBound,hF₀,O,hOzero,⟨K,hK,hOK⟩,hOwindow,
    hMapPhase,hOpenPhase,haImage,hDomPhase,hQN,hBoundary,hQMark,hWphase,hCutPhase,hUpperPhase,
    ⟨Y,T,hCan,hRes⟩,?_,?_⟩
  · intro Y' T' hTest
    exact actual_native_given_test_tower_original_functions W hW a₀ ha₀ Wphase hWphase Q hQN hQI
      S aFull wFull hWords hPositive hOwn hQMark hCutPhase hUpperPhase F₀ hF₀
        (Subtype.val : O → U₀) contMDiff_subtype_val hAnchored T' hTest
  · intro Y' T' hResolution
    exact actual_native_given_resolution_terminal_hs_drop W hW a₀ ha₀ Wphase hWphase Q hQN hQI
      S aFull wFull hWords hPositive hOwn hQMark hCutPhase hUpperPhase hPoint T' hResolution

end
end Hironaka.HironakaActualHistoricalOriginalNativePhase
