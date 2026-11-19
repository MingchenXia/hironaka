import Hironaka.Resolution.HironakaActualHistoricalSortedPrefixFrames
import Hironaka.Resolution.HironakaActualHistoricalMovingSelectedContact

/-! All FIVE initial moving point laws on the SAME originally produced
scale/family/window. Original labels are degree ordered ONCE, before p;
literal member equations and the ENTIRE actual scaled ideal are retained.
The actual native affine W/Q full-record realization is a separate layer. -/
set_option autoImplicit false
open Set Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualHistoricalInitialFiveLawWindow
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaActualHistoricalSortedPrefixFrames HironakaActualHistoricalMovingSelectedContact
  HironakaActualHistoricalMovingPrefixSupport HironakaActualHistoricalFormalSupportedDivision
  HironakaActualHistoricalWholeJetFrames HironakaActualHistoricalPrefixJetFrames
  HironakaActualHistoricalNormalizedWeakPresentation HironakaActualFixedInheritedSelector
  HironakaActualGeometricCurrentNeighborhoodHS HironakaActualRelativeNormalJetDivision
  HironakaActualNormalZeroAnalyticSaturation HironakaActualFormalInitialDiagram
  HironakaActualOriginalFormalHSTransfer HironakaActualCoefficientPresentationCentrePower
  HironakaRelativeNormalMonomialBasis HironakaActualCauchyMonomialDivision
  HironakaActualInheritedSmallTails HironakaActualOriginalScaledAnalyticDivision
  HironakaActualWeightedVertexSmallTails HironakaActualFiniteDegLexWeights
  HironakaHolomorphicJetChartInvariance HironakaActualDiagonalTaylor
  HironakaActualInheritedNestedContactFlag HironakaActualInheritedNeighborhoodStandardJets
  HironakaActualCauchyCoordinateDivision HironakaHolomorphicJetRankLoci

variable {n : ℕ} {I : Ideal (HolGerm (ComplexModel n))}
  {G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)}

/-- Genuine minimal vertices own their literal heads in ANY original
enumeration; no later moving-family division owner is selected. -/
theorem actual_initial_vertex_heads_have_historical_owner {k : ℕ}
    (m : MonomialOrder (Fin n)) (K : Ideal (MvPowerSeries (Fin n) ℂ))
    (a : Fin k ≃ actualInitialVertices m K) (w : Fin k → CoordinateWord n)
    (hw : ∀i,wordExponent (w i)=(a i).val) :
    ∀j,historicalOwner w (wordExponent (w j))=some j := by
  intro j
  apply (historicalOwner_eq_some_iff w _ j).mpr
  refine ⟨le_rfl,(avoidsCones_take_iff w j _).mpr ?_⟩
  intro i hij hle
  rw [hw i,hw j] at hle
  have hmi : Minimal (·∈actualInitialDiagram m K) (a i).val := by
    simpa only [actualInitialVertices,Set.Finite.mem_toFinset,Set.mem_ofPred_eq] using (a i).property
  have hmj : Minimal (·∈actualInitialDiagram m K) (a j).val := by
    simpa only [actualInitialVertices,Set.Finite.mem_toFinset,Set.mem_ofPred_eq] using (a j).property
  have he : (a i).val=(a j).val:=le_antisymm hle (hmj.2 hmi.1 hle)
  exact (ne_of_lt hij) (a.injective (Subtype.ext he))

/-- ORIGINAL actual source data choose ONE scale/window and ONE full
degree ordering BEFORE EVERY moving point, then prove ALL FIVE SAME
point laws with entire source analytic equations and whole formal ideal. -/
theorem exists_actual_initial_five_law_moving_window
    {A : GermIdeal n (ComplexModel n)} {R : ℕ → ℕ}
    (hspan : Ideal.span (range G.germs)=I)
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)))
    (hred : ∀r,ActualInheritedPrefixReducedAt G r)
    (hContact : ∀r,actualFixedSelectorContactAt S G.germs r) :
    ∃(P : ActualInheritedWeightedTailData G)(s : ℂ)(hs0 : s≠0)
      (hs : s∈Metric.ball 0 P.radius)(δ : ℝ)
      (hBound : ∀j : Fin (actualVertexCount n I),normalExponentDegree
        (wordExponent (actualVertexWords n I j))≤P.germs.degreeBound),
      0<δ ∧ IsOpen (historicalNativeJetWindow P s hs0 δ) ∧
      (0 : ComplexModel n)∈historicalNativeJetWindow P s hs0 δ ∧
      historicalNativeJetWindow P s hs0 δ⊆PHS.neighborhood ∧
      let pfull:=historicalDegreeFullLabelEquiv (actualVertexWords n I) P.germs.degreeBound hBound
      let aFull : Fin (historicalDegreePrefixCount (actualVertexWords n I) P.germs.degreeBound) ≃
        actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I):=
          pfull.trans (actualVertexEnumeration n I)
      let wFull:=historicalDegreePrefixWords (actualVertexWords n I) P.germs.degreeBound
      (∀j,wordExponent (wFull j)=(aFull j).val) ∧
      (∀j,historicalOwner wFull (wordExponent (wFull j))=some j) ∧
      ∀p∈Metric.ball (0 : CoordinateSpace n) δ,
        ∃hdom : MapsTo (fun z=>p+z) (Metric.ball 0 (P.radius/2)) (Metric.ball 0 P.radius),
        ∃hu : scaledOriginalPoint P s p∈PHS.neighborhood,
          (∀j : Fin (actualVertexCount n I),
            let v:=actualVertexEnumeration n I j
            let W:=degLexWeight n P.germs.degreeBound
            actualInheritedTranslatedGerm P hs p hdom j=
              HolGerm.constHom ((s^weightedDegree W v.val)⁻¹)*
                actualDiagonalPullback (fun i=>s^W i)
                  (translatedGerm (scaledOriginalPoint P s p) (PHS.representatives v)
                    (PHS.holomorphicAt _ hu v))) ∧
          actualHistoricalScaledFormalIdeal A (scaledOriginalPoint P s p)
              (fun i=>s^(degLexWeight n P.germs.degreeBound i))=
            Ideal.span (range fun j=>actualUnshiftedTaylorAlgHom n (actualInheritedTranslatedGerm P hs p hdom
              (historicalDegreePrefixLabel (actualVertexWords n I) P.germs.degreeBound j))) ∧
          ((∀ℓ,hilbertSamuelAt A (scaledOriginalPoint P s p) ℓ=R ℓ) →
            ActualHistoricalFivePointLaws S aFull wFull
              (fun v=>actualInheritedTranslatedGerm P hs p hdom ((actualVertexEnumeration n I).symm v))) := by
  have hFormal:=exists_actual_geometric_historical_formal_presentation_neighbourhood hspan PHS
  have hSupported:=exists_actual_geometric_historical_supported_presentation_neighbourhood PHS hFormal hred
  obtain ⟨P,s,hs0,hs,δ,hδ,hOpen,hZero,hSubset,hPoints⟩:=
    exists_actual_geometric_historical_contact_presentation_neighbourhood PHS S hSupported hContact
  have hBound : ∀j : Fin (actualVertexCount n I),normalExponentDegree
      (wordExponent (actualVertexWords n I j))≤P.germs.degreeBound := by
    intro j
    simpa only [actualVertexWords,wordExponent_wordOfExponent] using P.germs.degree_le (actualVertexEnumeration n I j)
  let w0:=actualVertexWords n I
  let M:=P.germs.degreeBound
  let pfull:=historicalDegreeFullLabelEquiv w0 M hBound
  let aFull : Fin (historicalDegreePrefixCount w0 M) ≃
      actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I):=
    pfull.trans (actualVertexEnumeration n I)
  let wFull:=historicalDegreePrefixWords w0 M
  have hWords (j : Fin (historicalDegreePrefixCount w0 M)) : wordExponent (wFull j)=(aFull j).val := by
    let v:=actualVertexEnumeration n I (historicalDegreePrefixLabel w0 M j)
    change wordExponent (wordOfExponent v.val)=v.val
    exact wordExponent_wordOfExponent v.val
  have hSorted : StrictMono (fun j=>historicalDegreeKey w0 (pfull j)):=
    historicalDegreePrefixLabel_strictMono w0 M
  have hFullWords : wFull=fun j=>w0 (pfull j):=rfl
  have hOwn:=actual_initial_vertex_heads_have_historical_owner MonomialOrder.degLex
    (analyticZeroTaylorIdeal n I) aFull wFull hWords
  refine ⟨P,s,hs0,hs,δ,hBound,hδ,hOpen,hZero,hSubset,hWords,hOwn,?_⟩
  intro p hp
  obtain ⟨hdom,hu,hCov,hIdeal,hPrefix,hPhase,hMovingContact⟩:=hPoints p hp
  refine ⟨hdom,hu,hCov,hIdeal,?_⟩
  intro hHS
  obtain ⟨_hExact,hMarked,hFrames,hDivision⟩:=hPhase hHS
  let Γ : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I) →
      HolGerm (ComplexModel n):=
    fun v=>actualInheritedTranslatedGerm P hs p hdom ((actualVertexEnumeration n I).symm v)
  let F:=actualInheritedTranslatedGerm P hs p hdom
  let g:=fun j=>actualUnshiftedTaylorAlgHom n (F j)
  have hReindex (j : Fin (historicalDegreePrefixCount w0 M)) : Γ (aFull j)=F (pfull j) := by
    change F ((actualVertexEnumeration n I).symm ((actualVertexEnumeration n I) (pfull j)))=F (pfull j)
    exact congrArg F ((actualVertexEnumeration n I).symm_apply_apply (pfull j))
  have hGerms : (fun j=>actualUnshiftedTaylorAlgHom n (Γ (aFull j)))=fun j=>g (pfull j):=
    funext fun j=>congrArg (actualUnshiftedTaylorAlgHom n) (hReindex j)
  change ActualHistoricalFivePointLaws S aFull wFull Γ
  refine ⟨?_,?_,?_,?_,hMovingContact hHS,hPrefix⟩
  · intro j
    rw [hReindex j]
    change actualUnshiftedTaylorAlgHom n (F (pfull j))∈
        genuineFormalVariables n^normalExponentDegree (wordExponent (w0 (pfull j))) ∧
      actualUnshiftedTaylorAlgHom n (F (pfull j))∉
        genuineFormalVariables n^(normalExponentDegree (wordExponent (w0 (pfull j)))+1)
    exact hMarked (pfull j)
  · rw [hGerms]
    exact (hFrames M).1
  · rw [hGerms,hFullWords]
    exact historical_sorted_reindex_prefix_frames w0 g pfull hSorted hFrames
  · rw [hGerms]
    exact hDivision

end
end Hironaka.HironakaActualHistoricalInitialFiveLawWindow
