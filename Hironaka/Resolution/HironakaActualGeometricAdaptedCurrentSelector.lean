import Hironaka.Resolution.HironakaActualGeometricAdaptedCurrentFamily
import Hironaka.Resolution.HironakaActualAnalyticAdaptedCurrentSelector
import Hironaka.Resolution.HironakaActualRepeatedZeroCurrentSources

/-! One produced CURRENT source is attached to the SAME actual geometric
strict stalk and the literal transported historical selector. No current
family, diagram, contact, ideal comparison or next source state is supplied. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualGeometricAdaptedCurrentSelector
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
 HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetMonomialSpan HironakaHolomorphicPointJets
 HironakaActualAnalyticBlowupTaylor HironakaActualCoefficientPresentationCentrePower
 HironakaRelativeNormalMonomialBasis HironakaActualFormalInitialDiagram HironakaActualRelativeNormalJetDivision
 HironakaActualInheritedNestedContactFlag HironakaActualNormalZeroAnalyticSaturation
 HironakaActualNormalAllDirectionAnalyticSaturation HironakaActualAnalyticAdaptedCurrentFamily
 HironakaActualAnalyticSourceNormalizedTransport HironakaActualInheritedSourcePermutationFamily
 HironakaActualNormalMarkedDirection HironakaActualAnalyticStrictGenerators
 HironakaRelativeNormalDeformationInitialRelations HironakaActualCoefficientAnalyticBlowup
 HironakaRelativeNormalCoherentTranslatedJets HironakaSmoothCentreCoherentDomain
 HironakaSmoothCentreNearbyStalks BlowupFlatCoordinates HironakaActualFixedInheritedSelector
 HironakaActualGeometricAdaptedCurrentFamily HironakaActualAnalyticAdaptedCurrentSelector
 HironakaActualRepeatedZeroCurrentSources HironakaActualFixedInheritedSelectorPermutation
 HironakaActualRelativeStandardnessNormalPivotPriority
variable {n : ℕ}

/-- The current source uses exactly the produced target family and the
literal permutation/casts of the original historical selector. -/
def actualAdaptedHistoricalCurrentSource
    {I : Ideal (HolGerm (ComplexModel (n+1)))}
    {G : ActualAnalyticInheritedFamily (n+1) 0 (analyticZeroTaylorIdeal (n+1) I)}
    {q e f : Fin (n+1)} {b : Fin (n+1) → ℂ}
    {S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) I))}
    (D : ActualAdaptedCurrentSelectorData I G q e f b S) : ActualZeroCurrentSource (n+1) where
  ideal:=sameAnalyticZeroNormalizedIdeal (n+1) _ D.sourceFamily q D.sourcePower
  family:=D.targetFamily
  member:=D.targetMember
  wholePrefix:=D.targetPrefix
  selector:=sourceFixedSelectorCast D.targetVertexSet
    (sourceFixedSelectorCast D.permutationVertexSet (actualFixedSelectorPermutation (normalPivotEquiv q f) S))
  contact:=D.targetContact

section Geometric
variable {d t : ℕ} {X Z : Type u} [TopologicalSpace X] [TopologicalSpace Z]
 [ChartedSpace (ComplexModel (d+(t+2))) X] [ChartedSpace (ComplexModel (d+(t+2))) Z]
 [IsComplexManifold (d+(t+2)) X] [IsComplexManifold (d+(t+2)) Z]

theorem exists_actual_geometric_current_source_and_historical_selector
    (π : Z → X)
    (hπ : ContMDiff 𝓘(ℂ,ComplexModel (d+(t+2))) 𝓘(ℂ,ComplexModel (d+(t+2))) ∞ π)
    (y : Z) (W : Set X) (hW : (vanishingIdeal (n:=d+(t+2)) W).IsCoherent)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+(t+2))) (π y) (π y)))
    (hΦsrc : Φ.source⊆(chartAt (ComplexModel (d+(t+2))) (π y)).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel (d+(t+2))) (π y) (π y))=0)
    (e : Fin (d+(t+2))) (he : d≤e.val) (b : Fin (d+(t+2)) → ℂ)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+(t+2))) y y))
    (hΘsrc : Θ.source⊆(chartAt (ComplexModel (d+(t+2))) y).target)
    (hΘ0 : Θ.toFun (chartAt (ComplexModel (d+(t+2))) y y)=0)
    (hnormal : ∀z : Z,z∈(chartAt (ComplexModel (d+(t+2))) y).source →
      chartAt (ComplexModel (d+(t+2))) y z∈Θ.source →
      π z∈flatDomain Φ ∧ Φ.toFun (chartAt (ComplexModel (d+(t+2))) (π y) (π z))=
        actualAnalyticBlowupMap (actualTangentCentreVariables d (t+2)) e b
          (Θ.toFun (chartAt (ComplexModel (d+(t+2))) y z)))
    (I : Ideal (HolGerm (ComplexModel (d+(t+2)))))
    (hI : I=originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
      (actualFlattenedOriginalSheaf (vanishingIdeal (n:=d+(t+2)) W) (π y) Φ) 0))
    (G : ActualAnalyticInheritedFamily (d+(t+2)) 0 (analyticZeroTaylorIdeal (d+(t+2)) I))
    (hmem : ∀a,G.germs a∈I)
    (hred : ∀k,ActualInheritedPrefixReducedAt G k)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+(t+2)) I)))
    (hContact : ∀k,actualFixedSelectorContactAt S G.germs k) :
    let q : Fin (d+(t+2)):=⟨d,by omega⟩
    ∀hp : ∀a,G.germs a∈actualAnalyticCoordinateIdeal (Set.Ici q)^normalExponentDegree a.val,
    (∀a,sameAnalyticNormalNormalizedVertex (d+(t+2)) I G q e he b hp a∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+(t+2))))^normalExponentDegree a.val) →
    let K:=originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
      (actualFlattenedOriginalSheaf (vanishingIdeal (n:=d+(t+2)) (strictTransform (d+(t+2)) π W)) y Θ) 0)
    ∃f : Fin (d+(t+2)),∃_hqf : q≤f,actualNormalMarkedDirection (Set.Ici q) e b f≠0 ∧
      ∃C : HolGerm (ComplexModel (d+(t+2)))≃ₐ[ℂ]HolGerm (ComplexModel (d+(t+2))),
      ∃D : ActualAdaptedCurrentSelectorData I G q e f b S,
        (actualAdaptedHistoricalCurrentSource D).ideal=Ideal.map C.toRingEquiv.toRingHom K ∧
        (∀ℓ,hilbertSamuelValue (actualAdaptedHistoricalCurrentSource D).ideal ℓ=hilbertSamuelValue I ℓ) ∧
        ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=d+(t+2)) (strictTransform (d+(t+2)) π W)) y ℓ=
          hilbertSamuelAt (vanishingIdeal (n:=d+(t+2)) W) (π y) ℓ := by
  dsimp only
  intro hp hOrder
  let q : Fin (d+(t+2)):=⟨d,by omega⟩
  have hTail : actualTangentCentreVariables d (t+2)=Set.Ici q := by
    rw [actualTangentCentreVariables_eq_tail]
    rfl
  have hpOld : ∀a,G.germs a∈actualAnalyticCoordinateIdeal (actualTangentCentreVariables d (t+2))^
      normalExponentDegree a.val := by simpa only [hTail] using hp
  have hProducts : ∀a,coordinateGerm e^normalExponentDegree a.val*
      sameAnalyticNormalNormalizedVertex (d+(t+2)) I G q e he b hp a=
      actualAnalyticBlowupPullback (actualTangentCentreVariables d (t+2)) e b (G.germs a) := by
    intro a
    simpa only [hTail] using sameAnalyticNormalNormalizedVertex_product (d+(t+2)) I G q e he b hp a
  obtain ⟨hK,hIntrinsic⟩:=actual_geometric_strict_stalk_eq_normalized_ideal (by omega)
    π hπ y W hW Φ hΦsrc hΦ0 e he b Θ hΘsrc hΘ0 hnormal I hI G hmem hpOld
    (sameAnalyticNormalNormalizedVertex (d+(t+2)) I G q e he b hp) hProducts hOrder
  rw [hTail] at hK
  obtain ⟨f,hqf,hvf,⟨D⟩⟩:=exists_actual_analytic_adapted_current_family_and_selector
    I G hmem q e he b hp hOrder hred S hContact
  obtain ⟨C,hC⟩:=exists_actual_original_to_adapted_normalized_ideal_transport q e f he hqf b hvf
  refine ⟨f,hqf,hvf,C,D,?_,D.targetHS,hIntrinsic⟩
  rw [hK]
  exact ((hC I).trans (actualAnalyticNormalizedMemberIdeal_eq_same_zero_span
    (d+(t+2)) _ D.sourceFamily D.sourceMember q D.sourcePower)).symm

end Geometric
end
end Hironaka.HironakaActualGeometricAdaptedCurrentSelector
