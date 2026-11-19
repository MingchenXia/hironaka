import Hironaka.Resolution.HironakaActualAnalyticSourceNormalizedTransport
import Hironaka.Resolution.HironakaActualGlobalInheritedCut

/-! The geometric strict stalk in a supplied actual normal chart becomes the
produced adapted current analytic family. Both the whole geometric ideal
comparison and every current monic/prefix certificate are internally proved.
Only one genuine step, with retained actual member orders, is asserted. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualGeometricAdaptedCurrentFamily
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
 OkaRelationSheaf HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetMonomialSpan
 HironakaHolomorphicPointJets HironakaActualAnalyticBlowupTaylor
 HironakaActualPointGeometricBennett BlowupFlatCoordinates HironakaActualLocalStrictSaturation
 HironakaActualStrictContactBlowupCoordinates HironakaActualFixedFlatteningHSComparison
 HironakaActualCoefficientPresentationCentrePower HironakaActualNormalAllDirectionAnalyticSaturation
 HironakaRelativeNormalMonomialBasis HironakaActualFormalInitialDiagram
 HironakaActualRelativeNormalJetDivision HironakaActualInheritedNestedContactFlag
 HironakaActualNormalZeroAnalyticSaturation HironakaActualAnalyticAdaptedCurrentFamily
 HironakaActualAnalyticSourceNormalizedTransport HironakaActualInheritedSourcePermutationFamily
 HironakaActualNormalMarkedDirection HironakaActualOriginalFormalTaylor
 HironakaActualAnalyticStrictGenerators HironakaActualRelativeStandardnessBlockSupport
 HironakaRelativeNormalDeformationInitialRelations HironakaActualCoefficientAnalyticBlowup
 HironakaRelativeNormalCoherentTranslatedJets
 HironakaSmoothCentreCoherentDomain HironakaSmoothCentreNearbyStalks
section Geometric
variable {d t : ℕ} {X Z : Type u} [TopologicalSpace X] [TopologicalSpace Z]
 [ChartedSpace (ComplexModel (d+t)) X] [ChartedSpace (ComplexModel (d+t)) Z]
 [IsComplexManifold (d+t) X] [IsComplexManifold (d+t) Z]

/-- The entire geometric strict stalk equals the independently named
normalized-original-member ideal in the SAME supplied actual chart. -/
theorem actual_geometric_strict_stalk_eq_normalized_ideal
    (ht : 2≤t) (π : Z → X)
    (hπ : ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ComplexModel (d+t)) ∞ π)
    (y : Z) (W : Set X) (hW : (vanishingIdeal (n:=d+t) W).IsCoherent)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) (π y) (π y)))
    (hΦsrc : Φ.source⊆(chartAt (ComplexModel (d+t)) (π y)).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel (d+t)) (π y) (π y))=0)
    (e : Fin (d+t)) (he : d≤e.val) (b : Fin (d+t) → ℂ)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) y y))
    (hΘsrc : Θ.source⊆(chartAt (ComplexModel (d+t)) y).target)
    (hΘ0 : Θ.toFun (chartAt (ComplexModel (d+t)) y y)=0)
    (hnormal : ∀z : Z,z∈(chartAt (ComplexModel (d+t)) y).source →
      chartAt (ComplexModel (d+t)) y z∈Θ.source →
      π z∈flatDomain Φ ∧ Φ.toFun (chartAt (ComplexModel (d+t)) (π y) (π z))=
        actualAnalyticBlowupMap (actualTangentCentreVariables d t) e b
          (Θ.toFun (chartAt (ComplexModel (d+t)) y z)))
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (hI : I=originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
      (actualFlattenedOriginalSheaf (vanishingIdeal (n:=d+t) W) (π y) Φ) 0))
    (G : ActualAnalyticInheritedFamily (d+t) 0 (analyticZeroTaylorIdeal (d+t) I))
    (hmem : ∀a,G.germs a∈I)
    (hp : ∀a,G.germs a∈actualAnalyticCoordinateIdeal (actualTangentCentreVariables d t)^normalExponentDegree a.val)
    (H : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+t) I) → HolGerm (ComplexModel (d+t)))
    (hH : ∀a,coordinateGerm e^normalExponentDegree a.val*H a=
      actualAnalyticBlowupPullback (actualTangentCentreVariables d t) e b (G.germs a))
    (hOrder : ∀a,H a∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t)))^normalExponentDegree a.val) :
    let K:=originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
      (actualFlattenedOriginalSheaf (vanishingIdeal (n:=d+t) (strictTransform (d+t) π W)) y Θ) 0)
    K=actualAnalyticNormalizedMemberIdeal I (actualTangentCentreVariables d t) e b ∧
      ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=d+t) (strictTransform (d+t) π W)) y ℓ=
        hilbertSamuelAt (vanishingIdeal (n:=d+t) W) (π y) ℓ := by
  let q : Fin (d+t):=⟨d,by omega⟩
  let j : Fin t:=⟨e.val-d,by have hlt:=e.isLt;omega⟩
  have hj : j.natAdd d=e := by apply Fin.ext;dsimp only [j,Fin.natAdd];omega
  have hTail : actualTangentCentreVariables d t=Set.Ici q := by
    rw [actualTangentCentreVariables_eq_tail];rfl
  have hPower : ∀a,G.germs a∈actualAnalyticCoordinateIdeal (Set.Ici q)^normalExponentDegree a.val := by
    simpa only [hTail] using hp
  have hEq (a) : sameAnalyticNormalNormalizedVertex (d+t) I G q e he b hPower a=H a := by
    apply mul_left_cancel₀ (pow_ne_zero (normalExponentDegree a.val)
      (HolomorphicGermReducednessBridge.coordinate_germ_ne_zero e))
    exact (sameAnalyticNormalNormalizedVertex_product (d+t) I G q e he b hPower a).trans
      (by simpa only [hTail,coordinateGerm] using (hH a).symm)
  have hFun : sameAnalyticNormalNormalizedVertex (d+t) I G q e he b hPower=H:=funext hEq
  have hOrders : ∀a,sameAnalyticNormalNormalizedVertex (d+t) I G q e he b hPower a∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t)))^normalExponentDegree a.val := by
    simpa only [hFun] using hOrder
  obtain ⟨_M,_hBound,_hColon,hSat,hHS⟩:=
    exists_same_normal_analytic_fixed_colon_and_hs_of_marked_orders (d+t) I G hmem q e he b hPower hOrders
  have hA : actualTangentCentreVariables d t={i : Fin (d+t) | d ≤ i.val}:=actualTangentCentreVariables_eq_tail d t
  have hnormal' : ∀z : Z,z∈(chartAt (ComplexModel (d+t)) y).source →
      chartAt (ComplexModel (d+t)) y z∈Θ.source →
      π z∈flatDomain Φ ∧ Φ.toFun (chartAt (ComplexModel (d+t)) (π y) (π z))=
        actualAnalyticBlowupMap {i : Fin (d+t) | d ≤ i.val} e b
          (Θ.toFun (chartAt (ComplexModel (d+t)) y z)) := by simpa only [hA] using hnormal
  have hchart:=strictFlattenedOriginIdeal_eq_model hπ y d Φ hΦsrc e b Θ hΘsrc hΘ0 hnormal' W
  rw [←hA,←hj] at hchart
  have hK : originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
      (actualFlattenedOriginalSheaf (vanishingIdeal (n:=d+t) (strictTransform (d+t) π W)) y Θ) 0)=
      sameAnalyticNormalNormalizedIdeal (d+t) I G q e he b hPower := by
    ext g
    rw [hchart,mem_fixedFlattening_strict_iff_power ht j b W hW (π y) Φ hΦsrc hΦ0]
    rw [←hI]
    simpa only [hj,hTail] using (hSat g).symm
  refine ⟨?_,?_⟩
  · rw [hTail,actualAnalyticNormalizedMemberIdeal_eq_same_normal_span (d+t) I G hmem q e he b hPower]
    exact hK
  · intro ℓ
    have hTarget:=hilbertSamuelAt_strict_eq_fixedFlattening_model hπ y d Φ hΦsrc e b Θ hΘsrc hΘ0 hnormal' W ℓ
    rw [←hA,←hj,hilbertSamuelAt_model_zero,←hchart,hK] at hTarget
    rw [hTarget,hHS]
    rw [hilbertSamuelAt_eq_fixedFlattening_model (π y) Φ hΦsrc hΦ0 W ℓ,
      hilbertSamuelAt_model_zero,←originalFlattenedVanishingOriginIdeal_eq_model (π y) Φ hΦsrc hΦ0,←hI]
end Geometric

section AdaptedGeometric
variable {d t : ℕ} {X Z : Type u} [TopologicalSpace X] [TopologicalSpace Z]
 [ChartedSpace (ComplexModel (d+(t+2))) X] [ChartedSpace (ComplexModel (d+(t+2))) Z]
 [IsComplexManifold (d+(t+2)) X] [IsComplexManifold (d+(t+2)) Z]

/-- A produced current analytic family generates the image of the ENTIRE
genuine geometric strict stalk under the internally constructed target germ
equivalence. The geometric comparison, source adaptation and all target
monic/whole-prefix certificates are outputs. -/
theorem exists_actual_geometric_adapted_current_family
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
    (hred : ∀k,ActualInheritedPrefixReducedAt G k) :
    let q : Fin (d+(t+2)):=⟨d,by omega⟩
    ∀hp : ∀a,G.germs a∈actualAnalyticCoordinateIdeal (Set.Ici q)^normalExponentDegree a.val,
    (∀a,sameAnalyticNormalNormalizedVertex (d+(t+2)) I G q e he b hp a∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+(t+2))))^normalExponentDegree a.val) →
    let K:=originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
      (actualFlattenedOriginalSheaf (vanishingIdeal (n:=d+(t+2)) (strictTransform (d+(t+2)) π W)) y Θ) 0)
    ∃f : Fin (d+(t+2)),∃_hqf : q≤f,actualNormalMarkedDirection (Set.Ici q) e b f≠0 ∧
      ∃C : HolGerm (ComplexModel (d+(t+2)))≃ₐ[ℂ]HolGerm (ComplexModel (d+(t+2))),
      let IS:=actualAnalyticNormalAdaptedSourceIdeal I q e f b
      ∃GS : ActualAnalyticInheritedFamily (d+(t+2)) 0 (analyticZeroTaylorIdeal (d+(t+2)) IS),
      ∃ES : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+(t+2)) I) ≃
          actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+(t+2)) IS),
      (∀a,(ES a).val=Finsupp.domCongr (HironakaActualRelativeStandardnessNormalPivotPriority.normalPivotEquiv q f) a.val) ∧
      (∀a,GS.germs (ES a)=HironakaActualFixedInheritedSelectorPermutation.actualPermutationGermEquiv
        (HironakaActualRelativeStandardnessNormalPivotPriority.normalPivotEquiv q f)
        (HironakaActualAnalyticDirectionRemovalQuotient.actualAnalyticDirectionShearGermEquiv (Set.Ici q) f
          (fun i=>actualNormalMarkedDirection (Set.Ici q) e b i /
            actualNormalMarkedDirection (Set.Ici q) e b f) (G.germs a))) ∧
      (∀a,GS.germs a∈IS) ∧ (∀k,ActualInheritedPrefixReducedAt GS k) ∧
      ∃hpS : ∀a,GS.germs a∈actualAnalyticCoordinateIdeal (Set.Ici q)^normalExponentDegree a.val,
      (∀a,sameAnalyticZeroNormalizedVertex (d+(t+2)) IS GS q hpS a∈
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+(t+2))))^normalExponentDegree a.val) ∧
      let J:=sameAnalyticZeroNormalizedIdeal (d+(t+2)) IS GS q hpS
      Ideal.map C.toRingEquiv.toRingHom K=J ∧
      actualInitialDiagram MonomialOrder.degLex (analyticZeroTaylorIdeal (d+(t+2)) J)=
        actualInitialDiagram MonomialOrder.degLex (analyticZeroTaylorIdeal (d+(t+2)) IS) ∧
      ∃hV : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+(t+2)) IS)=
          actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+(t+2)) J),
      ∃GT : ActualAnalyticInheritedFamily (d+(t+2)) 0 (analyticZeroTaylorIdeal (d+(t+2)) J),
      (∀a,GT.germs (sourceVertexSetCast hV a)=sameAnalyticZeroNormalizedVertex (d+(t+2)) IS GS q hpS a) ∧
      Ideal.span (range GT.germs)=J ∧ (∀a,GT.germs a∈J) ∧
      (∀k,ActualInheritedPrefixReducedAt GT k) ∧
      (∀ℓ,hilbertSamuelValue J ℓ=hilbertSamuelValue I ℓ) ∧
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
  obtain ⟨f,hqf,hvf,GS,ES,hES,hLiteral,hMember,hPrefix,hpS,hOrdS,hD,hV,GT,hGT,hSpan,hMT,hPT,hHS⟩:=
    exists_actual_analytic_adapted_current_family I G hmem q e he b hp hOrder hred
  obtain ⟨C,hC⟩:=exists_actual_original_to_adapted_normalized_ideal_transport q e f he hqf b hvf
  refine ⟨f,hqf,hvf,C,GS,ES,hES,hLiteral,hMember,hPrefix,hpS,hOrdS,?_,hD,hV,GT,hGT,hSpan,hMT,hPT,hHS,hIntrinsic⟩
  rw [hK]
  exact (hC I).trans (actualAnalyticNormalizedMemberIdeal_eq_same_zero_span
    (d+(t+2)) _ GS hMember q hpS)
end AdaptedGeometric
end
end Hironaka.HironakaActualGeometricAdaptedCurrentFamily
