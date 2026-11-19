import Hironaka.Resolution.HironakaActualGlobalInheritedCut
import Hironaka.Resolution.HironakaActualPersistentHSIdealRigidity
import Hironaka.Resolution.HironakaActualInheritedNormalMemberOrder

/-!
# Actual geometric persistence enters the unchanged inherited controlled cut

The geometric HS hypothesis concerns the true strict transform, before any
controlled-cut or target-presentation hypothesis. Reduced-centre powers and
the whole normalized/formal strict ideal comparison are produced internally.
Every actual quotient keeps its same original numerator, label and mark.

Blueprint: `hironaka-actual-geometric-persistent-inherited-cut-20261101.tex`.
-/

set_option autoImplicit false

open Set Filter Classical
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaActualGeometricPersistentInheritedCut

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicPointJets
  HironakaHolomorphicJetMonomialSpan HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalIdeal HironakaRelativeNormalDeformationInitialRelations
  HironakaActualOriginalFormalTaylor HironakaActualOriginalFormalHSTransfer
  HironakaActualUnshiftedInitialHSTransfer HironakaActualFormalInitialDiagram
  HironakaActualCoefficientPresentationCentrePower HironakaActualFormalCoordinatePowerDivision
  HironakaActualFormalStrictGenerators HironakaActualReducedFormalStandardBasis
  HironakaActualFormalBlowupMemberGeneration HironakaActualAnalyticBlowupTaylor
  HironakaActualRelativeNormalJetDivision HironakaActualInheritedNestedContactFlag
  HironakaActualCoefficientAnalyticBlowup
  HironakaActualCanonicalCentreCompatibility
  HironakaActualAnalyticStrictGenerators HironakaActualNormalZeroAnalyticSaturation
  HironakaActualNormalAllDirectionAnalyticSaturation HironakaActualInheritedNormalMemberOrder
  HironakaActualReducedCentreBennett HironakaActualPersistentHSIdealRigidity
  HironakaActualPointGeometricBennett HironakaActualFixedFlatteningHSComparison
  HironakaActualGlobalInheritedCut HironakaActualWeightedCoefficientCompression
  HironakaActualCoherentWeightedCoefficientMarked HironakaSmoothSubmersionGermIdealColon
  HironakaActualFiniteCoefficientIdeals HironakaSmoothCentreCoherentDomain
  HironakaRelativeNormalCoherentTranslatedJets GermIdealOrder InvertibleIdealQuotient
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupControlledTransform BlowupFlatCoordinates

/-- Whole GEOMETRIC HS equality forces every actual quotient of the SAME
inherited member into its ORIGINAL marked point power. No target order,
target diagram, reduced-centre data or controlled-cut premise is supplied. -/
theorem same_inherited_normal_orders_of_geometric_hs_eq
    (d t : ℕ) (W : Set (ComplexModel (d+(t+2))))
    (I : Ideal (HolGerm (ComplexModel (d+(t+2)))))
    (hI : I=originalCoherentOriginIdeal (vanishingIdeal (n:=d+(t+2)) W))
    (G : ActualAnalyticInheritedFamily (d+(t+2)) 0 (analyticZeroTaylorIdeal (d+(t+2)) I))
    (hmem : ∀ a, G.germs a∈I)
    (hp : ∀ a, G.germs a∈actualAnalyticCoordinateIdeal (actualTangentCentreVariables d (t+2))^
      normalExponentDegree a.val)
    (hred : ∀ k, ActualInheritedPrefixReducedAt G k)
    (e : Fin (d+(t+2))) (he : d≤e.val) (b : Fin (d+(t+2)) → ℂ)
    (hHS : ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n:=d+(t+2))
      (strictTransform (d+(t+2))
        (actualAnalyticBlowupMap (actualTangentCentreVariables d (t+2)) e b) W)) 0 ℓ=
      hilbertSamuelAt (vanishingIdeal (n:=d+(t+2)) W) 0 ℓ) :
    ∀ a (H : HolGerm (ComplexModel (d+(t+2)))),
      coordinateGerm e^normalExponentDegree a.val*H=
        actualAnalyticBlowupPullback (actualTangentCentreVariables d (t+2)) e b (G.germs a) →
      H∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+(t+2))))^normalExponentDegree a.val := by
  let n:=d+(t+2)
  let K:=analyticZeroTaylorIdeal n I
  let A:=actualTangentCentreVariables d (t+2)
  let q : Fin n:=⟨d,by omega⟩
  have hqe : q≤e:=he
  have hTail : A=Set.Ici q := by
    change actualTangentCentreVariables d (t+2)=Set.Ici q
    rw [actualTangentCentreVariables_eq_tail]
    rfl
  have hPower : ∀ a, G.germs a∈actualAnalyticCoordinateIdeal (Set.Ici q)^normalExponentDegree a.val := by
    intro a
    rw [←hTail]
    exact hp a
  let B:=analyticZeroMonicFamily n I G hmem
  have hB (a : actualInitialVertices MonomialOrder.degLex K) :
      B.series a∈actualFormalCoordinateIdeal n A^
        Finsupp.weight (actualCoordinateWeight A) a.val := by
    have hw : Finsupp.weight (actualCoordinateWeight A) a.val≤normalExponentDegree a.val := by
      rw [Finsupp.weight_eq_sum,normalExponentDegree]
      apply Finset.sum_le_sum
      intro i _hi
      by_cases hi : i∈A <;> simp [actualCoordinateWeight,hi]
    exact (Ideal.pow_le_pow_right hw)
      (actualTaylor_mem_coordinateCentre_pow A _ (G.germs a) (hp a))
  have hV:=actualReducedVertexSeries_mem_coordinate_power_of_family
    MonomialOrder.degLex K B A hB
  obtain ⟨P,hP⟩:=exists_actual_reduced_centre_vertex_data d (t+2) I hV
  let j : Fin (t+2):=⟨e.val-d,by have hlt:=e.isLt;omega⟩
  have hje : j.natAdd d=e := by
    apply Fin.ext
    dsimp only [j,Fin.natAdd]
    omega
  have hHSI : ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n:=n)
      (strictTransform n (actualAnalyticBlowupMap A (j.natAdd d) b) W)) 0 ℓ=
      hilbertSamuelValue I ℓ := by
    intro ℓ
    rw [hje]
    exact (hHS ℓ).trans (by rw [hilbertSamuelAt_model_zero,←hI])
  have hNorm:=actual_normalized_ideal_eq_geometric_of_persistent_hs
    d (t+2) (by omega) W I hI P hP j b hHSI
  rw [hje] at hNorm
  have hNormSame : actualAnalyticNormalizedMemberIdeal I A e b=
      sameAnalyticNormalNormalizedIdeal n I G q e hqe b hPower := by
    rw [hTail]
    exact actualAnalyticNormalizedMemberIdeal_eq_same_normal_span n I G hmem q e hqe b hPower
  have hSameHS (ℓ : ℕ) :
      hilbertSamuelValue (sameAnalyticNormalNormalizedIdeal n I G q e hqe b hPower) ℓ=
        hilbertSamuelValue I ℓ := by
    rw [←hNormSame,hNorm]
    simpa only [hilbertSamuelAt_model_zero,←hI] using hHS ℓ
  have hFormalHS (ℓ : ℕ) :
      genuineFormalHilbertSamuelValue n (actualFormalStrictTransform K (Set.Ici q) e hqe b) ℓ=
        genuineFormalHilbertSamuelValue n K ℓ := by
    calc
      _=hilbertSamuelValue (sameAnalyticNormalNormalizedIdeal n I G q e hqe b hPower) ℓ := by
        rw [hilbertSamuelValue_eq_actual_unshifted_formal_extension,
          map_sameAnalyticNormalNormalizedIdeal n I G hmem q e hqe b hPower]
      _=hilbertSamuelValue I ℓ:=hSameHS ℓ
      _=_:=hilbertSamuelValue_eq_actual_unshifted_formal_extension n I ℓ
  have hFormalOrders:=actual_normal_hs_equal_inherited_member_orders G
    (fun a=>Ideal.mem_map_of_mem _ (hmem a)) q e hqe b hPower hred hFormalHS
  have hOrders (a) : sameAnalyticNormalNormalizedVertex n I G q e hqe b hPower a∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^normalExponentDegree a.val := by
    apply (mem_analytic_ideal_iff_actualUnshifted_extension n _ _).mpr
    rw [map_actualUnshifted_maximal_pow,actualTaylor_sameAnalyticNormalNormalizedVertex]
    exact hFormalOrders a
  intro a H hProduct
  have hProductSame : coordinateGerm e^normalExponentDegree a.val*
      sameAnalyticNormalNormalizedVertex n I G q e hqe b hPower a=
        actualAnalyticBlowupPullback A e b (G.germs a) := by
    simpa only [hTail] using sameAnalyticNormalNormalizedVertex_product n I G q e hqe b hPower a
  have hEq : sameAnalyticNormalNormalizedVertex n I G q e hqe b hPower a=H :=
    mul_left_cancel₀ (pow_ne_zero (normalExponentDegree a.val)
      (HolomorphicGermReducednessBridge.coordinate_germ_ne_zero e))
      (hProductSame.trans hProduct.symm)
  exact hEq ▸ hOrders a

/-- EVERY actual geometrically HS-equal point over the reference enters the
SAME full-boundary controlled record, before a target PHS or cut is available.
All orders and the ideal formula use the ONE unconditional Θ/e/b/H witness. -/
theorem exists_actual_hs_equal_controlled_entry
    {d t : ℕ} {Z : Type} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel (d+(t+2))) Z] [IsComplexManifold (d+(t+2)) Z]
    (I : Ideal (HolGerm (ComplexModel (d+(t+2)))))
    (G : ActualAnalyticInheritedFamily (d+(t+2)) 0 (analyticZeroTaylorIdeal (d+(t+2)) I))
    (hmem : ∀ a, G.germs a∈I)
    (hw : ∀ a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+(t+2)) I),
      0<normalExponentDegree a.val)
    (hred : ∀ k, ActualInheritedPrefixReducedAt G k)
    (U : TopologicalSpace.Opens (ComplexModel (d+(t+2)))) (h0U : (0 : ComplexModel (d+(t+2)))∈U)
    (c : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+(t+2)) I) →
      ComplexModel (d+(t+2)) → ℂ)
    (hc : ∀ a, MDifferentiableOn 𝓘(ℂ,ComplexModel (d+(t+2))) 𝓘(ℂ,ℂ) (c a) U)
    (hrep : ∀ a, HolGerm.mk (c a)
      ((holomorphicAt_of_mdifferentiableOn U.isOpen (hc a) h0U).mono fun _ hz=>hz.differentiableAt)=G.germs a)
    (hCos : ∀ a, (U : Set (ComplexModel (d+(t+2))))∩complexCoordinatePlane (d+(t+2)) d⊆
      cosupport (d+(t+2)) univ (actualPrincipalCoefficientIdeal (d+(t+2)) (c a))
        (normalExponentDegree a.val))
    (E : List (Set U)) (π : Z → U)
    (hπ : IsBlowupAlong (d+(t+2)) ((Subtype.val : U → ComplexModel (d+(t+2))) ⁻¹'
      complexCoordinatePlane (d+(t+2)) d) π)
    (y : Z) (hy : (π y : ComplexModel (d+(t+2)))=0)
    (W : Set U)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+(t+2))) (π y) (π y)))
    (hΦsrc : Φ.source⊆(chartAt (ComplexModel (d+(t+2))) (π y)).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel (d+(t+2))) (π y) (π y))=0)
    (hΦid : Φ.toFun=id) (hΦdom : Φ.source=(U : Set (ComplexModel (d+(t+2)))))
    (hOrigin : I=originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
      (actualFlattenedOriginalSheaf (vanishingIdeal (n:=d+(t+2)) W) (π y) Φ) 0))
    (hHS : ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n:=d+(t+2))
      (strictTransform (d+(t+2)) π W)) y ℓ=
      hilbertSamuelAt (vanishingIdeal (n:=d+(t+2)) W) (π y) ℓ) :
    let w:=fun a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+(t+2)) I)=>
      normalExponentDegree a.val
    let M : MarkedIdeal (d+(t+2)) U:=⟨univ,E,weightedFunctionIdeal w (fun a (z : U)=>c a z),weightedCommonMark w⟩
    let Q:=M.geoTransform ((Subtype.val : U → ComplexModel (d+(t+2))) ⁻¹'
      complexCoordinatePlane (d+(t+2)) d) π
    y∈Q.cosupp ∧
      ∃ (e : Fin (d+(t+2))) (b : Fin (d+(t+2)) → ℂ)
        (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+(t+2))) y y))
        (hΘ0 : Θ.toFun (chartAt (ComplexModel (d+(t+2))) y y)=0),
        d≤e.val ∧ (∀ i : Fin (d+(t+2)), i.val<d → b i=0) ∧ b e=0 ∧
        Θ.source⊆(chartAt (ComplexModel (d+(t+2))) y).target ∧
        (∀ z : Z, z∈(chartAt (ComplexModel (d+(t+2))) y).source →
          chartAt (ComplexModel (d+(t+2))) y z∈Θ.source →
          (π z : ComplexModel (d+(t+2)))=
            actualAnalyticBlowupMap (actualTangentCentreVariables d (t+2)) e b
              (Θ.toFun (chartAt (ComplexModel (d+(t+2))) y z))) ∧
        ∃ H : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+(t+2)) I) →
            HolGerm (ComplexModel (d+(t+2))),
          (∀ a, G.germs a∈actualAnalyticCoordinateIdeal (actualTangentCentreVariables d (t+2))^w a) ∧
          (∀ a, coordinateGerm e^w a*H a=
            actualAnalyticBlowupPullback (actualTangentCentreVariables d (t+2)) e b (G.germs a)) ∧
          adaptedIdeal Q.ideal y Θ hΘ0=weightedCompression w H ∧
          ∀ a, H a∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+(t+2))))^w a := by
  dsimp only
  let w:=fun a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+(t+2)) I)=>
    normalExponentDegree a.val
  obtain ⟨e,b,Θ,hΘ0,he,hbt,hbe,hΘsrc,hSquare,H,hProducts,⟨hp,_heS,_hTaylor⟩,hIdeal,hCut⟩:=
    exists_actual_global_controlled_weighted_cut U h0U w hw c hc hCos π hπ y hy
  have hpG : ∀ a, G.germs a∈actualAnalyticCoordinateIdeal
      (actualTangentCentreVariables d (t+2))^normalExponentDegree a.val := by
    intro a
    simpa only [hrep] using hp a
  have hProductsG : ∀ a, coordinateGerm e^normalExponentDegree a.val*H a=
      actualAnalyticBlowupPullback (actualTangentCentreVariables d (t+2)) e b (G.germs a) := by
    intro a
    simpa only [hrep] using hProducts a
  have hnormal : ∀ z : Z, z∈(chartAt (ComplexModel (d+(t+2))) y).source →
      chartAt (ComplexModel (d+(t+2))) y z∈Θ.source →
      π z∈flatDomain Φ ∧ Φ.toFun (chartAt (ComplexModel (d+(t+2))) (π y) (π z))=
        actualAnalyticBlowupMap (actualTangentCentreVariables d (t+2)) e b
          (Θ.toFun (chartAt (ComplexModel (d+(t+2))) y z)) := by
    intro z hz hzΘ
    constructor
    · change π z∈(chartAt (ComplexModel (d+(t+2))) (π y)).source ∩ _
      constructor
      · rw [TopologicalSpace.Opens.chartAt_eq,chartAt_self_eq]
        rw [OpenPartialHomeomorph.subtypeRestr_source]
        exact mem_univ _
      · rw [hΦdom]
        change chartAt (ComplexModel (d+(t+2))) (π y) (π z)∈U
        rw [TopologicalSpace.Opens.chartAt_eq,chartAt_self_eq]
        exact (π z).property
    · rw [hΦid]
      change chartAt (ComplexModel (d+(t+2))) (π y) (π z)=_
      rw [TopologicalSpace.Opens.chartAt_eq,chartAt_self_eq]
      exact hSquare z hz hzΘ
  have hA : actualTangentCentreVariables d (t+2)=
      {i : Fin (d+(t+2)) | d ≤ i.val}:=actualTangentCentreVariables_eq_tail d (t+2)
  have hnormal' : ∀ z : Z, z∈(chartAt (ComplexModel (d+(t+2))) y).source →
      chartAt (ComplexModel (d+(t+2))) y z∈Θ.source →
      π z∈flatDomain Φ ∧ Φ.toFun (chartAt (ComplexModel (d+(t+2))) (π y) (π z))=
        actualAnalyticBlowupMap {i : Fin (d+(t+2)) | d ≤ i.val} e b
          (Θ.toFun (chartAt (ComplexModel (d+(t+2))) y z)) := by
    simpa only [hA] using hnormal
  let A:=actualFixedFlatteningSet (π y) Φ W
  have hModelOrigin : I=originalCoherentOriginIdeal (vanishingIdeal (n:=d+(t+2)) A) :=
    hOrigin.trans (originalFlattenedVanishingOriginIdeal_eq_model (π y) Φ hΦsrc hΦ0 W)
  have hModelHS : ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n:=d+(t+2))
      (strictTransform (d+(t+2))
        (actualAnalyticBlowupMap (actualTangentCentreVariables d (t+2)) e b) A)) 0 ℓ=
      hilbertSamuelAt (vanishingIdeal (n:=d+(t+2)) A) 0 ℓ := by
    intro ℓ
    have hTarget:=hilbertSamuelAt_strict_eq_fixedFlattening_model hπ.contMDiff y d
      Φ hΦsrc e b Θ hΘsrc hΘ0 hnormal' W ℓ
    calc
      _=hilbertSamuelAt (vanishingIdeal (n:=d+(t+2)) (strictTransform (d+(t+2)) π W)) y ℓ := by
        simpa only [hA] using hTarget.symm
      _=hilbertSamuelAt (vanishingIdeal (n:=d+(t+2)) W) (π y) ℓ:=hHS ℓ
      _=_:=hilbertSamuelAt_eq_fixedFlattening_model (π y) Φ hΦsrc hΦ0 W ℓ
  have hOrders : ∀ a, H a∈IsLocalRing.maximalIdeal
      (HolGerm (ComplexModel (d+(t+2))))^normalExponentDegree a.val :=
    fun a=>same_inherited_normal_orders_of_geometric_hs_eq d t A I hModelOrigin G
      hmem hpG hred e he b hModelHS a (H a) (hProductsG a)
  refine ⟨hCut.mpr hOrders,e,b,Θ,hΘ0,he,hbt,hbe,hΘsrc,hSquare,H,hpG,hProductsG,hIdeal,hOrders⟩

end

end Hironaka.HironakaActualGeometricPersistentInheritedCut
