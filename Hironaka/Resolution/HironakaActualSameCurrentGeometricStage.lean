import Hironaka.Resolution.HironakaActualGlobalCurrentCoordinateFlags
import Hironaka.Resolution.HironakaActualGeometricCurrentNeighborhoodHS

/-! One actual geometric strict presentation uses exactly the SAME current
functions as the full actual original controlled-record square. The one
stage theorem retains every historical coordinate-prefix flag on one open;
subsequent prescribed canonical-centre laws are separate obligations. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualSameCurrentGeometricStage
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf OkaIdealOperations
 HironakaActualGlobalCurrentCoordinateFlags HironakaActualHistoricalCoordinateTransport
 HironakaActualGeometricMarkedSquare HironakaActualCurrentMarkedFunctionSquares
 HironakaActualGeometricCurrentNeighborhoodHS HironakaActualInheritedNeighborhoodMarkedHS
 HironakaActualAnalyticAdaptedCurrentSelector HironakaActualRelativeNormalJetDivision
 HironakaActualFormalInitialDiagram HironakaActualNormalZeroAnalyticSaturation
 HironakaActualInheritedNestedContactFlag HironakaActualFixedInheritedSelector
 HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetRankLoci
 HironakaActualNormalAllDirectionAnalyticSaturation HironakaActualAnalyticAdaptedCurrentFamily
 HironakaActualOriginalAdaptedMarkedTransport HironakaActualFixedInheritedSelectorPermutation
 HironakaRelativeNormalMonomialBasis HironakaActualInheritedSourcePermutationFamily
 HironakaActualRelativeStandardnessNormalPivotPriority
 HironakaActualCoefficientPresentationCentrePower HironakaRelativeNormalDeformationInitialRelations
variable {n : ℕ}

theorem map_span_of_common_unit_covariance {ι κ : Type} [Fintype ι] [Fintype κ]
    (w : ι → ℕ) (old : ι → HolGerm (ComplexModel n))
    (current : κ → HolGerm (ComplexModel n)) (labels : ι≃κ)
    (C : HolGerm (ComplexModel n)≃ₐ[ℂ]HolGerm (ComplexModel n))
    (u : HolGerm (ComplexModel n)) (hu : IsUnit u)
    (hCov : ∀i,C (old i)=u^(w i)*current (labels i)) :
    Ideal.map C.toRingEquiv.toRingHom (Ideal.span (range old))=Ideal.span (range current) := by
  apply le_antisymm
  · rw [Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro g ⟨a,⟨i,rfl⟩,rfl⟩
    change C (old i)∈Ideal.span (range current)
    rw [hCov i]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨labels i,rfl⟩)
  · apply Ideal.span_le.mpr
    rintro g ⟨j,rfl⟩
    obtain ⟨i,rfl⟩:=labels.surjective j
    have h:=Ideal.mem_map_of_mem C.toRingEquiv.toRingHom
      (Ideal.subset_span (show old i∈range old from ⟨i,rfl⟩))
    change C (old i)∈Ideal.map C.toRingEquiv.toRingHom (Ideal.span (range old)) at h
    rw [hCov i] at h
    exact (Ideal.unit_mul_mem_iff_mem _ (hu.pow (w i))).mp h

private theorem inSpanAt_congr_near {ι : Type} [Fintype ι]
    {s t : ι → ComplexModel n → ℂ} {y : ComplexModel n}
    (h : ∀ᶠz in 𝓝 y,∀i,s i z=t i z) (g : ComplexModel n → ℂ) :
    InSpanAt s y g ↔ InSpanAt t y g := by
  constructor
  · rintro ⟨hg,a,ha,he⟩
    refine ⟨hg,a,ha,?_⟩
    filter_upwards [he,h] with z hz hst
    rw [hz]
    exact Finset.sum_congr rfl fun i _=>congrArg (fun q=>a i z*q) (hst i)
  · rintro ⟨hg,a,ha,he⟩
    refine ⟨hg,a,ha,?_⟩
    filter_upwards [he,h] with z hz hst
    rw [hz]
    exact Finset.sum_congr rfl fun i _=>congrArg (fun q=>a i z*q) (hst i).symm

/-- ANY fixed representatives of the SAME inherited germs give the whole
nearby ideal and whole HS reference locus, on one actual common open. -/
theorem exists_actual_same_representatives_neighborhood_hs
    (A : GermIdeal n (ComplexModel n)) (hfg : IdealFGAt A.mem 0)
    (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I))
    (hspan : Ideal.span (range G.germs)=I) (hred : ∀k,ActualInheritedPrefixReducedAt G k)
    (hI : I=originalCoherentOriginIdeal A) (R : ℕ → ℕ)
    (hReference : ∀ℓ,hilbertSamuelAt A 0 ℓ=R ℓ)
    (f : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I) → ComplexModel n → ℂ)
    (hf : ∀a,HolAt (f a) 0) (hF : ∀a,HolGerm.mk (f a) (hf a)=G.germs a)
    (O : Set (ComplexModel n)) (hO : IsOpen O) (h0O : (0 : ComplexModel n)∈O) :
    ∃P : ActualGeometricInheritedNeighborhoodHS A I G R,
      P.representatives=f ∧ P.neighborhood⊆O := by
  subst I
  obtain ⟨H,hg,hG,U,hU,h0U,hHd,hgen,hhol,hHS⟩:=
    exists_actual_inherited_neighborhood_member_orders_iff_hs A hfg G hspan hred
  have hEq (a) : H a=ᶠ[𝓝 (0 : ComplexModel n)] f a:=
    HolGerm.mk_eq_mk_iff.mp ((hG a).trans (hF a).symm)
  have hAll : ∀ᶠz in 𝓝 (0 : ComplexModel n),∀a,H a z=f a z:=eventually_all.mpr hEq
  obtain ⟨B,hBsub,hB,h0B⟩:=mem_nhds_iff.mp hAll
  obtain ⟨F,hFsub,hFopen,h0F⟩:=mem_nhds_iff.mp (eventually_all.mpr hf)
  let V:=(U∩B)∩(O∩F)
  have hV : IsOpen V:=(hU.inter hB).inter (hO.inter hFopen)
  have h0V : (0 : ComplexModel n)∈V:=⟨⟨h0U,h0B⟩,h0O,h0F⟩
  have hNear (y : ComplexModel n) (hy : y∈V) : ∀ᶠz in 𝓝 y,∀a,H a z=f a z:=by
    filter_upwards [hB.mem_nhds hy.1.2] with z hz
    exact hBsub hz
  have hfV : ∀y∈V,∀a,HolAt (f a) y:=by
    intro y hy a
    filter_upwards [hFopen.mem_nhds hy.2.2] with z hz
    exact hFsub hz a
  have hTranslate (y : ComplexModel n) (hy : y∈V) (a) :
      translatedGerm y (H a) (hhol y hy.1.1 a)=translatedGerm y (f a) (hfV y hy a) := by
    apply HolGerm.mk_eq_mk_iff.mpr
    have ht : Tendsto (fun z : ComplexModel n=>z+y) (𝓝 0) (𝓝 y):=by
      simpa only [zero_add] using
        (show Continuous (fun z : ComplexModel n=>z+y) from continuous_id.add continuous_const).tendsto 0
    exact (ht.eventually (hNear y hy)).mono fun _ hz=>hz a
  refine ⟨{
    representatives:=f
    holomorphicAtZero:=hf
    sameGerms:=hF
    neighborhood:=V
    isOpen_neighborhood:=hV
    zero_mem:=h0V
    holomorphicOn:=fun a y hy=>(hFsub hy.2.2 a).differentiableWithinAt
    wholeGeneration:=fun y hy g=>(hgen y hy.1.1 g).trans (inSpanAt_congr_near (hNear y hy) g)
    holomorphicAt:=hfV
    wholeHS:=?_ },rfl,fun _ hy=>hy.2.1⟩
  intro y hy
  have heq : (∀a,translatedGerm y (H a) (hhol y hy.1.1 a)∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^normalExponentDegree a.val) ↔
      ∀a,translatedGerm y (f a) (hfV y hy a)∈
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^normalExponentDegree a.val := by
    constructor
    · intro h a
      rw [←hTranslate y hy a]
      exact h a
    · intro h a
      rw [hTranslate y hy a]
      exact h a
  exact heq.symm.trans (by simpa only [hReference] using hHS y hy.1.1)

open HironakaActualGeometricAdaptedCurrentSelector HironakaActualLocalHolomorphicOriginPullback
 HironakaActualGermEquivLocalRealization HironakaActualFixedFlatteningHSComparison
 HironakaActualLocalStrictSaturation HironakaActualPointGeometricBennett
 HironakaActualCoefficientAnalyticBlowup HironakaSmoothCentreCoherentDomain
 HironakaRelativeNormalCoherentSaturation HironakaActualInheritedHSContactContainment
 HironakaRelativeNormalCoherentTranslatedJets BlowupFlatCoordinates
 MarkedIdeals MarkedIdealBiholomorphism HironakaRelativeNormalIdeal
 HironakaHolomorphicPointJets HironakaActualWeightedCoefficientCompression
 HironakaActualCoherentWeightedCoefficientMarked
 HironakaSmoothSubmersionGermIdealColon HironakaActualGeometricAdaptedCurrentFamily

open Hironaka.BlowupSequences HironakaActualGlobalInheritedCut GermIdealOrder
 HironakaActualRelativeNormalJetDivision HironakaActualFormalInitialDiagram
 HironakaActualNormalZeroAnalyticSaturation HironakaActualNormalAllDirectionAnalyticSaturation
 HironakaActualInheritedNestedContactFlag HironakaActualFixedInheritedSelector
 HironakaActualAnalyticAdaptedCurrentSelector HironakaActualNormalMarkedDirection
 HironakaActualAnalyticBlowupTaylor HironakaActualCoefficientPresentationCentrePower
 HironakaActualFiniteCoefficientIdeals HironakaActualCoefficientAnalyticBlowup
 HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
 HironakaActualOriginalAdaptedMarkedTransport HironakaHolomorphicJetMonomialSpan
 BlowupControlledTransform MarkedIdeals.MarkedIdeal InvertibleIdealQuotient

/-- ORIGINAL source representatives, original inherited monic data and the
literal actual controlled cut internally give the SAME current D and a
genuine common chart transporting the full ORIGINAL global geometric
controlled record to the literal current-family native weighted record.
No target presentation, chart comparison, unit, or desired stalk identity is
supplied. The same current functions simultaneously present the ACTUAL strict
sheaf and ACTUAL controlled record, and retain all historical prefix flags. -/
theorem exists_actual_same_current_geometric_stage
    {d t : ℕ} {Z : Type} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel (d+(t+2))) Z] [IsComplexManifold (d+(t+2)) Z]
    (I : Ideal (HolGerm (ComplexModel (d+(t+2)))))
    (G : ActualAnalyticInheritedFamily (d+(t+2)) 0 (analyticZeroTaylorIdeal (d+(t+2)) I))
    (hmem : ∀a,G.germs a∈I)
    (hw : ∀a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+(t+2)) I),
      0<normalExponentDegree a.val)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+(t+2)) I)))
    (hred : ∀k,ActualInheritedPrefixReducedAt G k)
    (hContact : ∀k,actualFixedSelectorContactAt S G.germs k)
    (U : TopologicalSpace.Opens (ComplexModel (d+(t+2)))) (h0U : (0 : ComplexModel (d+(t+2)))∈U)
    (c : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+(t+2)) I) →
      ComplexModel (d+(t+2)) → ℂ)
    (hc : ∀a,MDifferentiableOn 𝓘(ℂ,ComplexModel (d+(t+2))) 𝓘(ℂ,ℂ) (c a) U)
    (hrep : ∀a,HolGerm.mk (c a)
      ((holomorphicAt_of_mdifferentiableOn U.isOpen (hc a) h0U).mono fun _ hz=>hz.differentiableAt)=G.germs a)
    (hCos : ∀a,(U : Set (ComplexModel (d+(t+2))))∩complexCoordinatePlane (d+(t+2)) d⊆
      cosupport (d+(t+2)) univ (actualPrincipalCoefficientIdeal (d+(t+2)) (c a)) (normalExponentDegree a.val))
    (E : List (Set U)) (π : Z → U)
    (hπ : IsBlowupAlong (d+(t+2)) ((Subtype.val : U → ComplexModel (d+(t+2))) ⁻¹'
      complexCoordinatePlane (d+(t+2)) d) π)
    (y : Z) (hy : (π y : ComplexModel (d+(t+2)))=0)
    (W : Set U) (hWa : IsComplexAnalyticSubset (n:=d+(t+2)) W)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+(t+2))) (π y) (π y)))
    (hΦsrc : Φ.source⊆(chartAt (ComplexModel (d+(t+2))) (π y)).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel (d+(t+2))) (π y) (π y))=0)
    (hΦid : Φ.toFun=id) (hΦdom : Φ.source=(U : Set (ComplexModel (d+(t+2)))))
    (hOrigin : I=originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
      (actualFlattenedOriginalSheaf (vanishingIdeal (n:=d+(t+2)) W) (π y) Φ) 0)) :
    let w:=fun a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+(t+2)) I)=>
      normalExponentDegree a.val
    let M : MarkedIdeal (d+(t+2)) U:=⟨univ,E,weightedFunctionIdeal w (fun a (z : U)=>c a z),weightedCommonMark w⟩
    let Q:=M.geoTransform ((Subtype.val : U → ComplexModel (d+(t+2))) ⁻¹' complexCoordinatePlane (d+(t+2)) d) π
    let q : Fin (d+(t+2)):=⟨d,by omega⟩
    y∈Q.cosupp →
    ∃(e : Fin (d+(t+2)))(b : Fin (d+(t+2)) → ℂ)
      (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+(t+2))) y y))
      (_hΘ0 : Θ.toFun (chartAt (ComplexModel (d+(t+2))) y y)=0)
      (he : q≤e),
      Θ.source⊆(chartAt (ComplexModel (d+(t+2))) y).target ∧
      (∀z : Z,z∈(chartAt (ComplexModel (d+(t+2))) y).source →
        chartAt (ComplexModel (d+(t+2))) y z∈Θ.source →
        (π z : ComplexModel (d+(t+2)))=actualAnalyticBlowupMap (actualTangentCentreVariables d (t+2)) e b
          (Θ.toFun (chartAt (ComplexModel (d+(t+2))) y z))) ∧
      ∃hp : ∀a,G.germs a∈actualAnalyticCoordinateIdeal (Set.Ici q)^normalExponentDegree a.val,
      ∃f : Fin (d+(t+2)),∃_hqf : q≤f,actualNormalMarkedDirection (Set.Ici q) e b f≠0 ∧
      ∃C : HolGerm (ComplexModel (d+(t+2)))≃ₐ[ℂ]HolGerm (ComplexModel (d+(t+2))),
      ∃u : HolGerm (ComplexModel (d+(t+2))),IsUnit u ∧
      ∃D : ActualAdaptedCurrentSelectorData I G q e f b S,
      ∃P : ActualMarkedFunctionSquare w
        (sameAnalyticNormalNormalizedVertex (d+(t+2)) I G q e he b hp) D.targetFamily.germs
        (actualAdaptedOriginalLabelEquiv D) C u,
        (P.oldDomain : Set (ComplexModel (d+(t+2))))⊆Θ.target ∧
        MarkedIdeal.pullback
          (fun z : P.currentDomain=>actualFlatteningInverseMap y Θ (P.chart.toFun z)) Q=
          actualCurrentNativeWeightedRecord P (fun a=>normalExponentDegree a.val)
            ((fun z : P.oldDomain=>actualFlatteningInverseMap y Θ z) ⁻¹' Q.N)
            (Q.E.map ((fun z : P.oldDomain=>actualFlatteningInverseMap y Θ z) ⁻¹' ·)) ∧
        let K:=originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
          (actualFlattenedOriginalSheaf (vanishingIdeal (n:=d+(t+2))
            (strictTransform (d+(t+2)) π W)) y Θ) 0)
        let J:=(HironakaActualGeometricAdaptedCurrentSelector.actualAdaptedHistoricalCurrentSource D).ideal
        let A₀:=vanishingIdeal (n:=d+(t+2))
          (actualFixedFlatteningSet y Θ (strictTransform (d+(t+2)) π W))
        let A:=GermIdeal.pullback (m:=d+(t+2)) P.chart.toFun A₀
        J=Ideal.map C.toRingEquiv.toRingHom K ∧ J=originalCoherentOriginIdeal A ∧
        ∃PHS : ActualGeometricInheritedNeighborhoodHS A J D.targetFamily (hilbertSamuelValue I),
          PHS.representatives=P.currentFunctions ∧ PHS.neighborhood⊆P.currentDomain ∧
          MapsTo P.chart.toFun PHS.neighborhood Θ.target ∧
          (∀k,∀z∈PHS.neighborhood,
            (∀i∈fixedSelectorBlock (actualInitialVertices MonomialOrder.degLex
              (analyticZeroTaylorIdeal (d+(t+2)) I)) k,P.chart.toFun z i=0) ↔
            ∀j∈fixedSelectorBlock (actualInitialVertices MonomialOrder.degLex
              (analyticZeroTaylorIdeal (d+(t+2)) (sameAnalyticZeroNormalizedIdeal (d+(t+2)) _
                D.sourceFamily q D.sourcePower))) k,z j=0) ∧
          ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=d+(t+2)) (strictTransform (d+(t+2)) π W)) y ℓ=
            hilbertSamuelAt (vanishingIdeal (n:=d+(t+2)) W) (π y) ℓ := by
  dsimp only
  intro hcut
  let w:=fun a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+(t+2)) I)=>
    normalExponentDegree a.val
  let M0 : MarkedIdeal (d+(t+2)) U:=⟨univ,[],weightedFunctionIdeal w (fun a (z : U)=>c a z),weightedCommonMark w⟩
  let M : MarkedIdeal (d+(t+2)) U:=⟨univ,E,weightedFunctionIdeal w (fun a (z : U)=>c a z),weightedCommonMark w⟩
  let ZC:=((Subtype.val : U → ComplexModel (d+(t+2))) ⁻¹' complexCoordinatePlane (d+(t+2)) d)
  let Q:=M.geoTransform ZC π
  let q : Fin (d+(t+2)):=⟨d,by omega⟩
  have hcu (a) : MDifferentiable 𝓘(ℂ,ComplexModel (d+(t+2))) 𝓘(ℂ,ℂ) (fun z : U=>c a z) := by
    intro z
    exact ((holomorphicAt_of_mdifferentiableOn U.isOpen (hc a) z.property).comp_contMDiff
      (Eventually.of_forall fun _=>(contMDiff_subtype_val (U:=U)).contMDiffAt)).mdifferentiableAt
  have hI:=isCoherent_weightedFunctionIdeal w (fun a (z : U)=>c a z) hcu
  have hcut0 : y∈(M0.geoTransform ZC π).cosupp := by
    change y∈cosupport (d+(t+2)) (M0.geoTransform ZC π).N (M0.geoTransform ZC π).ideal (M0.geoTransform ZC π).d
    rw [geoTransform_N_eq_univ (𝔪:=M0) rfl hπ,
      geoTransform_ideal_eq_controlledTransform (𝔪:=M0) rfl hI hπ,geoTransform_d]
    change y∈cosupport (d+(t+2)) Q.N Q.ideal Q.d at hcut
    rw [geoTransform_N_eq_univ (𝔪:=M) rfl hπ,
      geoTransform_ideal_eq_controlledTransform (𝔪:=M) rfl hI hπ,geoTransform_d] at hcut
    exact hcut
  obtain ⟨e,b,Θ,hΘ0,H,he,hbe,hΘsrc,hSquare,hpOld,hOrders,hProducts,hIdeal0,
    _hHS,_hEssential,_hHistorical⟩:=
    exists_actual_cut_hs_and_historical_legality (by omega) I G hmem hw S hred hContact
      U h0U c hc hrep hCos π hπ y hy hcut0
  have hQ : Q.ideal.IsCoherent := by
    rw [geoTransform_ideal_eq_controlledTransform (𝔪:=M) rfl hI hπ]
    exact CoherentIdealColon.isCoherent_colon_of_isCoherent
      (GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff hI)
      (DivisorMetric.isCoherent_of_isInvertible (isInvertible_idealPow_exceptionalDivisor hπ (weightedCommonMark w)))
  have hIdeal : adaptedIdeal Q.ideal y Θ hΘ0=weightedCompression w H := by
    rw [geoTransform_ideal_eq_controlledTransform (𝔪:=M) rfl hI hπ]
    rw [geoTransform_ideal_eq_controlledTransform (𝔪:=M0) rfl hI hπ] at hIdeal0
    exact hIdeal0
  have hTail : actualTangentCentreVariables d (t+2)=Set.Ici q := by
    ext i
    rw [actualTangentCentreVariables_eq_tail]
    rfl
  have hp : ∀a,G.germs a∈actualAnalyticCoordinateIdeal (Set.Ici q)^normalExponentDegree a.val := by
    intro a
    have h:=hpOld a
    rw [hTail] at h
    exact h
  have hEq (a) : sameAnalyticNormalNormalizedVertex (d+(t+2)) I G q e he b hp a=H a := by
    apply mul_left_cancel₀ (pow_ne_zero (normalExponentDegree a.val)
      (HolomorphicGermReducednessBridge.coordinate_germ_ne_zero e))
    exact (sameAnalyticNormalNormalizedVertex_product (d+(t+2)) I G q e he b hp a).trans
      (by simpa only [hTail,coordinateGerm] using (hProducts a).symm)
  have hFun : sameAnalyticNormalNormalizedVertex (d+(t+2)) I G q e he b hp=H:=funext hEq
  have hOrd : ∀a,sameAnalyticNormalNormalizedVertex (d+(t+2)) I G q e he b hp a∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+(t+2))))^normalExponentDegree a.val := by
    simpa only [hFun] using hOrders
  have hW : (vanishingIdeal (n:=d+(t+2)) W).IsCoherent:=CartanIrreducible.cartanCoherence W hWa
  have hnormal : ∀z : Z,z∈(chartAt (ComplexModel (d+(t+2))) y).source →
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
  obtain ⟨hStrict,hIntrinsic⟩:=actual_geometric_strict_stalk_eq_normalized_ideal (by omega)
    π hπ.contMDiff y W hW Φ hΦsrc hΦ0 e he b Θ hΘsrc hΘ0 hnormal
    I hOrigin G hmem hpOld H hProducts hOrders
  obtain ⟨f,hqf,hvf,C,u,hu,D,hCov,hCoord,_hBlockIdeals⟩:=
    exists_actual_current_transport_with_historical_coordinate_flags
      I G hmem q e he b hp hOrd hred S hContact
  obtain ⟨P⟩:=exists_actual_marked_function_square w
    (sameAnalyticNormalNormalizedVertex (d+(t+2)) I G q e he b hp)
    D.targetFamily.germs (actualAdaptedOriginalLabelEquiv D) C u hu hCov
  have hIdealN : adaptedIdeal Q.ideal y Θ hΘ0=weightedCompression w
      (sameAnalyticNormalNormalizedVertex (d+(t+2)) I G q e he b hp) := by
    rw [hFun]
    exact hIdeal
  obtain ⟨R,_hChart,_hOld,_hCurrent,_hUnit,hRT,hGeom⟩:=exists_actual_geometric_marked_square
    (w:=w) (old:=sameAnalyticNormalNormalizedVertex (d+(t+2)) I G q e he b hp)
    (current:=D.targetFamily.germs) (labels:=actualAdaptedOriginalLabelEquiv D) (C:=C) (u:=u)
    Q hQ y Θ hΘsrc hΘ0 hIdealN (geoTransform_d (𝔪:=M) ZC π) P
      (fun a=>normalExponentDegree a.val) (fun a=>actualAdaptedOriginalLabelEquiv_degree D a)
  obtain ⟨O,hO,h0O,_hOS,_hv,_hne,_hCoordFunctions,hFlags⟩:=
    exists_actual_common_coordinate_flag_neighborhood C (normalPivotEquiv q f) u hu
      (fixedSelectorEssential (actualInitialVertices MonomialOrder.degLex
        (analyticZeroTaylorIdeal (d+(t+2)) I))) hCoord R.chart R.chart_zero R.chart_germs
      R.unitFunction R.unitHolomorphicAtZero R.unitGerm
  let K:=originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
    (actualFlattenedOriginalSheaf (vanishingIdeal (n:=d+(t+2))
      (strictTransform (d+(t+2)) π W)) y Θ) 0)
  let J:=(HironakaActualGeometricAdaptedCurrentSelector.actualAdaptedHistoricalCurrentSource D).ideal
  have hK : K=Ideal.span (range (sameAnalyticNormalNormalizedVertex (d+(t+2)) I G q e he b hp)) := by
    dsimp only [K]
    rw [hStrict,hTail]
    exact actualAnalyticNormalizedMemberIdeal_eq_same_normal_span (d+(t+2)) I G hmem q e he b hp
  have hCurrentK : J=Ideal.map C.toRingEquiv.toRingHom K := by
    rw [hK]
    exact ((map_span_of_common_unit_covariance w
      (sameAnalyticNormalNormalizedVertex (d+(t+2)) I G q e he b hp)
      D.targetFamily.germs (actualAdaptedOriginalLabelEquiv D) C u hu hCov).trans D.targetSpan).symm
  let A₀:=vanishingIdeal (n:=d+(t+2)) (actualFixedFlatteningSet y Θ (strictTransform (d+(t+2)) π W))
  let A:=GermIdeal.pullback (m:=d+(t+2)) R.chart.toFun A₀
  have hSa:=HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong hπ hWa
  have hScoh : (vanishingIdeal (n:=d+(t+2)) (strictTransform (d+(t+2)) π W)).IsCoherent:=
    CartanIrreducible.cartanCoherence _ hSa
  have hfg₀ : IdealFGAt A₀.mem (0 : ComplexModel (d+(t+2))):=
    fixedFlattening_vanishing_local_fg _ hScoh y Θ hΘsrc hΘ0
  have hfg : IdealFGAt A.mem (0 : ComplexModel (d+(t+2))):=
    local_fg_pullback_of_holomorphic_germ R.chart.toFun (local_toFun_holomorphic R.chart)
      R.chart_zero A₀ hfg₀
  have hHom : (compAlgHom R.chart.toFun (local_toFun_holomorphic R.chart) R.chart_zero).toRingHom=
      C.toRingEquiv.toRingHom := by
    change (localGermAlgEquiv R.chart R.chart_zero).toRingEquiv.toRingHom=C.toRingEquiv.toRingHom
    rw [R.chart_germs]
  have hModel:=originalFlattenedVanishingOriginIdeal_eq_model y Θ hΘsrc hΘ0
    (strictTransform (d+(t+2)) π W)
  have hPullOrigin:=origin_pullback_eq_of_holomorphic_germ R.chart.toFun
    (local_toFun_holomorphic R.chart) R.chart_zero A₀ hfg₀
  rw [hHom,←hModel] at hPullOrigin
  have hCurrentOrigin : J=originalCoherentOriginIdeal A:=hCurrentK.trans hPullOrigin.symm
  have hReference (ℓ : ℕ) : hilbertSamuelAt A 0 ℓ=hilbertSamuelValue I ℓ := by
    rw [hilbertSamuelAt_model_zero,←hCurrentOrigin]
    exact D.targetHS ℓ
  let V:=O∩(R.currentDomain : Set (ComplexModel (d+(t+2))))
  obtain ⟨PHS,hSame,hPHS⟩:=exists_actual_same_representatives_neighborhood_hs A hfg J
    D.targetFamily D.targetSpan D.targetPrefix hCurrentOrigin (hilbertSamuelValue I) hReference
    R.currentFunctions R.currentHolomorphicAtZero (fun a=>(R.currentGerms a).symm)
    V (hO.inter R.currentDomain.isOpen) ⟨h0O,R.zero_mem_current⟩
  refine ⟨e,b,Θ,hΘ0,he,hΘsrc,hSquare,hp,f,hqf,hvf,C,u,hu,D,R,hRT,hGeom,
    hCurrentK,hCurrentOrigin,PHS,hSame,(fun _ hz=>(hPHS hz).2),
    (fun z hz=>hRT (R.inside_old ((hPHS hz).2))),?_,hIntrinsic⟩
  intro k z hz
  have hTL : fixedSelectorBlock (actualInitialVertices MonomialOrder.degLex
      (analyticZeroTaylorIdeal (d+(t+2)) I)) k⊆
      fixedSelectorEssential (actualInitialVertices MonomialOrder.degLex
        (analyticZeroTaylorIdeal (d+(t+2)) I)) := by
    rintro i ⟨a,_ha,hai⟩
    exact ⟨a,hai⟩
  have h:=hFlags (fixedSelectorBlock (actualInitialVertices MonomialOrder.degLex
    (analyticZeroTaylorIdeal (d+(t+2)) I)) k) hTL z (hPHS hz).1
  have heq:=Set.ext_iff.mp (actual_current_block_eq_original_image D k)
  constructor
  · intro ho j hj
    exact h.mp ho j ((heq j).mp hj)
  · intro hn
    apply h.mpr
    intro j hj
    exact hn j ((heq j).mpr hj)

end
end Hironaka.HironakaActualSameCurrentGeometricStage
