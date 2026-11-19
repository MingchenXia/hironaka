import Hironaka.Resolution.HironakaActualControlledNeighborhoodGenerators
import Hironaka.Resolution.HironakaActualRawRecordPullbacks

/-! The same actual current-family function square is shrunk to a genuine
geometric controlled-ideal neighborhood, with no change to any member,
weight, germ equivalence, or historical selector. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualGeometricMarkedSquare
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf
 HironakaActualControlledNeighborhoodGenerators HironakaActualCurrentMarkedFunctionSquares
 HironakaActualWeightedCoefficientCompression HironakaActualCoherentWeightedCoefficientMarked
 HironakaSmoothCentreCoherentDomain HironakaSmoothSubmersionGermIdealColon
 HironakaHolomorphicJetChartInvariance RelativePrincipalizationSpan
 MarkedIdeals MarkedIdealBiholomorphism
variable {n : ℕ} {ι κ : Type} [Fintype ι] [Fintype κ]
 {w : ι → ℕ} {old : ι → HolGerm (ComplexModel n)} {current : κ → HolGerm (ComplexModel n)}
 {labels : ι≃κ} {C : HolGerm (ComplexModel n)≃ₐ[ℂ]HolGerm (ComplexModel n)} {u : HolGerm (ComplexModel n)}

/-- Replace only the old open by the given genuine zero-neighborhood and
shrink the current open by its actual inverse image. Every function and
entire germ in the square is retained literally. -/
def actualMarkedSquareOnOldOpen (P : ActualMarkedFunctionSquare w old current labels C u)
    (V : TopologicalSpace.Opens (ComplexModel n)) (h0V : (0 : ComplexModel n)∈V)
    (hV : ∀i,DifferentiableOn ℂ (P.oldFunctions i) V) :
    ActualMarkedFunctionSquare w old current labels C u := by
  have hφ : DifferentiableOn ℂ P.chart.toFun P.currentDomain :=
    fun z hz=>(P.chart.toFun_holomorphic.differentiableAt
      (P.chart.isOpen_source.mem_nhds (P.inside_chart hz))).differentiableWithinAt
  let U : TopologicalSpace.Opens (ComplexModel n):=
    ⟨(P.currentDomain : Set (ComplexModel n))∩P.chart.toFun ⁻¹' V,
      hφ.continuousOn.isOpen_inter_preimage P.currentDomain.isOpen V.isOpen⟩
  have h0U : (0 : ComplexModel n)∈U:=⟨P.zero_mem_current,by
    change P.chart.toFun 0∈V
    rw [P.chart_zero]
    exact h0V⟩
  exact {
    P with
    oldDomain:=V
    zero_mem_old:=h0V
    currentDomain:=U
    zero_mem_current:=h0U
    inside_chart:=fun _ hz=>P.inside_chart hz.1
    inside_old:=fun _ hz=>hz.2
    oldHolomorphicOn:=hV
    currentHolomorphicOn:=fun j=>(P.currentHolomorphicOn j).mono inter_subset_left
    unitHolomorphicOn:=P.unitHolomorphicOn.mono inter_subset_left
    unitNonzero:=fun z hz=>P.unitNonzero z hz.1
    memberSquare:=fun i z hz=>P.memberSquare i z hz.1 }

private theorem native_inverse_chart_contMDiff
    {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    (x : X) (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source⊆(chartAt (ComplexModel n) x).target)
    (V : TopologicalSpace.Opens (ComplexModel n)) (hV : (V : Set (ComplexModel n))⊆Φ.target) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (fun z : V=>actualFlatteningInverseMap x Φ z) := by
  intro z
  have hmd : ∀ᶠa in 𝓝 (z : ComplexModel n),
      MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) (actualFlatteningInverseMap x Φ) a :=
    eventually_of_mem (Φ.isOpen_target.mem_nhds (hV z.property))
      (fun a ha=>actualFlatteningInverseMap_mdifferentiable x Φ hsrc a ha)
  exact (MarkedIdealOpenBiholomorphism.contMDiffAt_of_eventually_mdifferentiableAt' hmd).comp z
    (contMDiff_subtype_val z)

private theorem square_map_contMDiff (P : ActualMarkedFunctionSquare w old current labels C u) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (actualMarkedSquareMap P) := by
  have hForward : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (fun z : P.currentDomain=>P.chart.toFun z) := by
    intro z
    have hmd : ∀ᶠa in 𝓝 (z : ComplexModel n),MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n)
        P.chart.toFun a :=
      eventually_of_mem (P.chart.isOpen_source.mem_nhds (P.inside_chart z.property)) fun a ha=>
        (P.chart.toFun_holomorphic.differentiableAt (P.chart.isOpen_source.mem_nhds ha)).mdifferentiableAt
    exact (MarkedIdealOpenBiholomorphism.contMDiffAt_of_eventually_mdifferentiableAt' hmd).comp z
      (contMDiff_subtype_val z)
  exact BlowupRestrictOpen.contMDiff_opens_mk hForward (fun z=>P.inside_old z.property)

/-- The entire original geometric record is transported into the SAME
current-family functions by the actual composed chart on one common domain.
All comparison data are derived from coherence and the whole adapted span. -/
theorem exists_actual_geometric_marked_square
    {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    (Q : MarkedIdeal n X) (hQ : Q.ideal.IsCoherent) (x : X)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source⊆(chartAt (ComplexModel n) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0)
    (hIdeal : adaptedIdeal Q.ideal x Φ h0=weightedCompression w old)
    (hd : Q.d=weightedCommonMark w)
    (P : ActualMarkedFunctionSquare w old current labels C u)
    (wn : κ → ℕ) (hWeights : ∀i,wn (labels i)=w i) :
    ∃R : ActualMarkedFunctionSquare w old current labels C u,
      R.chart=P.chart ∧ R.oldFunctions=P.oldFunctions ∧ R.currentFunctions=P.currentFunctions ∧
      R.unitFunction=P.unitFunction ∧
      (R.oldDomain : Set (ComplexModel n))⊆Φ.target ∧
      MarkedIdeal.pullback
        (fun z : R.currentDomain=>actualFlatteningInverseMap x Φ (R.chart.toFun z)) Q=
        actualCurrentNativeWeightedRecord R wn
          ((fun z : R.oldDomain=>actualFlatteningInverseMap x Φ z) ⁻¹' Q.N)
          (Q.E.map ((fun z : R.oldDomain=>actualFlatteningInverseMap x Φ z) ⁻¹' ·)) := by
  obtain ⟨V,h0V,hVT,hVhol,hNative⟩:=exists_actual_native_weighted_record_of_adapted_span
    Q hQ x Φ hsrc h0 w old hIdeal hd P.oldFunctions P.oldHolomorphicAtZero P.oldGerms
  let R:=actualMarkedSquareOnOldOpen P V h0V hVhol
  have hRTarget : (R.oldDomain : Set (ComplexModel n))⊆Φ.target:=hVT
  let ψ : R.oldDomain → X:=fun z=>actualFlatteningInverseMap x Φ z
  have hOld : MarkedIdeal.pullback ψ Q=
      actualOldNativeWeightedRecord R (ψ ⁻¹' Q.N) (Q.E.map (ψ ⁻¹' ·)) := hNative
  have hCompose:=HironakaActualRawRecordPullbacks.marked_pullback_comp_hhol
    (fun x f hf=>holomorphicAt_of_mem_coherent Q.ideal hQ hf)
    (native_inverse_chart_contMDiff x Φ hsrc R.oldDomain hRTarget)
    (square_map_contMDiff R)
    (d:=fun z : R.currentDomain=>actualFlatteningInverseMap x Φ (R.chart.toFun z))
    (fun _=>rfl)
  refine ⟨R,rfl,rfl,rfl,rfl,hRTarget,?_⟩
  rw [←hCompose,hOld]
  exact actual_square_native_weighted_record_eq R wn (fun i=>(hWeights i).symm) (ψ ⁻¹' Q.N) (Q.E.map (ψ ⁻¹' ·))


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
supplied. The contact carrier is the actual old carrier trace. -/
theorem exists_actual_global_controlled_current_marked_record
    {d t : ℕ} {Z : Type} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel (d+(t+1))) Z] [IsComplexManifold (d+(t+1)) Z]
    (I : Ideal (HolGerm (ComplexModel (d+(t+1)))))
    (G : ActualAnalyticInheritedFamily (d+(t+1)) 0 (analyticZeroTaylorIdeal (d+(t+1)) I))
    (hmem : ∀a,G.germs a∈I)
    (hw : ∀a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+(t+1)) I),
      0<normalExponentDegree a.val)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+(t+1)) I)))
    (hred : ∀k,ActualInheritedPrefixReducedAt G k)
    (hContact : ∀k,actualFixedSelectorContactAt S G.germs k)
    (U : TopologicalSpace.Opens (ComplexModel (d+(t+1)))) (h0U : (0 : ComplexModel (d+(t+1)))∈U)
    (c : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+(t+1)) I) →
      ComplexModel (d+(t+1)) → ℂ)
    (hc : ∀a,MDifferentiableOn 𝓘(ℂ,ComplexModel (d+(t+1))) 𝓘(ℂ,ℂ) (c a) U)
    (hrep : ∀a,HolGerm.mk (c a)
      ((holomorphicAt_of_mdifferentiableOn U.isOpen (hc a) h0U).mono fun _ hz=>hz.differentiableAt)=G.germs a)
    (hCos : ∀a,(U : Set (ComplexModel (d+(t+1))))∩complexCoordinatePlane (d+(t+1)) d⊆
      cosupport (d+(t+1)) univ (actualPrincipalCoefficientIdeal (d+(t+1)) (c a)) (normalExponentDegree a.val))
    (E : List (Set U)) (π : Z → U)
    (hπ : IsBlowupAlong (d+(t+1)) ((Subtype.val : U → ComplexModel (d+(t+1))) ⁻¹'
      complexCoordinatePlane (d+(t+1)) d) π)
    (y : Z) (hy : (π y : ComplexModel (d+(t+1)))=0) :
    let w:=fun a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+(t+1)) I)=>
      normalExponentDegree a.val
    let M : MarkedIdeal (d+(t+1)) U:=⟨univ,E,weightedFunctionIdeal w (fun a (z : U)=>c a z),weightedCommonMark w⟩
    let Q:=M.geoTransform ((Subtype.val : U → ComplexModel (d+(t+1))) ⁻¹' complexCoordinatePlane (d+(t+1)) d) π
    let q : Fin (d+(t+1)):=⟨d,by omega⟩
    y∈Q.cosupp →
    ∃(e : Fin (d+(t+1)))(b : Fin (d+(t+1)) → ℂ)
      (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+(t+1))) y y))
      (_hΘ0 : Θ.toFun (chartAt (ComplexModel (d+(t+1))) y y)=0)
      (he : q≤e),
      Θ.source⊆(chartAt (ComplexModel (d+(t+1))) y).target ∧
      (∀z : Z,z∈(chartAt (ComplexModel (d+(t+1))) y).source →
        chartAt (ComplexModel (d+(t+1))) y z∈Θ.source →
        (π z : ComplexModel (d+(t+1)))=actualAnalyticBlowupMap (actualTangentCentreVariables d (t+1)) e b
          (Θ.toFun (chartAt (ComplexModel (d+(t+1))) y z))) ∧
      ∃hp : ∀a,G.germs a∈actualAnalyticCoordinateIdeal (Set.Ici q)^normalExponentDegree a.val,
      ∃f : Fin (d+(t+1)),∃_hqf : q≤f,actualNormalMarkedDirection (Set.Ici q) e b f≠0 ∧
      ∃C : HolGerm (ComplexModel (d+(t+1)))≃ₐ[ℂ]HolGerm (ComplexModel (d+(t+1))),
      ∃u : HolGerm (ComplexModel (d+(t+1))),IsUnit u ∧
      ∃D : ActualAdaptedCurrentSelectorData I G q e f b S,
      ∃P : ActualMarkedFunctionSquare w
        (sameAnalyticNormalNormalizedVertex (d+(t+1)) I G q e he b hp) D.targetFamily.germs
        (actualAdaptedOriginalLabelEquiv D) C u,
        (P.oldDomain : Set (ComplexModel (d+(t+1))))⊆Θ.target ∧
        MarkedIdeal.pullback
          (fun z : P.currentDomain=>actualFlatteningInverseMap y Θ (P.chart.toFun z)) Q=
          actualCurrentNativeWeightedRecord P (fun a=>normalExponentDegree a.val)
            ((fun z : P.oldDomain=>actualFlatteningInverseMap y Θ z) ⁻¹' Q.N)
            (Q.E.map ((fun z : P.oldDomain=>actualFlatteningInverseMap y Θ z) ⁻¹' ·)) := by
  dsimp only
  intro hcut
  let w:=fun a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+(t+1)) I)=>
    normalExponentDegree a.val
  let M0 : MarkedIdeal (d+(t+1)) U:=⟨univ,[],weightedFunctionIdeal w (fun a (z : U)=>c a z),weightedCommonMark w⟩
  let M : MarkedIdeal (d+(t+1)) U:=⟨univ,E,weightedFunctionIdeal w (fun a (z : U)=>c a z),weightedCommonMark w⟩
  let ZC:=((Subtype.val : U → ComplexModel (d+(t+1))) ⁻¹' complexCoordinatePlane (d+(t+1)) d)
  let Q:=M.geoTransform ZC π
  let q : Fin (d+(t+1)):=⟨d,by omega⟩
  have hcu (a) : MDifferentiable 𝓘(ℂ,ComplexModel (d+(t+1))) 𝓘(ℂ,ℂ) (fun z : U=>c a z) := by
    intro z
    exact ((holomorphicAt_of_mdifferentiableOn U.isOpen (hc a) z.property).comp_contMDiff
      (Eventually.of_forall fun _=>(contMDiff_subtype_val (U:=U)).contMDiffAt)).mdifferentiableAt
  have hI:=isCoherent_weightedFunctionIdeal w (fun a (z : U)=>c a z) hcu
  have hcut0 : y∈(M0.geoTransform ZC π).cosupp := by
    change y∈cosupport (d+(t+1)) (M0.geoTransform ZC π).N (M0.geoTransform ZC π).ideal (M0.geoTransform ZC π).d
    rw [geoTransform_N_eq_univ (𝔪:=M0) rfl hπ,
      geoTransform_ideal_eq_controlledTransform (𝔪:=M0) rfl hI hπ,geoTransform_d]
    change y∈cosupport (d+(t+1)) Q.N Q.ideal Q.d at hcut
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
  have hTail : actualTangentCentreVariables d (t+1)=Set.Ici q := by
    ext i
    rw [actualTangentCentreVariables_eq_tail]
    rfl
  have hp : ∀a,G.germs a∈actualAnalyticCoordinateIdeal (Set.Ici q)^normalExponentDegree a.val := by
    intro a
    have h:=hpOld a
    rw [hTail] at h
    exact h
  have hEq (a) : sameAnalyticNormalNormalizedVertex (d+(t+1)) I G q e he b hp a=H a := by
    apply mul_left_cancel₀ (pow_ne_zero (normalExponentDegree a.val)
      (HolomorphicGermReducednessBridge.coordinate_germ_ne_zero e))
    exact (sameAnalyticNormalNormalizedVertex_product (d+(t+1)) I G q e he b hp a).trans
      (by simpa only [hTail,coordinateGerm] using (hProducts a).symm)
  have hFun : sameAnalyticNormalNormalizedVertex (d+(t+1)) I G q e he b hp=H:=funext hEq
  have hOrd : ∀a,sameAnalyticNormalNormalizedVertex (d+(t+1)) I G q e he b hp a∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+(t+1))))^normalExponentDegree a.val := by
    simpa only [hFun] using hOrders
  obtain ⟨f,hqf,hvf,C,u,hu,D,⟨P⟩⟩:=exists_actual_current_marked_function_square
    I G hmem q e he b hp hOrd hred S hContact
  have hIdealN : adaptedIdeal Q.ideal y Θ hΘ0=weightedCompression w
      (sameAnalyticNormalNormalizedVertex (d+(t+1)) I G q e he b hp) := by
    rw [hFun]
    exact hIdeal
  obtain ⟨R,_hChart,_hOld,_hCurrent,_hUnit,hRT,hGeom⟩:=exists_actual_geometric_marked_square
    (w:=w) (old:=sameAnalyticNormalNormalizedVertex (d+(t+1)) I G q e he b hp)
    (current:=D.targetFamily.germs) (labels:=actualAdaptedOriginalLabelEquiv D) (C:=C) (u:=u)
    Q hQ y Θ hΘsrc hΘ0 hIdealN (geoTransform_d (𝔪:=M) ZC π) P
      (fun a=>normalExponentDegree a.val) (fun a=>actualAdaptedOriginalLabelEquiv_degree D a)
  exact ⟨e,b,Θ,hΘ0,he,hΘsrc,hSquare,hp,f,hqf,hvf,C,u,hu,D,R,hRT,hGeom⟩

end
end Hironaka.HironakaActualGeometricMarkedSquare

