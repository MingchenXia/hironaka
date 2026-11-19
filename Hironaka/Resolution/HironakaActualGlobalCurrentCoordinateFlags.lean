import Hironaka.Resolution.HironakaActualHistoricalCoordinateTransport

/-! Literal current block indices and the actual common-domain historical
coordinate flags for the SAME original geometric controlled record. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualGlobalCurrentCoordinateFlags
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
 HironakaActualHistoricalCoordinateTransport HironakaActualGeometricMarkedSquare
 HironakaActualCurrentMarkedFunctionSquares HironakaActualAnalyticAdaptedCurrentSelector
 HironakaActualRelativeNormalJetDivision HironakaActualFormalInitialDiagram
 HironakaActualNormalZeroAnalyticSaturation HironakaActualInheritedNestedContactFlag
 HironakaActualFixedInheritedSelector HironakaActualFixedInheritedSelectorPermutation
 HironakaActualInheritedSourcePermutationFamily HironakaActualOriginalAdaptedMarkedTransport
 HironakaActualRelativeStandardnessNormalPivotPriority HironakaRelativeNormalMonomialBasis
 HironakaActualCoefficientPresentationCentrePower
 HironakaSmoothCentreCoherentDomain HironakaSmoothSubmersionGermIdealColon
 HironakaActualWeightedCoefficientCompression HironakaActualCoherentWeightedCoefficientMarked
 MarkedIdeals MarkedIdealBiholomorphism

private theorem blockCast_val {n : ℕ} {V W : Finset (Fin n →₀ ℕ)}
    (h : V=W) (k : ℕ) (a : fixedSelectorBlock V k) :
    (sourceBlockCast h k a).val=a.val := by
  cases h
  rfl

/-- The TRUE current degree-prefix block is precisely the literal image of
the original block under the SAME pivot permutation; both vertex casts
retain every actual coordinate label. -/
theorem actual_current_block_eq_original_image
    {n : ℕ} {I : Ideal (HolGerm (ComplexModel (n+1)))}
    {G : ActualAnalyticInheritedFamily (n+1) 0 (analyticZeroTaylorIdeal (n+1) I)}
    {q e f : Fin (n+1)} {b : Fin (n+1) → ℂ}
    {S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) I))}
    (D : ActualAdaptedCurrentSelectorData I G q e f b S) (k : ℕ) :
    fixedSelectorBlock (actualInitialVertices MonomialOrder.degLex
      (analyticZeroTaylorIdeal (n+1) (sameAnalyticZeroNormalizedIdeal (n+1) _ D.sourceFamily q D.sourcePower))) k=
      (normalPivotEquiv q f) '' fixedSelectorBlock
        (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) I)) k := by
  let B:=(fixedBlockPermutation (normalPivotEquiv q f)
      (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) I)) k).trans
    ((sourceBlockCast D.permutationVertexSet k).trans (sourceBlockCast D.targetVertexSet k))
  have hVal (a) : (B a).val=normalPivotEquiv q f a.val := by
    dsimp only [B,Equiv.trans_apply]
    rw [blockCast_val,blockCast_val]
    rfl
  ext i
  constructor
  · intro hi
    let j:=B.symm ⟨i,hi⟩
    refine ⟨j.val,j.property,?_⟩
    exact (hVal j).symm.trans (congrArg Subtype.val (B.apply_symm_apply ⟨i,hi⟩))
  · rintro ⟨j,hj,rfl⟩
    exact hVal ⟨j,hj⟩ ▸ (B ⟨j,hj⟩).property

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
supplied. The contact carrier is the actual old carrier trace; on ONE common
subneighborhood, EVERY actual D current coordinate-prefix zero flag is
the literal inverse image of the corresponding old historical flag. -/
theorem exists_actual_global_controlled_current_record_and_coordinate_flags
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
            (Q.E.map ((fun z : P.oldDomain=>actualFlatteningInverseMap y Θ z) ⁻¹' ·)) ∧
        ∃V : Set (ComplexModel (d+(t+1))),IsOpen V ∧ (0 : ComplexModel (d+(t+1)))∈V ∧
          V⊆P.currentDomain ∧ ∀k,∀z∈V,
            (∀i∈fixedSelectorBlock (actualInitialVertices MonomialOrder.degLex
              (analyticZeroTaylorIdeal (d+(t+1)) I)) k,P.chart.toFun z i=0) ↔
            ∀j∈fixedSelectorBlock (actualInitialVertices MonomialOrder.degLex
              (analyticZeroTaylorIdeal (d+(t+1)) (sameAnalyticZeroNormalizedIdeal (d+(t+1)) _
                D.sourceFamily q D.sourcePower))) k,z j=0 := by
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
  obtain ⟨f,hqf,hvf,C,u,hu,D,hCov,hCoord,_hBlockIdeals⟩:=
    exists_actual_current_transport_with_historical_coordinate_flags
      I G hmem q e he b hp hOrd hred S hContact
  obtain ⟨P⟩:=exists_actual_marked_function_square w
    (sameAnalyticNormalNormalizedVertex (d+(t+1)) I G q e he b hp)
    D.targetFamily.germs (actualAdaptedOriginalLabelEquiv D) C u hu hCov
  have hIdealN : adaptedIdeal Q.ideal y Θ hΘ0=weightedCompression w
      (sameAnalyticNormalNormalizedVertex (d+(t+1)) I G q e he b hp) := by
    rw [hFun]
    exact hIdeal
  obtain ⟨R,_hChart,_hOld,_hCurrent,_hUnit,hRT,hGeom⟩:=exists_actual_geometric_marked_square
    (w:=w) (old:=sameAnalyticNormalNormalizedVertex (d+(t+1)) I G q e he b hp)
    (current:=D.targetFamily.germs) (labels:=actualAdaptedOriginalLabelEquiv D) (C:=C) (u:=u)
    Q hQ y Θ hΘsrc hΘ0 hIdealN (geoTransform_d (𝔪:=M) ZC π) P
      (fun a=>normalExponentDegree a.val) (fun a=>actualAdaptedOriginalLabelEquiv_degree D a)
  obtain ⟨O,hO,h0O,_hOS,_hv,_hne,_hCoordFunctions,hFlags⟩:=
    exists_actual_common_coordinate_flag_neighborhood C (normalPivotEquiv q f) u hu
      (fixedSelectorEssential (actualInitialVertices MonomialOrder.degLex
        (analyticZeroTaylorIdeal (d+(t+1)) I))) hCoord R.chart R.chart_zero R.chart_germs
      R.unitFunction R.unitHolomorphicAtZero R.unitGerm
  let V:=O∩(R.currentDomain : Set (ComplexModel (d+(t+1))))
  refine ⟨e,b,Θ,hΘ0,he,hΘsrc,hSquare,hp,f,hqf,hvf,C,u,hu,D,R,hRT,hGeom,
    V,hO.inter R.currentDomain.isOpen,⟨h0O,R.zero_mem_current⟩,inter_subset_right,?_⟩
  intro k z hz
  have hTL : fixedSelectorBlock (actualInitialVertices MonomialOrder.degLex
      (analyticZeroTaylorIdeal (d+(t+1)) I)) k⊆
      fixedSelectorEssential (actualInitialVertices MonomialOrder.degLex
        (analyticZeroTaylorIdeal (d+(t+1)) I)) := by
    rintro i ⟨a,_ha,hai⟩
    exact ⟨a,hai⟩
  have h:=hFlags (fixedSelectorBlock (actualInitialVertices MonomialOrder.degLex
    (analyticZeroTaylorIdeal (d+(t+1)) I)) k) hTL z hz.1
  have heq:=Set.ext_iff.mp (actual_current_block_eq_original_image D k)
  constructor
  · intro ho j hj
    exact h.mp ho j ((heq j).mp hj)
  · intro hn
    apply h.mpr
    intro j hj
    exact hn j ((heq j).mpr hj)

end
end Hironaka.HironakaActualGlobalCurrentCoordinateFlags
