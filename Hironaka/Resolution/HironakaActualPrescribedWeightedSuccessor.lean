import Hironaka.Resolution.HironakaActualPrescribedCentreRebasing

/-! Literal flat-family functions and the ENTIRE actual weighted Q-record
after compatible straightening of the prescribed NEXT actual centre. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualPrescribedWeightedSuccessor
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
 HironakaActualPrescribedCentreRebasing HironakaActualCurrentMarkedFunctionSquares
 HironakaActualFixedInheritedSelector HironakaActualFormalInitialDiagram
 HironakaActualCoefficientPresentationCentrePower HironakaRelativeNormalMonomialBasis
 HironakaActualRelativeNormalJetDivision HironakaActualInheritedNestedContactFlag
 HironakaActualInheritedCurrentSourceRelabel HironakaActualNormalZeroAnalyticSaturation
 HironakaHolomorphicJetChartInvariance OkaRelationSheaf HironakaSmoothCentreCoherentDomain
 HironakaActualWeightedCoefficientCompression HironakaActualCoherentWeightedCoefficientMarked
 HironakaActualFlatCoordinateIntrinsicHS HironakaActualFixedFlatteningHSComparison
 HironakaEmbeddedExceptional RegularAtDimTransport BlowupFlatCoordinates
 HironakaActualRawRecordPullbacks MarkedIdealBiholomorphism MarkedIdeals
 MarkedIdeals.MarkedIdeal RelativePrincipalizationSpan InvertibleIdealQuotient
 HironakaActualGeometricCurrentNeighborhoodHS HironakaActualWholeHSContactWindow
 HironakaRelativeNormalDeformationInitialRelations HironakaHolomorphicPointJets
 GermIdealOrder IdealWeightPowers OrderTaylor MarkedIdealRestrictOpen
 HironakaActualInheritedNeighborhoodMarkedHS HironakaHolomorphicJetRankLoci

variable {n : ℕ}

section FlatFunctions
variable {I : Ideal (HolGerm (ComplexModel n))}
 {G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)}
 {hspan : Ideal.span (range G.germs)=I}
 {S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I))}
 {C₀ : Set (ComplexModel n)} {k : ℕ}

/-- Literal same functions, same historical labels, and actual inverse chart. -/
def prescribedFlatFunctions (T : ActualPrescribedHistoricalFlattening I G hspan S C₀ k)
    (F : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I) → ComplexModel n → ℂ) :=
  fun j z=>F (T.historicalLabels.symm j) (T.chart.invFun z)

theorem prescribedFlatFunctionsHolomorphicAtZero
    (T : ActualPrescribedHistoricalFlattening I G hspan S C₀ k)
    (F : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I) → ComplexModel n → ℂ)
    (hF : ∀a,HolAt (F a) 0) : ∀j,HolAt (prescribedFlatFunctions T F j) 0 :=
  fun j=>holomorphic_comp T.chart.invFun (local_invFun_holomorphic T.chart T.chart_zero)
    (local_invFun_zero T.chart T.chart_zero) (hF (T.historicalLabels.symm j))

theorem prescribedFlatFunctions_germs
    (T : ActualPrescribedHistoricalFlattening I G hspan S C₀ k)
    (F : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I) → ComplexModel n → ℂ)
    (hF : ∀a,HolAt (F a) 0) (hGerms : ∀a,G.germs a=HolGerm.mk (F a) (hF a)) :
    ∀j,HolGerm.mk (prescribedFlatFunctions T F j)
      (prescribedFlatFunctionsHolomorphicAtZero T F hF j)=T.family.germs j := by
  intro j
  have hm:=T.historicalMembers (T.historicalLabels.symm j)
  have hm' : T.family.germs j=(localGermAlgEquiv T.chart T.chart_zero).symm
      (G.germs (T.historicalLabels.symm j)) :=
    (congrArg T.family.germs (T.historicalLabels.apply_symm_apply j)).symm.trans hm
  symm
  refine hm'.trans ?_
  rw [hGerms]
  rfl

end FlatFunctions

private theorem native_inverse_contMDiff
    {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] (x : X)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Θ.source⊆(chartAt (ComplexModel n) x).target)
    (O : Opens (ComplexModel n)) (hO : (O : Set (ComplexModel n))⊆Θ.target) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (fun z : O=>actualFlatteningInverseMap x Θ z) := by
  intro z
  have hmd : ∀ᶠa in 𝓝 (z : ComplexModel n),
      MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n)
        (actualFlatteningInverseMap x Θ) a :=
    eventually_of_mem (Θ.isOpen_target.mem_nhds (hO z.property))
      (fun a ha=>actualFlatteningInverseMap_mdifferentiable x Θ hsrc a ha)
  exact (MarkedIdealOpenBiholomorphism.contMDiffAt_of_eventually_mdifferentiableAt' hmd).comp z
    (contMDiff_subtype_val z)

private theorem square_map_contMDiff
    {ι κ : Type} [Fintype ι] [Fintype κ] {w : ι → ℕ}
    {old : ι → HolGerm (ComplexModel n)} {current : κ → HolGerm (ComplexModel n)}
    {labels : ι≃κ} {Cg : HolGerm (ComplexModel n)≃ₐ[ℂ]HolGerm (ComplexModel n)}
    {u : HolGerm (ComplexModel n)} (P : ActualMarkedFunctionSquare w old current labels Cg u) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (actualMarkedSquareMap P) := by
  have hForward : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (fun z : P.currentDomain=>P.chart.toFun z) := by
    intro z
    have hmd : ∀ᶠa in 𝓝 (z : ComplexModel n),MDifferentiableAt 𝓘(ℂ,ComplexModel n)
        𝓘(ℂ,ComplexModel n) P.chart.toFun a :=
      eventually_of_mem (P.chart.isOpen_source.mem_nhds (P.inside_chart z.property)) fun a ha=>
        (P.chart.toFun_holomorphic.differentiableAt (P.chart.isOpen_source.mem_nhds ha)).mdifferentiableAt
    exact (MarkedIdealOpenBiholomorphism.contMDiffAt_of_eventually_mdifferentiableAt' hmd).comp z
      (contMDiff_subtype_val z)
  exact BlowupRestrictOpen.contMDiff_opens_mk hForward (fun z=>P.inside_old z.property)

/-- Transparent complete native weighted-record output for the SAME flat
family; always produced from the original stage square below. -/
def ActualFlatWeightedRecordLaws
    {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    {ι : Type} [Fintype ι] {I : Ideal (HolGerm (ComplexModel n))}
    {G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)}
    {w : ι → ℕ} {old : ι → HolGerm (ComplexModel n)}
    {labels : ι≃actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)}
    {Cg : HolGerm (ComplexModel n)≃ₐ[ℂ]HolGerm (ComplexModel n)} {u : HolGerm (ComplexModel n)}
    (Q : MarkedIdeal n X) (x : X) (P : ActualMarkedFunctionSquare w old G.germs labels Cg u)
    (Ξ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hΞ0 : Ξ.toFun (chartAt (ComplexModel n) x x)=0)
    {hspan : Ideal.span (range G.germs)=I}
    {S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I))}
    {C₀ : Set (ComplexModel n)} {k : ℕ}
    (T : ActualPrescribedHistoricalFlattening I G hspan S C₀ k) : Prop :=
    let Ω:=LocalHolomorphicEquivAt.comp Ξ T.chart hΞ0
    let F:=prescribedFlatFunctions T P.currentFunctions
    (∀j,HolGerm.mk (F j)
      (prescribedFlatFunctionsHolomorphicAtZero T P.currentFunctions P.currentHolomorphicAtZero j)=T.family.germs j) ∧
    (∀j,DifferentiableOn ℂ (F j) Ω.target) ∧
    actualRebasedRecord Q x Ω=
      (⟨univ,Q.E.map ((fun z : actualRebaseModel x Ω=>actualFlatteningInverseMap x Ω z) ⁻¹' ·),
        weightedFunctionIdeal (fun j=>normalExponentDegree j.val)
          (fun j (z : actualRebaseModel x Ω)=>F j z),
        weightedCommonMark (fun j : actualInitialVertices MonomialOrder.degLex
          (actualInheritedCurrentSourceIdeal (prescribedFlatOriginIdeal I T.chart T.chart_zero))=>
          normalExponentDegree j.val)⟩ : MarkedIdeal n (actualRebaseModel x Ω))

/-- The entire actual rebased Q-record is precisely the native weighted
FUNCTION record of the produced flat historical family, on the exact true
flat open.  No weighted-record comparison or coefficient function is given. -/
theorem actual_same_prescribed_flat_weighted_record
    {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    {ι : Type} [Fintype ι] {I : Ideal (HolGerm (ComplexModel n))}
    {G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)}
    {w : ι → ℕ} {old : ι → HolGerm (ComplexModel n)}
    {labels : ι≃actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)}
    {Cg : HolGerm (ComplexModel n)≃ₐ[ℂ]HolGerm (ComplexModel n)} {u : HolGerm (ComplexModel n)}
    (Q : MarkedIdeal n X) (hQhol : ∀x f,Q.ideal.mem x f → HolomorphicAt n f x) (hQN : Q.N=univ)
    (x : X) (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Θ.source⊆(chartAt (ComplexModel n) x).target)
    (hΘ0 : Θ.toFun (chartAt (ComplexModel n) x x)=0)
    (P : ActualMarkedFunctionSquare w old G.germs labels Cg u)
    (hOldTarget : (P.oldDomain : Set (ComplexModel n))⊆Θ.target)
    (hRecord : MarkedIdeal.pullback
      (fun z : P.currentDomain=>actualFlatteningInverseMap x Θ (P.chart.toFun z)) Q=
      actualCurrentNativeWeightedRecord P (fun a=>normalExponentDegree a.val)
        ((fun z : P.oldDomain=>actualFlatteningInverseMap x Θ z) ⁻¹' Q.N)
        (Q.E.map ((fun z : P.oldDomain=>actualFlatteningInverseMap x Θ z) ⁻¹' ·)))
    (Ξ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hΞ0 : Ξ.toFun (chartAt (ComplexModel n) x x)=0)
    (hInv : Ξ.invFun=Θ.invFun ∘ P.chart.toFun) (hCurrent : Ξ.target⊆P.currentDomain)
    (hspan : Ideal.span (range G.germs)=I)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)))
    (C₀ : Set (ComplexModel n)) (k : ℕ)
    (T : ActualPrescribedHistoricalFlattening I G hspan S C₀ k) :
    let Ω:=LocalHolomorphicEquivAt.comp Ξ T.chart hΞ0
    let F:=prescribedFlatFunctions T P.currentFunctions
    (∀j,HolGerm.mk (F j)
      (prescribedFlatFunctionsHolomorphicAtZero T P.currentFunctions P.currentHolomorphicAtZero j)=T.family.germs j) ∧
    (∀j,DifferentiableOn ℂ (F j) Ω.target) ∧
    actualRebasedRecord Q x Ω=
      (⟨univ,Q.E.map ((fun z : actualRebaseModel x Ω=>actualFlatteningInverseMap x Ω z) ⁻¹' ·),
        weightedFunctionIdeal (fun j=>normalExponentDegree j.val)
          (fun j (z : actualRebaseModel x Ω)=>F j z),
        weightedCommonMark (fun j : actualInitialVertices MonomialOrder.degLex
          (actualInheritedCurrentSourceIdeal (prescribedFlatOriginIdeal I T.chart T.chart_zero))=>
          normalExponentDegree j.val)⟩ : MarkedIdeal n (actualRebaseModel x Ω)) := by
  intro Ω F
  let E:=(localGermAlgEquiv T.chart T.chart_zero).symm
  let χ:=HironakaEmbeddedExceptional.LocalHolomorphicEquivAt.symmAt T.chart T.chart_zero
  have hχ0 : χ.toFun 0=0:=local_invFun_zero T.chart T.chart_zero
  have hχE : localGermAlgEquiv χ hχ0=E := by
    apply AlgEquiv.ext
    intro a
    rfl
  have hΩ0 : Ω.toFun (chartAt (ComplexModel n) x x)=0 := by
    change T.chart.toFun (Ξ.toFun (chartAt (ComplexModel n) x x))=0
    rw [hΞ0]
    exact T.chart_zero
  let PF : ActualMarkedFunctionSquare (fun a=>normalExponentDegree a.val) G.germs T.family.germs
      T.historicalLabels E (1 : HolGerm (ComplexModel n)) := {
    chart:=χ
    chart_zero:=hχ0
    chart_germs:=hχE
    oldFunctions:=P.currentFunctions
    oldHolomorphicAtZero:=P.currentHolomorphicAtZero
    oldGerms:=P.currentGerms
    currentFunctions:=F
    currentHolomorphicAtZero:=prescribedFlatFunctionsHolomorphicAtZero T P.currentFunctions P.currentHolomorphicAtZero
    currentGerms:=fun j=>(prescribedFlatFunctions_germs T P.currentFunctions P.currentHolomorphicAtZero P.currentGerms j).symm
    unitFunction:=fun _=>1
    unitHolomorphicAtZero:=Eventually.of_forall fun _=>differentiableAt_const (1 : ℂ)
    unitGerm:=rfl
    oldDomain:=P.currentDomain
    zero_mem_old:=P.zero_mem_current
    currentDomain:=actualRebaseModel x Ω
    zero_mem_current:=actualFlattening_target_zero_mem x Ω hΩ0
    inside_chart:=fun _ hz=>hz.1
    inside_old:=fun _ hz=>hCurrent hz.2
    oldHolomorphicOn:=P.currentHolomorphicOn
    currentHolomorphicOn:=fun j=>(P.currentHolomorphicOn (T.historicalLabels.symm j)).comp
      (T.chart.invFun_holomorphic.mono (fun _ hz=>hz.1)) (fun _ hz=>hCurrent hz.2)
    unitHolomorphicOn:=differentiableOn_const (1 : ℂ)
    unitNonzero:=fun _ _=>one_ne_zero
    memberSquare:=by
      intro a z _hz
      change P.currentFunctions a (T.chart.invFun z)=1^normalExponentDegree a.val*
        P.currentFunctions (T.historicalLabels.symm (T.historicalLabels a)) (T.chart.invFun z)
      simp only [Equiv.symm_apply_apply,one_pow,one_mul] }
  let H : P.currentDomain → X:=fun z=>actualFlatteningInverseMap x Θ (P.chart.toFun z)
  let Base:=currentCoordinateFlattening x Θ hΘ0 P.chart P.chart_zero
  have hBaseSrc : Base.source⊆(chartAt (ComplexModel n) x).target:=fun _ hz=>hsrc hz.1
  have hBaseTarget : (P.currentDomain : Set (ComplexModel n))⊆Base.target:=
    fun z hz=>⟨P.inside_chart hz,hOldTarget (P.inside_old hz)⟩
  have hH : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ H:=
    native_inverse_contMDiff x Base hBaseSrc P.currentDomain hBaseTarget
  have hPoints : ∀z : PF.currentDomain,H (actualMarkedSquareMap PF z)=
      actualFlatteningInverseMap x Ω z := by
    intro z
    change (chartAt (ComplexModel n) x).symm (Θ.invFun (P.chart.toFun (T.chart.invFun z)))=
      (chartAt (ComplexModel n) x).symm (Ξ.invFun (T.chart.invFun z))
    rw [hInv]
    rfl
  have hCompose : MarkedIdeal.pullback (actualMarkedSquareMap PF) (MarkedIdeal.pullback H Q)=
      actualRebasedRecord Q x Ω :=
    marked_pullback_comp_hhol hQhol hH (square_map_contMDiff PF) hPoints
  have hOld : MarkedIdeal.pullback H Q=
      actualOldNativeWeightedRecord PF (H ⁻¹' Q.N) (Q.E.map (H ⁻¹' ·)) := by
    rw [hRecord]
    refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl ?_ rfl rfl
    simp only [actualCurrentNativeWeightedRecord,actualOldNativeWeightedRecord,List.map_map]
    rfl
  have hSquare:=actual_square_native_weighted_record_eq PF (fun j=>normalExponentDegree j.val)
    (fun a=>(T.historicalLabels_degree a).symm) (H ⁻¹' Q.N) (Q.E.map (H ⁻¹' ·))
  have hFull:=hCompose.symm.trans
    ((congrArg (MarkedIdeal.pullback (actualMarkedSquareMap PF)) hOld).trans hSquare)
  refine ⟨prescribedFlatFunctions_germs T P.currentFunctions P.currentHolomorphicAtZero P.currentGerms,
    PF.currentHolomorphicOn, hFull.trans ?_⟩
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ ?_ rfl rfl
  · change (actualMarkedSquareMap PF ⁻¹' (H ⁻¹' Q.N))=univ
    rw [hQN,preimage_univ,preimage_univ]
  · change (Q.E.map (H ⁻¹' ·)).map ((actualMarkedSquareMap PF) ⁻¹' ·)=
      Q.E.map ((fun z : actualRebaseModel x Ω=>actualFlatteningInverseMap x Ω z) ⁻¹' ·)
    rw [List.map_map]
    apply List.map_congr_left
    intro B _hB
    ext z
    change H (actualMarkedSquareMap PF z)∈B ↔ actualFlatteningInverseMap x Ω z∈B
    exact Iff.of_eq (congrArg (fun q=>q∈B) (hPoints z))

/-- The actual prescribed centre internally supplies every individual flat
function's marked cosupport condition, on the true source open.  The native
compressed marked ideal and the strict vanishing ideal remain distinct. -/
theorem actual_flat_centre_coefficient_orders
    {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    {κ : Type} [Fintype κ]
    (Q : MarkedIdeal n X) (x : X)
    (Ω : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Ω.source⊆(chartAt (ComplexModel n) x).target)
    (C : Set X) (hC : C⊆Q.cosupp) (k : ℕ)
    (hCentre : (fun z : actualRebaseModel x Ω=>actualFlatteningInverseMap x Ω z) ⁻¹' C=
      (Subtype.val : actualRebaseModel x Ω → ComplexModel n) ⁻¹' complexCoordinatePlane n k)
    (w : κ → ℕ) (hw : ∀a,0<w a) (F : κ → ComplexModel n → ℂ)
    (hF : ∀a,DifferentiableOn ℂ (F a) Ω.target)
    (hRecord : actualRebasedRecord Q x Ω=
      (⟨univ,Q.E.map ((fun z : actualRebaseModel x Ω=>actualFlatteningInverseMap x Ω z) ⁻¹' ·),
        weightedFunctionIdeal w (fun a (z : actualRebaseModel x Ω)=>F a z),
        weightedCommonMark w⟩ : MarkedIdeal n (actualRebaseModel x Ω))) :
    ∀a,Ω.target∩complexCoordinatePlane n k⊆(actualInheritedPrincipalMarked (F a) (w a)).cosupp := by
  let U:=actualRebaseModel x Ω
  let H : U → X:=fun z=>actualFlatteningInverseMap x Ω z
  have hH : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ H:=
    contMDiff_actual_flat_inverse Ω hsrc
  have hNative (a) : MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (fun z : U=>F a z) := by
    intro z
    exact ((holomorphicAt_of_mdifferentiableOn U.isOpen
      (mdifferentiableOn_iff_differentiableOn.mpr (hF a)) z.property).comp_contMDiff
      (Eventually.of_forall fun _=>(contMDiff_subtype_val (U:=U)).contMDiffAt)).mdifferentiableAt
  intro a z hz
  let p : U:=⟨z,hz.1⟩
  have hzC : H p∈C:=(congrArg (fun B : Set U=>p∈B) hCentre).mpr hz.2
  have hp : p∈(actualRebasedRecord Q x Ω).cosupp := by
    refine ⟨(hC hzC).1,fun g hg=>?_⟩
    refine IdealOrderArithmetic.IsInSpanAt.vanishesToOrderOn (GermIdeal.mem_pullback_iff.mp hg) ?_
    rintro _ ⟨f,hf,rfl⟩
    exact MonomialPartEtale.vanishesToOrderOn_comp
      (Eventually.of_forall fun q=>(hH q).mdifferentiableAt (by simp)) ((hC hzC).2 f hf)
  rw [hRecord] at hp
  simp only [MarkedIdeal.cosupp] at hp
  have hAll : p∈⋂a,cosupport n univ
      (finiteFunctionIdeal (fun _ : Unit=>(fun q : U=>F a q))) (w a) :=
    (congrArg (fun B : Set U=>p∈B)
      (cosupport_weightedFunctionIdeal w hw (fun a (q : U)=>F a q) hNative)).mp hp
  have hv:=(mem_cosupport_finiteFunctionIdeal_iff
    (fun _ : Unit=>(fun q : U=>F a q)) p (w a)
    (fun _=>Eventually.of_forall fun q=>hNative a q)).mp (mem_iInter.mp hAll a) ()
  have hExt:=mem_idealPow_pointIdeal_extendOpens U (w a)
    (mem_idealPow_of_vanishesToOrderOn_univ hv)
  have hAmbient : (idealPow (pointIdeal n z) (w a)).mem z (F a) := by
    apply mem_idealPow_congr hExt
    filter_upwards [Ω.isOpen_target.mem_nhds hz.1] with q hq
    change extendOpens U (fun q : U=>F a q) (⟨q,hq⟩ : U).val=F a q
    rw [extendOpens_val]
  have hf : HolAt (F a) z:=eventually_of_mem (Ω.isOpen_target.mem_nhds hz.1) fun q hq=>
    (hF a).differentiableAt (Ω.isOpen_target.mem_nhds hq)
  apply (mem_actualInheritedPrincipalMarked_cosupp_iff (F a) z hf (w a)).mpr
  exact (translatedGerm_mem_maximalIdeal_pow_iff_pointIdeal z (F a) hf (w a)).mpr hAmbient

/-- The true individual source marks on the prescribed coordinate plane. -/
def ActualFlatCentreOrders
    {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    {I : Ideal (HolGerm (ComplexModel n))}
    {G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)}
    {hspan : Ideal.span (range G.germs)=I}
    {S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I))}
    {C₀ : Set (ComplexModel n)} {k : ℕ}
    (x : X) (Ξ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hΞ0 : Ξ.toFun (chartAt (ComplexModel n) x x)=0)
    (T : ActualPrescribedHistoricalFlattening I G hspan S C₀ k)
    (F : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I) → ComplexModel n → ℂ) : Prop :=
    let Ω:=LocalHolomorphicEquivAt.comp Ξ T.chart hΞ0
    ∀j : actualInitialVertices MonomialOrder.degLex
      (actualInheritedCurrentSourceIdeal (prescribedFlatOriginIdeal I T.chart T.chart_zero)),
      Ω.target∩complexCoordinatePlane n k⊆
        (actualInheritedPrincipalMarked (prescribedFlatFunctions T F j) (normalExponentDegree j.val)).cosupp

private theorem flat_centre_orders_from_weighted_family
    {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    {ι : Type} [Fintype ι] {I : Ideal (HolGerm (ComplexModel n))}
    {G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)}
    {w : ι → ℕ} {old : ι → HolGerm (ComplexModel n)}
    {labels : ι≃actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)}
    {Cg : HolGerm (ComplexModel n)≃ₐ[ℂ]HolGerm (ComplexModel n)} {u : HolGerm (ComplexModel n)}
    {hspan : Ideal.span (range G.germs)=I}
    {S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I))}
    {C₀ : Set (ComplexModel n)} {k : ℕ}
    (Q : MarkedIdeal n X) (x : X) (P : ActualMarkedFunctionSquare w old G.germs labels Cg u)
    (Ξ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hΞ0 : Ξ.toFun (chartAt (ComplexModel n) x x)=0)
    (T : ActualPrescribedHistoricalFlattening I G hspan S C₀ k)
    (hsrc : (LocalHolomorphicEquivAt.comp Ξ T.chart hΞ0).source⊆(chartAt (ComplexModel n) x).target)
    (C : Set X) (hC : C⊆Q.cosupp)
    (hCentre : (fun z : actualRebaseModel x (LocalHolomorphicEquivAt.comp Ξ T.chart hΞ0)=>
        actualFlatteningInverseMap x (LocalHolomorphicEquivAt.comp Ξ T.chart hΞ0) z) ⁻¹' C=
      (Subtype.val : actualRebaseModel x (LocalHolomorphicEquivAt.comp Ξ T.chart hΞ0) → ComplexModel n) ⁻¹'
        complexCoordinatePlane n k)
    (hWeighted : ActualFlatWeightedRecordLaws Q x P Ξ hΞ0 T)
    (hw : ∀j : actualInitialVertices MonomialOrder.degLex
      (actualInheritedCurrentSourceIdeal (prescribedFlatOriginIdeal I T.chart T.chart_zero)),
      0<normalExponentDegree j.val) : ActualFlatCentreOrders x Ξ hΞ0 T P.currentFunctions := by
  let Ω:=LocalHolomorphicEquivAt.comp Ξ T.chart hΞ0
  let V:=actualInitialVertices MonomialOrder.degLex
    (actualInheritedCurrentSourceIdeal (prescribedFlatOriginIdeal I T.chart T.chart_zero))
  let wf : V → ℕ:=fun j=>normalExponentDegree j.val
  let F : V → ComplexModel n → ℂ:=prescribedFlatFunctions T P.currentFunctions
  have hF : ∀j,DifferentiableOn ℂ (F j) Ω.target:=hWeighted.2.1
  have hRecord : actualRebasedRecord Q x Ω=
      (⟨univ,Q.E.map ((fun z : actualRebaseModel x Ω=>actualFlatteningInverseMap x Ω z) ⁻¹' ·),
        weightedFunctionIdeal wf (fun j (z : actualRebaseModel x Ω)=>F j z),
        weightedCommonMark wf⟩ : MarkedIdeal n (actualRebaseModel x Ω)) := hWeighted.2.2
  exact actual_flat_centre_coefficient_orders (κ:=V) Q x Ω hsrc C hC k hCentre wf hw F hF hRecord

section OriginalStage
variable {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- Complete SAME-stage output including literal flat functions, the whole
native weighted record and unchanged positive historical degrees. -/
def ActualPrescribedWeightedRebaseLaws
    {ι : Type} [Fintype ι] {I : Ideal (HolGerm (ComplexModel n))}
    {G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)}
    {w : ι → ℕ} {old : ι → HolGerm (ComplexModel n)}
    {labels : ι≃actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)}
    {Cg : HolGerm (ComplexModel n)≃ₐ[ℂ]HolGerm (ComplexModel n)} {u : HolGerm (ComplexModel n)}
    (Q : MarkedIdeal n X) (x : X)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (P : ActualMarkedFunctionSquare w old G.germs labels Cg u) (W : Set X)
    (hspan : Ideal.span (range G.germs)=I)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)))
    (R : ℕ → ℕ)
    (PHS : ActualGeometricInheritedNeighborhoodHS (actualHistoricalStageSheaf x Θ P.chart W) I G R) : Prop :=
    ∀(Y : Type) [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y],
    ∀(C : Set X)(ρ : Y → X)(hρ : IsBlowupAlong n C ρ),x∈C → C⊆Q.cosupp →
    ∃(Ξ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
      (_hΞsrc : Ξ.source⊆(chartAt (ComplexModel n) x).target)
      (hΞ0 : Ξ.toFun (chartAt (ComplexModel n) x x)=0),
      Ξ.target=PHS.neighborhood ∧ Ξ.invFun=Θ.invFun ∘ P.chart.toFun ∧
      ∃k,∃T : ActualPrescribedHistoricalFlattening I G hspan S (actualFixedFlatteningSet x Ξ C) k,
      let Ω:=LocalHolomorphicEquivAt.comp Ξ T.chart hΞ0
      ∃hΩsrc : Ω.source⊆(chartAt (ComplexModel n) x).target,
      ∃_hΩ0 : Ω.toFun (chartAt (ComplexModel n) x x)=0,
      ((fun z : actualRebaseModel x Ω=>actualFlatteningInverseMap x Ω z) ⁻¹' C=
        (Subtype.val : actualRebaseModel x Ω → ComplexModel n) ⁻¹' complexCoordinatePlane n k) ∧
      (∀z∈Ω.target,∀v,(GermIdeal.pullback (m:=n) T.chart.invFun
        (actualHistoricalStageSheaf x Θ P.chart W)).mem z v ↔
        (vanishingIdeal (n:=n) (actualFixedFlatteningSet x Ω W)).mem z v) ∧
      prescribedFlatOriginIdeal I T.chart T.chart_zero=
        originalCoherentOriginIdeal (vanishingIdeal (n:=n) (actualFixedFlatteningSet x Ω W)) ∧
      ActualPrescribedNextBlowupLaws Q x Ω hΩsrc C ρ hρ W ∧
      ActualFlatWeightedRecordLaws Q x P Ξ hΞ0 T ∧
      (∀j : actualInitialVertices MonomialOrder.degLex
        (actualInheritedCurrentSourceIdeal (prescribedFlatOriginIdeal I T.chart T.chart_zero)),
        0<normalExponentDegree j.val) ∧
      ActualFlatCentreOrders x Ξ hΞ0 T P.currentFunctions

theorem prescribed_weighted_rebase_of_actual_stage
    {ι : Type} [Fintype ι] {I : Ideal (HolGerm (ComplexModel n))}
    {G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)}
    {w : ι → ℕ} {old : ι → HolGerm (ComplexModel n)}
    {labels : ι≃actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)}
    {Cg : HolGerm (ComplexModel n)≃ₐ[ℂ]HolGerm (ComplexModel n)} {u : HolGerm (ComplexModel n)}
    (Q : MarkedIdeal n X) (hQhol : ∀x f,Q.ideal.mem x f → HolomorphicAt n f x) (hQN : Q.N=univ)
    (x : X) (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Θ.source⊆(chartAt (ComplexModel n) x).target)
    (hΘ0 : Θ.toFun (chartAt (ComplexModel n) x x)=0)
    (P : ActualMarkedFunctionSquare w old G.germs labels Cg u)
    (hOldTarget : (P.oldDomain : Set (ComplexModel n))⊆Θ.target)
    (hRecord : MarkedIdeal.pullback
      (fun z : P.currentDomain=>actualFlatteningInverseMap x Θ (P.chart.toFun z)) Q=
      actualCurrentNativeWeightedRecord P (fun a=>normalExponentDegree a.val)
        ((fun z : P.oldDomain=>actualFlatteningInverseMap x Θ z) ⁻¹' Q.N)
        (Q.E.map ((fun z : P.oldDomain=>actualFlatteningInverseMap x Θ z) ⁻¹' ·)))
    (W : Set X) (hspan : Ideal.span (range G.germs)=I)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)))
    (R : ℕ → ℕ)
    (PHS : ActualGeometricInheritedNeighborhoodHS (actualHistoricalStageSheaf x Θ P.chart W) I G R)
    (hDomain : PHS.neighborhood⊆P.currentDomain)
    (hwCurrent : ∀a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I),
      0<normalExponentDegree a.val)
    (hRebase : ActualPrescribedStageRebaseLaws Q x Θ P W hspan S R PHS) :
    ActualPrescribedWeightedRebaseLaws Q x Θ P W hspan S R PHS := by
  intro Y _ _ _ Cnext ρ hρ hxC hC
  obtain ⟨Ξ,hΞsrc,hΞ0,hTarget,hInv,k,T,hΩsrc,hΩ0,hCentre,hWhole,hFlatOrigin,hNext⟩:=
    hRebase Y Cnext ρ hρ hxC hC
  have hCurrent : Ξ.target⊆P.currentDomain:=fun z hz=>hDomain (hTarget ▸ hz)
  have hwFlat : ∀j : actualInitialVertices MonomialOrder.degLex
      (actualInheritedCurrentSourceIdeal (prescribedFlatOriginIdeal I T.chart T.chart_zero)),
      0<normalExponentDegree j.val := by
    intro j
    obtain ⟨a,rfl⟩:=T.historicalLabels.surjective j
    exact (congrArg (fun q : ℕ=>0<q) (T.historicalLabels_degree a)).mpr (hwCurrent a)
  have hWeighted : ActualFlatWeightedRecordLaws Q x P Ξ hΞ0 T :=
    actual_same_prescribed_flat_weighted_record Q hQhol hQN x Θ hsrc hΘ0 P hOldTarget hRecord
      Ξ hΞ0 hInv hCurrent hspan S (actualFixedFlatteningSet x Ξ Cnext) k T
  have hFlatCos:=flat_centre_orders_from_weighted_family Q x P Ξ hΞ0 T hΩsrc Cnext hC hCentre hWeighted hwFlat
  exact ⟨Ξ,hΞsrc,hΞ0,hTarget,hInv,k,T,hΩsrc,hΩ0,hCentre,hWhole,hFlatOrigin,hNext,hWeighted,hwFlat,hFlatCos⟩

end OriginalStage

open Hironaka.BlowupSequences HironakaActualSameCurrentGeometricStage
 HironakaActualSameStageSelectedCarrierTransport HironakaActualGeometricAdaptedCurrentSelector
 HironakaActualAnalyticAdaptedCurrentSelector HironakaActualCurrentMarkedFunctionSquares
 HironakaActualGeometricMarkedSquare HironakaActualControlledNeighborhoodGenerators
 HironakaActualNormalMarkedDirection HironakaActualAnalyticBlowupTaylor
 HironakaActualFiniteCoefficientIdeals HironakaActualCoefficientAnalyticBlowup
 HironakaActualOriginalAdaptedMarkedTransport HironakaRelativeNormalDeformationInitialRelations
 HironakaActualInheritedSourcePermutationFamily BlowupControlledTransform
 MarkedIdeals.MarkedIdeal InvertibleIdealQuotient
 MarkedIdeals GermIdealOrder HironakaActualNormalAllDirectionAnalyticSaturation
 HironakaActualGlobalInheritedCut HironakaActualGeometricAdaptedCurrentFamily
 HironakaRelativeNormalCoherentTranslatedJets HironakaSmoothCentreCoherentDomain
 HironakaActualFixedFlatteningHSComparison HironakaActualSingularChartTransport
 MarkedIdealBiholomorphism HironakaActualWeightedCoefficientCompression
 HironakaActualCoherentWeightedCoefficientMarked

/-- Original source geometry internally produces the SAME actual geometric
stage and every prescribed-next rebase together with its literal weighted
FUNCTION source record.  No flat coefficient or comparison input is supplied. -/
theorem exists_actual_geometric_stage_prescribed_weighted_source
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
          (∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=d+(t+2)) (strictTransform (d+(t+2)) π W)) y ℓ=
            hilbertSamuelAt (vanishingIdeal (n:=d+(t+2)) W) (π y) ℓ) ∧
          ActualSelectedContactWindowLaws S
            (sameAnalyticNormalNormalizedVertex (d+(t+2)) I G q e he b hp)
            (actualAdaptedHistoricalCurrentSource D).selector D.targetFamily.germs
            A (hilbertSamuelValue I) P.chart.toFun PHS.neighborhood ∧
          ActualPrescribedStageRebaseLaws Q y Θ P (strictTransform (d+(t+2)) π W)
            D.targetSpan (actualAdaptedHistoricalCurrentSource D).selector (hilbertSamuelValue I) PHS ∧
          ActualPrescribedWeightedRebaseLaws Q y Θ P (strictTransform (d+(t+2)) π W)
            D.targetSpan (actualAdaptedHistoricalCurrentSource D).selector (hilbertSamuelValue I) PHS := by
  dsimp only
  intro hcut
  let w:=fun a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+(t+2)) I)=>
    normalExponentDegree a.val
  let M : MarkedIdeal (d+(t+2)) U:=⟨univ,E,weightedFunctionIdeal w (fun a (z : U)=>c a z),weightedCommonMark w⟩
  let ZC:=((Subtype.val : U → ComplexModel (d+(t+2))) ⁻¹' complexCoordinatePlane (d+(t+2)) d)
  let Q:=M.geoTransform ZC π
  have hQN : Q.N=univ:=geoTransform_N_eq_univ (𝔪:=M) rfl hπ
  have hQhol : ∀z f,Q.ideal.mem z f → HolomorphicAt (d+(t+2)) f z := by
    intro z f hf
    exact hf.1
  obtain ⟨e,b,Θ,hΘ0,he,hΘsrc,hSquare,hp,f,hqf,hvf,Cg,u,hu,D,P,hOldTarget,hRecord,
    hStrict,hOriginCurrent,PHS,hRepresentatives,hPHS,hMap,hFlags,hIntrinsic,hContactLaws,hRebaseLaws⟩:=
    exists_actual_geometric_stage_prescribed_rebasing I G hmem hw S hred hContact
      U h0U c hc hrep hCos E π hπ y hy W hWa Φ hΦsrc hΦ0 hΦid hΦdom hOrigin hcut
  refine ⟨e,b,Θ,hΘ0,he,hΘsrc,hSquare,hp,f,hqf,hvf,Cg,u,hu,D,P,hOldTarget,hRecord,
    hStrict,hOriginCurrent,PHS,hRepresentatives,hPHS,hMap,hFlags,hIntrinsic,hContactLaws,hRebaseLaws,?_⟩
  have hwCurrent : ∀a : actualInitialVertices MonomialOrder.degLex
      (analyticZeroTaylorIdeal (d+(t+2)) (actualAdaptedHistoricalCurrentSource D).ideal),
      0<normalExponentDegree a.val := by
    intro a
    obtain ⟨a,rfl⟩:=(actualAdaptedOriginalLabelEquiv D).surjective a
    rw [actualAdaptedOriginalLabelEquiv_degree D a]
    exact hw a
  exact prescribed_weighted_rebase_of_actual_stage Q hQhol hQN y Θ hΘsrc hΘ0 P hOldTarget hRecord
    (strictTransform (d+(t+2)) π W) D.targetSpan (actualAdaptedHistoricalCurrentSource D).selector
    (hilbertSamuelValue I) PHS hPHS hwCurrent hRebaseLaws


end
end Hironaka.HironakaActualPrescribedWeightedSuccessor
