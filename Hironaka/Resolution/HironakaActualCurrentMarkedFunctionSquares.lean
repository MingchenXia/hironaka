import Hironaka.Resolution.HironakaActualOriginalAdaptedMarkedTransport
import Hironaka.Resolution.HironakaActualGermEquivLocalRealization
import Hironaka.Resolution.HironakaActualCoherentWeightedCoefficientMarked
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Hironaka.Blowup.BlowupRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdealOpenBiholomorphism

/-! Same actual marked germs are realized SIMULTANEOUSLY by genuine functions
on one common local chart, with one nowhere-zero holomorphic unit. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualCurrentMarkedFunctionSquares
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm HironakaHolomorphicJetChartInvariance
 HironakaActualGermEquivLocalRealization HironakaActualOriginalAdaptedMarkedTransport
 HironakaActualCoefficientPresentationCentrePower HironakaRelativeNormalMonomialBasis
 HironakaActualFormalInitialDiagram HironakaActualRelativeNormalJetDivision
 HironakaActualInheritedNestedContactFlag HironakaActualNormalZeroAnalyticSaturation
 HironakaActualNormalAllDirectionAnalyticSaturation HironakaActualFixedInheritedSelector
 HironakaActualAnalyticAdaptedCurrentSelector HironakaActualNormalMarkedDirection
 HironakaActualAnalyticBlowupTaylor HironakaActualCoherentWeightedCoefficientMarked
 RelativePrincipalizationSpan InvertibleIdealQuotient GermIdealPullbackCalculus
 HironakaActualWeightedCoefficientCompression MarkedIdeals MarkedIdealBiholomorphism
variable {n : ℕ}

/-- All maps, representatives and one common actual domain are OUTPUT data.
The SAME C,u and SAME old/current germs occur in every literal equation. -/
structure ActualMarkedFunctionSquare {ι κ : Type} [Fintype ι] [Fintype κ]
    (w : ι → ℕ) (old : ι → HolGerm (ComplexModel n)) (current : κ → HolGerm (ComplexModel n))
    (labels : ι≃κ) (C : HolGerm (ComplexModel n)≃ₐ[ℂ]HolGerm (ComplexModel n))
    (u : HolGerm (ComplexModel n)) where
  chart : LocalHolomorphicEquivAt (n:=n) (0 : ComplexModel n)
  chart_zero : chart.toFun 0=0
  chart_germs : localGermAlgEquiv chart chart_zero=C
  oldFunctions : ι → ComplexModel n → ℂ
  oldHolomorphicAtZero : ∀i,∀ᶠz in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ (oldFunctions i) z
  oldGerms : ∀i,old i=HolGerm.mk (oldFunctions i) (oldHolomorphicAtZero i)
  currentFunctions : κ → ComplexModel n → ℂ
  currentHolomorphicAtZero : ∀j,∀ᶠz in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ (currentFunctions j) z
  currentGerms : ∀j,current j=HolGerm.mk (currentFunctions j) (currentHolomorphicAtZero j)
  unitFunction : ComplexModel n → ℂ
  unitHolomorphicAtZero : ∀ᶠz in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ unitFunction z
  unitGerm : u=HolGerm.mk unitFunction unitHolomorphicAtZero
  oldDomain : TopologicalSpace.Opens (ComplexModel n)
  zero_mem_old : (0 : ComplexModel n)∈oldDomain
  currentDomain : TopologicalSpace.Opens (ComplexModel n)
  zero_mem_current : (0 : ComplexModel n)∈currentDomain
  inside_chart : (currentDomain : Set (ComplexModel n))⊆chart.source
  inside_old : MapsTo chart.toFun currentDomain oldDomain
  oldHolomorphicOn : ∀i,DifferentiableOn ℂ (oldFunctions i) oldDomain
  currentHolomorphicOn : ∀j,DifferentiableOn ℂ (currentFunctions j) currentDomain
  unitHolomorphicOn : DifferentiableOn ℂ unitFunction currentDomain
  unitNonzero : ∀z∈currentDomain,unitFunction z≠0
  memberSquare : ∀i,∀z∈currentDomain,
    oldFunctions i (chart.toFun z)=unitFunction z^(w i)*currentFunctions (labels i) z

/-- Entire germ covariance internally supplies actual function covariance
for EVERY finite label on ONE common true chart with a nowhere-zero unit. -/
theorem exists_actual_marked_function_square {ι κ : Type} [Fintype ι] [Fintype κ]
    (w : ι → ℕ) (old : ι → HolGerm (ComplexModel n)) (current : κ → HolGerm (ComplexModel n))
    (labels : ι≃κ) (C : HolGerm (ComplexModel n)≃ₐ[ℂ]HolGerm (ComplexModel n))
    (u : HolGerm (ComplexModel n)) (hu : IsUnit u)
    (hCov : ∀i,C (old i)=u^(w i)*current (labels i)) :
    Nonempty (ActualMarkedFunctionSquare w old current labels C u) := by
  obtain ⟨Φ,hΦ0,hΦC⟩:=exists_localHolomorphicEquivAt_of_germ_equiv C
  choose Ho hHo hGO using fun i=>HolGerm.exists_eq_mk (old i)
  choose Hn hHn hGN using fun j=>HolGerm.exists_eq_mk (current j)
  obtain ⟨v,hv,hGu⟩:=HolGerm.exists_eq_mk u
  have hv0 : v 0≠0 := by
    have h:HolGerm.eval u≠0:=(HolGerm.isUnit_iff_eval_ne_zero u).mp hu
    simpa only [hGu,HolGerm.eval_mk] using h
  have hEq (i : ι) : ∀ᶠz in 𝓝 (0 : ComplexModel n),
      Ho i (Φ.toFun z)=v z^(w i)*Hn (labels i) z := by
    have h:=hCov i
    rw [←hΦC,hGO i,localGermAlgEquiv_mk,hGu,hGN (labels i),←HolGerm.mk_pow,←HolGerm.mk_mul] at h
    exact HolGerm.mk_eq_mk_iff.mp h
  obtain ⟨V,hV,hVo,h0V⟩:=mem_nhds_iff.mp (eventually_all.mpr hHo)
  have hΦV : ∀ᶠz in 𝓝 (0 : ComplexModel n),Φ.toFun z∈V := by
    have ht:Tendsto Φ.toFun (𝓝 (0 : ComplexModel n)) (𝓝 (0 : ComplexModel n)):=by
      simpa only [hΦ0] using (local_toFun_holomorphic Φ).self_of_nhds.continuousAt.tendsto
    exact ht.eventually (hVo.mem_nhds h0V)
  have hAll : ∀ᶠz in 𝓝 (0 : ComplexModel n),z∈Φ.source ∧ Φ.toFun z∈V ∧
      (∀j,DifferentiableAt ℂ (Hn j) z) ∧ DifferentiableAt ℂ v z ∧ v z≠0 ∧
      ∀i,Ho i (Φ.toFun z)=v z^(w i)*Hn (labels i) z := by
    have hSource : ∀ᶠz in 𝓝 (0 : ComplexModel n),z∈Φ.source:=Φ.isOpen_source.mem_nhds Φ.center_mem_source
    filter_upwards [hSource,hΦV,eventually_all.mpr hHn,hv,
      hv.self_of_nhds.continuousAt.eventually_ne hv0,eventually_all.mpr hEq] with z hs ht hn hvz hne heq
    exact ⟨hs,ht,hn,hvz,hne,heq⟩
  obtain ⟨U,hU,hUo,h0U⟩:=mem_nhds_iff.mp hAll
  exact ⟨{
    chart:=Φ
    chart_zero:=hΦ0
    chart_germs:=hΦC
    oldFunctions:=Ho
    oldHolomorphicAtZero:=hHo
    oldGerms:=hGO
    currentFunctions:=Hn
    currentHolomorphicAtZero:=hHn
    currentGerms:=hGN
    unitFunction:=v
    unitHolomorphicAtZero:=hv
    unitGerm:=hGu
    oldDomain:=⟨V,hVo⟩
    zero_mem_old:=h0V
    currentDomain:=⟨U,hUo⟩
    zero_mem_current:=h0U
    inside_chart:=fun _ hz=>(hU hz).1
    inside_old:=fun _ hz=>(hU hz).2.1
    oldHolomorphicOn:=fun i z hz=>(hV hz i).differentiableWithinAt
    currentHolomorphicOn:=fun j z hz=>(hU hz).2.2.1 j |>.differentiableWithinAt
    unitHolomorphicOn:=fun z hz=>(hU hz).2.2.2.1.differentiableWithinAt
    unitNonzero:=fun z hz=>(hU hz).2.2.2.2.1
    memberSquare:=fun i z hz=>(hU hz).2.2.2.2.2 i }⟩

/-- Only original source data produce the exact current family, its literal
old labels, and the simultaneous true local function square. -/
theorem exists_actual_current_marked_function_square
    (I : Ideal (HolGerm (ComplexModel (n+1))))
    (G : ActualAnalyticInheritedFamily (n+1) 0 (analyticZeroTaylorIdeal (n+1) I))
    (hmem : ∀a,G.germs a∈I) (q e : Fin (n+1)) (hqe : q≤e) (b : Fin (n+1) → ℂ)
    (hp : ∀a,G.germs a∈actualAnalyticCoordinateIdeal (Set.Ici q)^normalExponentDegree a.val)
    (hOrder : ∀a,sameAnalyticNormalNormalizedVertex (n+1) I G q e hqe b hp a∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (n+1)))^normalExponentDegree a.val)
    (hred : ∀k,ActualInheritedPrefixReducedAt G k)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) I)))
    (hContact : ∀k,actualFixedSelectorContactAt S G.germs k) :
    ∃f : Fin (n+1),∃_hqf : q≤f,actualNormalMarkedDirection (Set.Ici q) e b f≠0 ∧
      ∃C : HolGerm (ComplexModel (n+1))≃ₐ[ℂ]HolGerm (ComplexModel (n+1)),
      ∃u : HolGerm (ComplexModel (n+1)),IsUnit u ∧
      ∃D : ActualAdaptedCurrentSelectorData I G q e f b S,
      Nonempty (ActualMarkedFunctionSquare (fun a=>normalExponentDegree a.val)
        (sameAnalyticNormalNormalizedVertex (n+1) I G q e hqe b hp) D.targetFamily.germs
        (actualAdaptedOriginalLabelEquiv D) C u) := by
  obtain ⟨f,hqf,hvf,C,u,hu,D,_hNorm,hCov⟩:=exists_actual_same_current_family_common_unit_transport
    I G hmem q e hqe b hp hOrder hred S hContact
  exact ⟨f,hqf,hvf,C,u,hu,D,exists_actual_marked_function_square
    (fun a=>normalExponentDegree a.val) _ D.targetFamily.germs (actualAdaptedOriginalLabelEquiv D) C u hu hCov⟩

section FiniteIdeals
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
 [ChartedSpace (ComplexModel n) X] [ChartedSpace (ComplexModel n) Y]
 [IsComplexManifold n X] [IsComplexManifold n Y]

private theorem pullback_finiteFunctionIdeal {ι : Type*} (c : ι → Y → ℂ)
    (hc : ∀i,MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (c i))
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f) :
    GermIdeal.pullback (m:=n) f (finiteFunctionIdeal (n:=n) c)=
      finiteFunctionIdeal (n:=n) (fun i=>c i ∘ f) := by
  refine GermIdeal.ext (funext fun x=>funext fun g=>propext ⟨?_,?_⟩)
  · intro hg
    refine IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hg)
    rintro _ ⟨a,ha,rfl⟩
    refine IsInSpanAt.mono ?_ (isInSpanAt_comp hf ha)
    rintro _ ⟨c,⟨i,rfl⟩,rfl⟩
    exact ⟨i,rfl⟩
  · intro hg
    refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.mono ?_ hg)
    rintro _ ⟨i,rfl⟩
    exact ⟨c i,isInSpanAt_self ⟨i,rfl⟩ (Eventually.of_forall fun y=>hc i y),rfl⟩

omit [IsComplexManifold n X] in
private theorem finiteFunctionIdeal_eq_of_common_nonvanishing_unit {ι : Type*}
    (c g : ι → X → ℂ) (u : X → ℂ)
    (hc : ∀i x,HolomorphicAt n (c i) x) (hg : ∀i x,HolomorphicAt n (g i) x)
    (hu : ∀x,HolomorphicAt n u x) (hun : ∀x,u x≠0)
    (hEq : ∀i x,c i x=u x*g i x) :
    finiteFunctionIdeal (n:=n) c=finiteFunctionIdeal (n:=n) g := by
  refine GermIdeal.ext (funext fun x=>funext fun h=>propext ⟨?_,?_⟩)
  · intro hh
    refine IsInSpanAt.trans ?_ hh
    rintro _ ⟨i,rfl⟩
    exact isInSpanAt_of_eq_mul ⟨i,rfl⟩ (hc i x) (hu x) (Eventually.of_forall (hEq i))
  · intro hh
    refine IsInSpanAt.trans ?_ hh
    rintro _ ⟨i,rfl⟩
    refine isInSpanAt_of_eq_mul ⟨i,rfl⟩ (hg i x) (holomorphicAt_inv (hu x) (hun x)) ?_
    exact Eventually.of_forall fun y=>by
      change g i y=(u y)⁻¹*c i y
      rw [hEq i y]
      simp only [←mul_assoc,inv_mul_cancel₀ (hun y),one_mul]
end FiniteIdeals

section SquareMap
variable {ι κ : Type} [Fintype ι] [Fintype κ]
 {w : ι → ℕ} {old : ι → HolGerm (ComplexModel n)} {current : κ → HolGerm (ComplexModel n)}
 {labels : ι≃κ} {C : HolGerm (ComplexModel n)≃ₐ[ℂ]HolGerm (ComplexModel n)} {u : HolGerm (ComplexModel n)}

/-- The actual common chart map between its two genuine representative domains. -/
def actualMarkedSquareMap (P : ActualMarkedFunctionSquare w old current labels C u) : P.currentDomain → P.oldDomain :=
  fun z=>⟨P.chart.toFun z,P.inside_old z.property⟩

private theorem actualMarkedSquareMap_contMDiff (P : ActualMarkedFunctionSquare w old current labels C u) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (actualMarkedSquareMap P) := by
  have hForward : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (fun z : P.currentDomain=>P.chart.toFun z) := by
    intro z
    have hmd : ∀ᶠy in 𝓝 (z : ComplexModel n),MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n)
        P.chart.toFun y :=
      eventually_of_mem (P.chart.isOpen_source.mem_nhds (P.inside_chart z.property)) fun y hy=>
        (P.chart.toFun_holomorphic.differentiableAt (P.chart.isOpen_source.mem_nhds hy)).mdifferentiableAt
    exact (MarkedIdealOpenBiholomorphism.contMDiffAt_of_eventually_mdifferentiableAt' hmd).comp z
      (contMDiff_subtype_val z)
  exact BlowupRestrictOpen.contMDiff_opens_mk hForward (fun z=>P.inside_old z.property)

private theorem mdifferentiable_restrict (V : TopologicalSpace.Opens (ComplexModel n))
    (f : ComplexModel n → ℂ) (hf : DifferentiableOn ℂ f V) :
    MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (fun x : V=>f x) := by
  intro x
  exact ((holomorphicAt_of_mdifferentiableOn V.isOpen
    (mdifferentiableOn_iff_differentiableOn.mpr hf) x.property).comp_contMDiff
    (Eventually.of_forall fun _=>(contMDiff_subtype_val (U:=V)).contMDiffAt)).mdifferentiableAt

private theorem actual_square_weighted_ideal
    (P : ActualMarkedFunctionSquare w old current labels C u) (wn : κ → ℕ)
    (hWeights : ∀i,w i=wn (labels i)) :
    GermIdeal.pullback (m:=n) (actualMarkedSquareMap P)
      (weightedFunctionIdeal (n:=n) w (fun i (z : P.oldDomain)=>P.oldFunctions i z))=
      weightedFunctionIdeal (n:=n) wn (fun j (z : P.currentDomain)=>P.currentFunctions j z) := by
  let f:=actualMarkedSquareMap P
  let co:=fun i (z : P.oldDomain)=>P.oldFunctions i z
  let cn:=fun j (z : P.currentDomain)=>P.currentFunctions j z
  let v:=fun z : P.currentDomain=>P.unitFunction z
  let d:=fun i=>weightedCommonMark w/w i
  have hco (i : ι) : MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (co i):=
    mdifferentiable_restrict P.oldDomain _ (P.oldHolomorphicOn i)
  have hcn (j : κ) : MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (cn j):=
    mdifferentiable_restrict P.currentDomain _ (P.currentHolomorphicOn j)
  have hv : MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) v:=
    mdifferentiable_restrict P.currentDomain _ P.unitHolomorphicOn
  have hf:=actualMarkedSquareMap_contMDiff P
  have hPowered (i : ι) (z : P.currentDomain) : (co i (f z))^(d i)=
      v z^weightedCommonMark w*(cn (labels i) z)^(d i) := by
    change (P.oldFunctions i (P.chart.toFun z))^(weightedCommonMark w/w i)=_
    rw [P.memberSquare i z z.property,mul_pow,←pow_mul,weight_mul_compressionExponent]
  have hPull:=pullback_finiteFunctionIdeal (fun i (z : P.oldDomain)=>co i z^(d i))
    (fun i=>(hco i).pow (d i)) f hf
  have hUnit:=finiteFunctionIdeal_eq_of_common_nonvanishing_unit
    (fun i (z : P.currentDomain)=>co i (f z)^(d i))
    (fun i (z : P.currentDomain)=>cn (labels i) z^(d i))
    (fun z=>v z^weightedCommonMark w)
    (fun i x=>Eventually.of_forall fun y=>(((hco i).pow (d i)).comp (hf.mdifferentiable (by simp))) y)
    (fun i x=>Eventually.of_forall fun y=>(hcn (labels i)).pow (d i) y)
    (fun x=>Eventually.of_forall fun y=>hv.pow (weightedCommonMark w) y)
    (fun z=>pow_ne_zero _ (P.unitNonzero z z.property)) hPowered
  have hMark : weightedCommonMark w=weightedCommonMark wn:=Fintype.prod_equiv labels w wn hWeights
  have hRange : range (fun i (z : P.currentDomain)=>cn (labels i) z^(d i))=
      range (fun j (z : P.currentDomain)=>cn j z^(weightedCommonMark wn/wn j)) := by
    ext g
    constructor
    · rintro ⟨i,rfl⟩
      refine ⟨labels i,?_⟩
      funext z
      simp only [d,hMark,hWeights]
    · rintro ⟨j,rfl⟩
      obtain ⟨i,rfl⟩:=labels.surjective j
      refine ⟨i,?_⟩
      funext z
      simp only [d,hMark,hWeights]
  have hReindex : finiteFunctionIdeal (n:=n) (fun i (z : P.currentDomain)=>cn (labels i) z^(d i))=
      finiteFunctionIdeal (n:=n) (fun j (z : P.currentDomain)=>cn j z^(weightedCommonMark wn/wn j)) := by
    refine GermIdeal.ext (funext fun x=>funext fun g=>?_)
    change IsInSpanAt (n:=n) (·∈range (fun i (z : P.currentDomain)=>cn (labels i) z^(d i))) x g=
      IsInSpanAt (n:=n) (·∈range (fun j (z : P.currentDomain)=>cn j z^(weightedCommonMark wn/wn j))) x g
    rw [hRange]
  exact hPull.trans (hUnit.trans hReindex)

/-- The literal OLD native weighted marked record on the true old domain. -/
def actualOldNativeWeightedRecord (P : ActualMarkedFunctionSquare w old current labels C u)
    (N : Set P.oldDomain) (E : List (Set P.oldDomain)) : MarkedIdeal n P.oldDomain :=
  ⟨N,E,weightedFunctionIdeal w (fun i (z : P.oldDomain)=>P.oldFunctions i z),weightedCommonMark w⟩

/-- True current coefficients with the actual pulled-back carrier and the
COMPLETE ordered old boundary labels; the current common mark is literal. -/
def actualCurrentNativeWeightedRecord (P : ActualMarkedFunctionSquare w old current labels C u)
    (wn : κ → ℕ) (N : Set P.oldDomain) (E : List (Set P.oldDomain)) : MarkedIdeal n P.currentDomain :=
  ⟨actualMarkedSquareMap P ⁻¹' N,E.map ((actualMarkedSquareMap P) ⁻¹' ·),
    weightedFunctionIdeal wn (fun j (z : P.currentDomain)=>P.currentFunctions j z),weightedCommonMark wn⟩

/-- The ENTIRE actual native marked record, with arbitrary carrier and all
ordered boundary labels, transports on the SAME common function chart. -/
theorem actual_square_native_weighted_record_eq
    (P : ActualMarkedFunctionSquare w old current labels C u) (wn : κ → ℕ)
    (hWeights : ∀i,w i=wn (labels i)) (N : Set P.oldDomain) (E : List (Set P.oldDomain)) :
    MarkedIdeal.pullback (actualMarkedSquareMap P) (actualOldNativeWeightedRecord P N E)=
      actualCurrentNativeWeightedRecord P wn N E := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ ?_
  · exact actual_square_weighted_ideal P wn hWeights
  · exact Fintype.prod_equiv labels w wn hWeights
end SquareMap

/-- Original source data internally produce the entire exact native
weighted-record comparison, including carrier and every ordered boundary
label. No current coefficient, unit, map, record equality or target marked
source is supplied. -/
theorem exists_actual_current_native_weighted_records
    (I : Ideal (HolGerm (ComplexModel (n+1))))
    (G : ActualAnalyticInheritedFamily (n+1) 0 (analyticZeroTaylorIdeal (n+1) I))
    (hmem : ∀a,G.germs a∈I) (q e : Fin (n+1)) (hqe : q≤e) (b : Fin (n+1) → ℂ)
    (hp : ∀a,G.germs a∈actualAnalyticCoordinateIdeal (Set.Ici q)^normalExponentDegree a.val)
    (hOrder : ∀a,sameAnalyticNormalNormalizedVertex (n+1) I G q e hqe b hp a∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (n+1)))^normalExponentDegree a.val)
    (hred : ∀k,ActualInheritedPrefixReducedAt G k)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) I)))
    (hContact : ∀k,actualFixedSelectorContactAt S G.germs k) :
    ∃f : Fin (n+1),∃_hqf : q≤f,actualNormalMarkedDirection (Set.Ici q) e b f≠0 ∧
      ∃C : HolGerm (ComplexModel (n+1))≃ₐ[ℂ]HolGerm (ComplexModel (n+1)),
      ∃u : HolGerm (ComplexModel (n+1)),IsUnit u ∧
      ∃D : ActualAdaptedCurrentSelectorData I G q e f b S,
      ∃P : ActualMarkedFunctionSquare (fun a=>normalExponentDegree a.val)
        (sameAnalyticNormalNormalizedVertex (n+1) I G q e hqe b hp) D.targetFamily.germs
        (actualAdaptedOriginalLabelEquiv D) C u,
      ∀(N : Set P.oldDomain)(E : List (Set P.oldDomain)),
        MarkedIdeal.pullback (actualMarkedSquareMap P) (actualOldNativeWeightedRecord P N E)=
          actualCurrentNativeWeightedRecord P (fun a=>normalExponentDegree a.val) N E := by
  obtain ⟨f,hqf,hvf,C,u,hu,D,⟨P⟩⟩:=exists_actual_current_marked_function_square
    I G hmem q e hqe b hp hOrder hred S hContact
  refine ⟨f,hqf,hvf,C,u,hu,D,P,?_⟩
  intro N E
  exact actual_square_native_weighted_record_eq P (fun a=>normalExponentDegree a.val)
    (fun a=>(actualAdaptedOriginalLabelEquiv_degree D a).symm) N E

end
end Hironaka.HironakaActualCurrentMarkedFunctionSquares
