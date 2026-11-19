import Hironaka.Resolution.HironakaActualWholeHSSingularity
import Hironaka.Resolution.HironakaActualGeometricCurrentNeighborhoodHS
import Hironaka.Resolution.HironakaActualCurrentMarkedFunctionSquares
import Hironaka.Resolution.HironakaRelativelyCompact

/-! A genuine native domain for the SAME historical whole-HS weighted record.
Actual singular-reference geometry forces nonzero; the whole boundary and
actual function square retain the literal marked source for a finite phase. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualHistoricalHSMarkedDomain
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaIdealOperations OkaRelationSheaf
  HironakaHolomorphicPointJets HironakaHolomorphicJetRankLoci
  HironakaHolomorphicJetChartInvariance HironakaRelativeNormalMonomialBasis
  HironakaActualRelativeNormalJetDivision HironakaActualNormalZeroAnalyticSaturation
  HironakaActualFormalInitialDiagram HironakaActualGeometricCurrentNeighborhoodHS
  HironakaActualCoherentWeightedCoefficientMarked HironakaActualWeightedCoefficientCompression
  HironakaActualCurrentMarkedFunctionSquares HironakaActualWholeHSSingularity
  HironakaRelativeNormalActualBaseJetDimension HironakaEmbeddedAnalytic
  MarkedIdeals MarkedIdeals.MarkedIdeal DivisorExponentAlong InvertibleIdealQuotient
  MarkedIdealBiholomorphism NormalCrossings SimultaneousNormalCrossings ResolutionInvariantSpec
  RelativePrincipalizationSpan GermIdealPullbackCalculus
  BlowupTowers BlowupTowerTransforms HironakaAdmissibleSequence

variable {n : ℕ} {A : GermIdeal n (ComplexModel n)}
  {I : Ideal (HolGerm (ComplexModel n))}
  {G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)} {R : ℕ → ℕ}

/-- The actual open on which the SAME whole-HS presentation was produced. -/
def presentationOpen (PHS : ActualGeometricInheritedNeighborhoodHS A I G R) :
    Opens (ComplexModel n) := ⟨PHS.neighborhood,PHS.isOpen_neighborhood⟩

private theorem translatedGerm_zero_of_eventually
    (q : ComplexModel n) (f : ComplexModel n → ℂ) (hf : HolAt f q)
    (hz : ∀ᶠ z in 𝓝 q,f z=0) : translatedGerm q f hf=0 := by
  have ht : Tendsto (fun z : ComplexModel n => z+q) (𝓝 0) (𝓝 q) := by
    simpa only [id_eq,zero_add] using (continuous_id.add_const q).tendsto (0 : ComplexModel n)
  have he : translatedGerm q f hf=HolGerm.mk (fun _ : ComplexModel n => (0 : ℂ))
      (Eventually.of_forall fun _ => differentiableAt_const 0) :=
    HolGerm.mk_eq_mk_iff.mpr (ht.eventually hz)
  simpa only [HolGerm.mk_const,map_zero] using he

private theorem presentation_stalk_zero_of_representatives_zero
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R)
    (q : ComplexModel n) (hq : q ∈ PHS.neighborhood)
    (hz : ∀ i,∀ᶠ z in 𝓝 q,PHS.representatives i z=0) :
    wholeChartStalkIdeal A q q (mem_chart_source _ q)=⊥ := by
  apply le_antisymm ?_ bot_le
  apply Ideal.span_le.mpr
  rintro _ ⟨f,hf,hAf,rfl⟩
  obtain ⟨hfh,c,_hc,he⟩ := (PHS.wholeGeneration q hq f).mp hAf
  have hfzero : ∀ᶠ z in 𝓝 q,f z=0 := by
    filter_upwards [he,eventually_all.mpr hz] with z hez hzz
    rw [hez]
    exact Finset.sum_eq_zero fun i _ => by rw [hzz i,mul_zero]
  have hg : chartTranslatedGerm q q (mem_chart_source _ q) f hf=
      translatedGerm q f hfh := by
    unfold chartTranslatedGerm translatedGerm
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => by simp [chartAt_self_eq]
  rw [hg,translatedGerm_zero_of_eventually q f hfh hfzero]
  exact Ideal.zero_mem _

private theorem presentation_hs_ambient_of_representatives_zero
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R)
    (q : ComplexModel n) (hq : q ∈ PHS.neighborhood)
    (hz : ∀ i,∀ᶠ z in 𝓝 q,PHS.representatives i z=0) :
    ∀ ℓ,R ℓ=(n+ℓ).choose n := by
  have hmarks : ∀ i,translatedGerm q (PHS.representatives i) (PHS.holomorphicAt q hq i)∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^normalExponentDegree i.val := by
    intro i
    rw [translatedGerm_zero_of_eventually q _ _ (hz i)]
    exact Ideal.zero_mem _
  have hHS := (PHS.wholeHS q hq).mp hmarks
  intro ℓ
  rw [←hHS ℓ,hilbertSamuelAt,presentation_stalk_zero_of_representatives_zero PHS q hq hz,
    hilbertSamuelValue,bot_sup_eq]
  exact actualBaseJetDimension n ℓ

/-- A genuine whole-HS presentation with an ORIGINAL intrinsically singular
reference internally gives nonzero of its SAME literal weighted ideal,
together with positivity of its unchanged common mark. -/
theorem presentation_weighted_nonzero
    {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] {W : Set M}
    (hW : IsComplexAnalyticSubset (n := n) W) {a : M}
    (ha : a ∈ singularSet (n := n) W)
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G
      (fun ℓ => hilbertSamuelAt (vanishingIdeal (n := n) W) a ℓ))
    (hw : ∀ i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I),
      0 < normalExponentDegree i.val) :
    0 < weightedCommonMark (fun i : actualInitialVertices MonomialOrder.degLex
      (analyticZeroTaylorIdeal n I) => normalExponentDegree i.val) ∧
    ∀ x : presentationOpen PHS, IsNonzeroAlongAt (n := n) univ
      (weightedFunctionIdeal (n := n) (fun i => normalExponentDegree i.val)
        (fun i (z : presentationOpen PHS) => PHS.representatives i z.val)) x := by
  let μ := fun i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I) =>
    normalExponentDegree i.val
  let U := presentationOpen PHS
  let f := fun i (z : U) => PHS.representatives i z.val
  have hf (i) : MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (f i) := by
    intro z
    have hh := holomorphicAt_of_mdifferentiableOn PHS.isOpen_neighborhood
      (mdifferentiableOn_iff_differentiableOn.mpr (PHS.holomorphicOn i)) z.property
    exact (hh.comp_contMDiff
      (Eventually.of_forall fun _ => (contMDiff_subtype_val (U := U)).contMDiffAt)).mdifferentiableAt
  refine ⟨weightedCommonMark_pos μ hw,?_⟩
  intro x
  by_contra hnz
  have hpow (i) : ∀ᶠ z in 𝓝 x, f i z^(weightedCommonMark μ/μ i)=0 := by
    have hmem : (weightedFunctionIdeal μ f).mem x
        (fun z => f i z^(weightedCommonMark μ/μ i)) :=
      isInSpanAt_self ⟨i,rfl⟩ (holomorphicAt_of_mdifferentiableOn isOpen_univ
        ((hf i).pow _).mdifferentiableOn (mem_univ x))
    have hn : ¬ ∃ᶠ z in 𝓝 x,z ∈ univ ∧ f i z^(weightedCommonMark μ/μ i) ≠ 0 :=
      fun hh => hnz ⟨_,hmem,hh⟩
    rw [not_frequently] at hn
    simpa only [mem_univ,true_and,not_not] using hn
  have hz (i) : ∀ᶠ z in 𝓝 x.val,PHS.representatives i z=0 := by
    apply (eventually_nhds_val_iff U).mpr
    exact (hpow i).mono fun z h => by
      by_contra hne
      exact (pow_ne_zero _ hne) h
  have hbin := presentation_hs_ambient_of_representatives_zero PHS x.val x.property hz
  have hreg := (regularAtDim_iff_intrinsic_hs_binomial hW a n).mpr hbin
  exact (mem_singularSet_iff.mp ha).2 n hreg

section Square
variable {ι κ : Type} [Fintype ι] [Fintype κ]
  {w : ι → ℕ} {old : ι → HolGerm (ComplexModel n)}
  {current : κ → HolGerm (ComplexModel n)} {labels : ι ≃ κ}
  {Cg : HolGerm (ComplexModel n) ≃ₐ[ℂ] HolGerm (ComplexModel n)}
  {unit : HolGerm (ComplexModel n)}

private theorem holomorphic_comp_contMDiff
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y] (g : Y → ComplexModel n)
    (hg : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ g)
    {O : Set (ComplexModel n)} (hO : IsOpen O) (f : ComplexModel n → ComplexModel n)
    (hf : DifferentiableOn ℂ f O) (hmap : ∀ y,g y ∈ O) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (f ∘ g) := by
  intro y
  have hm : ∀ᶠ z in 𝓝 (g y),MDifferentiableAt 𝓘(ℂ,ComplexModel n)
      𝓘(ℂ,ComplexModel n) f z := by
    filter_upwards [hO.mem_nhds (hmap y)] with z hz
    exact (hf.differentiableAt (hO.mem_nhds hz)).mdifferentiableAt
  exact (MarkedIdealOpenBiholomorphism.contMDiffAt_of_eventually_mdifferentiableAt' hm).comp y (hg y)

private def oldWindow (P : ActualMarkedFunctionSquare w old current labels Cg unit)
    (U : Opens (ComplexModel n)) : Opens P.oldDomain :=
  ⟨{z | z.val ∈ P.chart.target ∧ P.chart.invFun z.val ∈ U},
    (P.chart.invFun_holomorphic.continuousOn.isOpen_inter_preimage P.chart.isOpen_target
      U.isOpen).preimage continuous_subtype_val⟩

private def windowDiffeomorph (P : ActualMarkedFunctionSquare w old current labels Cg unit)
    (U : Opens (ComplexModel n)) (hU : (U : Set (ComplexModel n)) ⊆ P.currentDomain) :
    U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ oldWindow P U where
  toFun z := ⟨⟨P.chart.toFun z.val,P.inside_old (hU z.property)⟩,
    P.chart.mapsTo_toFun (P.inside_chart (hU z.property)),by
      rw [P.chart.left_inv _ (P.inside_chart (hU z.property))]
      exact z.property⟩
  invFun z := ⟨P.chart.invFun z.val.val,z.property.2⟩
  left_inv z := Subtype.ext (P.chart.left_inv _ (P.inside_chart (hU z.property)))
  right_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    exact P.chart.right_inv _ z.property.1
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (oldWindow P U) _).mp
    apply (ContMDiff.subtypeVal_comp_iff P.oldDomain _).mp
    exact holomorphic_comp_contMDiff (Subtype.val : U → ComplexModel n) contMDiff_subtype_val
      P.chart.isOpen_source P.chart.toFun P.chart.toFun_holomorphic
      (fun z => P.inside_chart (hU z.property))
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff U _).mp
    exact holomorphic_comp_contMDiff (fun z : oldWindow P U => z.val.val)
      (contMDiff_subtype_val.comp contMDiff_subtype_val) P.chart.isOpen_target
      P.chart.invFun P.chart.invFun_holomorphic (fun z => z.property.1)

private theorem whole_boundary_snc (P : ActualMarkedFunctionSquare w old current labels Cg unit)
    (U : Opens (ComplexModel n)) (hU : (U : Set (ComplexModel n)) ⊆ P.currentDomain)
    (E : List (Set P.oldDomain)) (hE : NormalCrossings.IsSNCDivisor n E) :
    NormalCrossings.IsSNCDivisor n
      (E.map ((fun z : U => (⟨P.chart.toFun z.val,P.inside_old (hU z.property)⟩ : P.oldDomain)) ⁻¹' ·)) := by
  let Φ := windowDiffeomorph P U hU
  have hOld : NormalCrossings.IsSNCDivisor n
      (E.map ((Subtype.val : oldWindow P U → P.oldDomain) ⁻¹' ·)) :=
    NormalCrossingsInvariance.isSNCDivisor_map_preimage
      (NormalCrossingsInvariance.pullsBackCoordinates_val (oldWindow P U)) continuous_subtype_val hE
  have hNew := NormalCrossingsInvariance.isSNCDivisor_map_preimage
    (NormalCrossingsInvariance.pullsBackCoordinates_of_forall_notMem_exceptionalLocus
      Φ.contMDiff (MarkedIdealTowerTransport.notMem_exceptionalLocus Φ))
    Φ.contMDiff.continuous hOld
  have hNative : (fun z : U => ((Φ z : oldWindow P U) : P.oldDomain))=
      (fun z : U => (⟨P.chart.toFun z.val,P.inside_old (hU z.property)⟩ : P.oldDomain)) := by
    funext z
    apply Subtype.ext
    rfl
  simp only [List.map_map,Function.comp_def,Set.preimage_preimage] at hNew
  rw [hNative] at hNew
  exact hNew

private theorem function_restrict_mdifferentiable (U : Opens (ComplexModel n))
    (f : ComplexModel n → ℂ) (hf : DifferentiableOn ℂ f U) :
    MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (fun z : U => f z.val) := by
  intro z
  have hh := holomorphicAt_of_mdifferentiableOn U.isOpen
    (mdifferentiableOn_iff_differentiableOn.mpr hf) z.property
  exact (hh.comp_contMDiff
    (Eventually.of_forall fun _ => (contMDiff_subtype_val (U := U)).contMDiffAt)).mdifferentiableAt

private theorem pullback_finite_family
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) X] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n X] [IsComplexManifold n Y]
    {τ : Type*} (c : τ → Y → ℂ)
    (hc : ∀ i,MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (c i))
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f) :
    GermIdeal.pullback (m := n) f (finiteFunctionIdeal (n := n) c)=
      finiteFunctionIdeal (n := n) (fun i => c i ∘ f) := by
  refine GermIdeal.ext (funext fun x => funext fun g => propext ⟨?_,?_⟩)
  · intro hg
    refine IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hg)
    rintro _ ⟨a,ha,rfl⟩
    refine IsInSpanAt.mono ?_ (isInSpanAt_comp hf ha)
    rintro _ ⟨c,⟨i,rfl⟩,rfl⟩
    exact ⟨i,rfl⟩
  · intro hg
    refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.mono ?_ hg)
    rintro _ ⟨i,rfl⟩
    exact ⟨c i,isInSpanAt_self ⟨i,rfl⟩ (Eventually.of_forall fun y => hc i y),rfl⟩

/-- The genuine inclusion of an actual model window in the SAME current domain. -/
def currentWindowMap (P : ActualMarkedFunctionSquare w old current labels Cg unit)
    (U : Opens (ComplexModel n)) (hU : (U : Set (ComplexModel n)) ⊆ P.currentDomain) :
    U → P.currentDomain := fun z => ⟨z.val,hU z.property⟩

/-- The literal restriction of the SAME existing current native record. -/
def actualCurrentRecordOn (P : ActualMarkedFunctionSquare w old current labels Cg unit)
    (wn : κ → ℕ) (U : Opens (ComplexModel n))
    (hU : (U : Set (ComplexModel n)) ⊆ P.currentDomain) (E : List (Set P.oldDomain)) :
    MarkedIdeal n U :=
  MarkedIdeal.pullback (currentWindowMap P U hU) (actualCurrentNativeWeightedRecord P wn univ E)

private theorem currentRecordOn_formula
    (P : ActualMarkedFunctionSquare w old current labels Cg unit)
    (wn : κ → ℕ) (U : Opens (ComplexModel n))
    (hU : (U : Set (ComplexModel n)) ⊆ P.currentDomain) (E : List (Set P.oldDomain)) :
    actualCurrentRecordOn P wn U hU E=
      ⟨univ,E.map ((fun z : U =>
          (⟨P.chart.toFun z.val,P.inside_old (hU z.property)⟩ : P.oldDomain)) ⁻¹' ·),
        weightedFunctionIdeal wn (fun i (z : U) => P.currentFunctions i z.val),weightedCommonMark wn⟩ := by
  have hmap : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (currentWindowMap P U hU) := by
    apply (ContMDiff.subtypeVal_comp_iff P.currentDomain _).mp
    exact contMDiff_subtype_val
  have hc (i) := function_restrict_mdifferentiable P.currentDomain
    (P.currentFunctions i) (P.currentHolomorphicOn i)
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ ?_ ?_ rfl
  · simp only [actualCurrentRecordOn,MarkedIdeal.pullback,actualCurrentNativeWeightedRecord,preimage_univ]
  · change (E.map ((actualMarkedSquareMap P) ⁻¹' ·)).map ((currentWindowMap P U hU) ⁻¹' ·)=_
    rw [List.map_map]
    rfl
  · change GermIdeal.pullback (currentWindowMap P U hU)
      (finiteFunctionIdeal (fun i (z : P.currentDomain) => P.currentFunctions i z.val^(weightedCommonMark wn/wn i)))=_
    exact pullback_finite_family _ (fun i => (hc i).pow _) _ hmap

end Square

/-- The SAME current native record, restricted through its actual chart square,
has every native invariant-domain field. Full old-boundary SNC is genuine
source geometry; current SNC and nonzero are derived here. -/
theorem actual_current_record_isInvDomain
    {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] {W : Set M}
    (hW : IsComplexAnalyticSubset (n := n) W) {a : M}
    (ha : a ∈ singularSet (n := n) W)
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G
      (fun ℓ => hilbertSamuelAt (vanishingIdeal (n := n) W) a ℓ))
    (hw : ∀ i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I),
      0 < normalExponentDegree i.val)
    {ι : Type} [Fintype ι] {w : ι → ℕ} {old : ι → HolGerm (ComplexModel n)}
    {labels : ι ≃ actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)}
    {Cg : HolGerm (ComplexModel n) ≃ₐ[ℂ] HolGerm (ComplexModel n)}
    {unit : HolGerm (ComplexModel n)}
    (P : ActualMarkedFunctionSquare w old G.germs labels Cg unit)
    (hSame : PHS.representatives=P.currentFunctions)
    (hU : (presentationOpen PHS : Set (ComplexModel n)) ⊆ P.currentDomain)
    (E : List (Set P.oldDomain)) (hE : IsSNCDivisor n E) :
    IsInvDomain n (actualCurrentRecordOn P (fun i => normalExponentDegree i.val)
      (presentationOpen PHS) hU E) := by
  rw [currentRecordOn_formula]
  have hBoundary := whole_boundary_snc P (presentationOpen PHS) hU E hE
  have hFunctions (i) : MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ)
      (fun z : presentationOpen PHS => P.currentFunctions i z.val) :=
    function_restrict_mdifferentiable _ _ ((P.currentHolomorphicOn i).mono hU)
  have hNonzero := presentation_weighted_nonzero hW ha PHS hw
  refine ⟨⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,
    isCoherent_weightedFunctionIdeal _ _ hFunctions,hBoundary,
    isTransverse_univ_of_isSNCDivisor hBoundary⟩,?_,hNonzero.1,?_⟩
  · intro z _
    exact ⟨n,le_rfl,EmbeddedFromResolution.regularAtDim_of_mem_nhds (by simp)⟩
  · intro z _
    convert hNonzero.2 z using 1
    dsimp only
    rw [hSame]
    rfl

/-- An actual finite canonical marked phase is chosen internally on each
relatively compact window of this SAME record. The all-points future HS
comparison is a separate historical successor theorem. -/
theorem exists_actual_current_canonical_resolution
    {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] {W : Set M}
    (hW : IsComplexAnalyticSubset (n := n) W) {a : M}
    (ha : a ∈ singularSet (n := n) W)
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G
      (fun ℓ => hilbertSamuelAt (vanishingIdeal (n := n) W) a ℓ))
    (hw : ∀ i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I),
      0 < normalExponentDegree i.val)
    {ι : Type} [Fintype ι] {w : ι → ℕ} {old : ι → HolGerm (ComplexModel n)}
    {labels : ι ≃ actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)}
    {Cg : HolGerm (ComplexModel n) ≃ₐ[ℂ] HolGerm (ComplexModel n)}
    {unit : HolGerm (ComplexModel n)}
    (P : ActualMarkedFunctionSquare w old G.germs labels Cg unit)
    (hSame : PHS.representatives=P.currentFunctions)
    (hU : (presentationOpen PHS : Set (ComplexModel n)) ⊆ P.currentDomain)
    (E : List (Set P.oldDomain)) (hE : IsSNCDivisor n E)
    {K : Set (presentationOpen PHS)} (hK : IsCompact K)
    (O : Opens (presentationOpen PHS)) (hO : (O : Set (presentationOpen PHS)) ⊆ K) :
    let Q := actualCurrentRecordOn P (fun i => normalExponentDegree i.val)
      (presentationOpen PHS) hU E
    ∃ (Y : CMfd n) (T : BlowupTower (CMfd.of (n := n) O) Y),
      IsCanonical (MarkedIdeal.pullback (Subtype.val : O → presentationOpen PHS) Q)
        ((CanonicalCentres.canonicalInvariant n).inv
          (MarkedIdeal.pullback (Subtype.val : O → presentationOpen PHS) Q)) T ∧
      IsGeoResolution (MarkedIdeal.pullback (Subtype.val : O → presentationOpen PHS) Q) T := by
  exact HironakaRelativelyCompact.exists_isCanonical_resolution_of_subset_isCompact
    (CanonicalCentres.canonicalInvariant n)
    (X := CMfd.of (n := n) (presentationOpen PHS))
    (actual_current_record_isInvDomain hW ha PHS hw P hSame hU E hE) hK O hO

end
end Hironaka.HironakaActualHistoricalHSMarkedDomain
