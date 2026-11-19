import Hironaka.Resolution.HironakaActualWholeHSContactWindow
import Hironaka.Resolution.HironakaActualInheritedFreeProductCentre
import Hironaka.Resolution.HironakaEmbeddedExceptional

/-! Rebase the prescribed NEXT actual blowup on genuine coordinates of the
SAME current geometric stage.  Whole records and whole vanishing sheaves,
all ordered boundary members, and the exact restricted next map are kept.
No historical comparison, normal-power, or whole-HS certificate is assumed.
-/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualPrescribedCentreRebasing
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
 HolGerm HironakaHolomorphicJetChartInvariance
 HironakaActualWholeHSContactWindow HironakaActualCurrentMarkedFunctionSquares
 HironakaActualGeometricCurrentNeighborhoodHS HironakaActualCoherentWeightedCoefficientMarked
 HironakaActualWeightedCoefficientCompression HironakaActualCoefficientPresentationCentrePower
 HironakaRelativeNormalMonomialBasis HironakaActualFormalInitialDiagram
 HironakaActualRelativeNormalJetDivision HironakaActualInheritedNestedContactFlag
 HironakaActualFixedInheritedSelector HironakaActualInheritedFreeProductPresentation
 HironakaActualFlatCoordinateIntrinsicHS HironakaActualFixedFlatteningHSComparison
 HironakaEmbeddedExceptional RegularAtDimTransport BlowupFlatCoordinates
 HironakaActualRawRecordPullbacks MarkedIdealBiholomorphism MarkedIdealRestrictOpen
 MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealPullbackCalculus
 RelativePrincipalizationSpan InvertibleIdealQuotient
 HironakaHolomorphicPointJets HironakaHolomorphicJetRankLoci
 HironakaActualInheritedNeighborhoodMarkedHS GermIdealOrder IdealWeightPowers
 OkaRelationSheaf HironakaSmoothCentreCoherentDomain
 HironakaRelativeNormalDeformationInitialRelations HadamardBridge OrderTaylor BlowupTowers
 HironakaActualInheritedEssentialPriority HironakaActualInheritedSourcePermutationFamily
 HironakaActualInheritedSourceOwnerPermutation HironakaActualInheritedCurrentSourceRelabel
 HironakaActualFixedInheritedSelectorPermutation HironakaActualNormalZeroAnalyticSaturation
 OkaIdealOperations HironakaActualLocalHolomorphicOriginPullback AnalyticSubsetOpens

variable {n : ℕ}

private theorem local_pullback_comp_at
    {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X]
    (A : GermIdeal n X) (hA : ∀x f,A.mem x f → HolomorphicAt n f x)
    (f : ComplexModel n → X) (g : ComplexModel n → ComplexModel n) (p : ComplexModel n)
    (hf : ∀ᶠz in 𝓝 (g p),MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) f z)
    (hg : ∀ᶠz in 𝓝 p,MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) g z)
    (v : ComplexModel n → ℂ) :
    (GermIdeal.pullback (m:=n) g (GermIdeal.pullback (m:=n) f A)).mem p v ↔
      (GermIdeal.pullback (m:=n) (f ∘ g) A).mem p v := by
  constructor
  · intro hv
    refine GermIdeal.mem_pullback_iff.mpr
      (IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hv))
    rintro _ ⟨s,hs,rfl⟩
    refine IsInSpanAt.mono ?_
      (CoefficientRestrictionTower.isInSpanAt_comp_map hg (GermIdeal.mem_pullback_iff.mp hs))
    rintro _ ⟨b,⟨a,ha,rfl⟩,rfl⟩
    exact ⟨a,ha,rfl⟩
  · intro hv
    refine GermIdeal.mem_pullback_iff.mpr
      (IsInSpanAt.mono ?_ (GermIdeal.mem_pullback_iff.mp hv))
    rintro _ ⟨a,ha,rfl⟩
    exact ⟨a ∘ f,GermIdeal.mem_pullback_iff.mpr
      (isInSpanAt_self ⟨a,ha,rfl⟩ (holomorphicAt_comp_map hf (hA _ _ ha))),rfl⟩

private theorem originIdeal_eq_of_mem_at_zero
    (A B : GermIdeal n (ComplexModel n)) (h : ∀f,A.mem 0 f ↔ B.mem 0 f) :
    originalCoherentOriginIdeal A=originalCoherentOriginIdeal B := by
  unfold originalCoherentOriginIdeal
  apply congrArg Ideal.span
  ext g
  constructor
  · rintro ⟨f,hf,hAf,rfl⟩
    exact ⟨f,hf,(h f).mp hAf,rfl⟩
  · rintro ⟨f,hf,hBf,rfl⟩
    exact ⟨f,hf,(h f).mpr hBf,rfl⟩

private theorem inverse_on_open_contMDiff
    {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
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

private theorem marked_cosupp_pullback_forward
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) X] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n X] [IsComplexManifold n Y]
    (Q : MarkedIdeal n X) (f : Y → X)
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f)
    (z : Y) (hz : f z∈Q.cosupp) : z∈(MarkedIdeal.pullback f Q).cosupp := by
  refine ⟨hz.1,fun g hg=>?_⟩
  refine IdealOrderArithmetic.IsInSpanAt.vanishesToOrderOn
    (GermIdeal.mem_pullback_iff.mp hg) ?_
  rintro _ ⟨a,ha,rfl⟩
  exact MonomialPartEtale.vanishesToOrderOn_comp
    (Eventually.of_forall fun w=>(hf w).mdifferentiableAt (by simp)) (hz.2 a ha)

private theorem translated_order_of_native_order
    (O : Opens (ComplexModel n)) (p : O) (f : ComplexModel n → ℂ)
    (hf : HolAt f p.val) (q : ℕ)
    (hv : VanishesToOrderOn n univ p q (fun z : O=>f z)) :
    translatedGerm p.val f hf∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^q := by
  apply (translatedGerm_mem_maximalIdeal_pow_iff_pointIdeal p.val f hf q).mpr
  have hPow:=mem_idealPow_of_vanishesToOrderOn_univ hv
  have hExt:=mem_idealPow_pointIdeal_extendOpens O q hPow
  apply mem_idealPow_congr hExt
  filter_upwards [O.isOpen.mem_nhds p.property] with z hz
  change extendOpens O (fun a : O=>f a) (⟨z,hz⟩ : O).val=f z
  rw [extendOpens_val]

/-- The actual geometric chart into the SAME historical current coordinates.
Its literal inverse is the original actual inverse chart after P.chart. -/
def currentCoordinateFlattening {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] (x : X)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hΘ0 : Θ.toFun (chartAt (ComplexModel n) x x)=0)
    (Λ : LocalHolomorphicEquivAt (n:=n) (0 : ComplexModel n)) (hΛ0 : Λ.toFun 0=0) :
    LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x) :=
  LocalHolomorphicEquivAt.comp Θ
    (HironakaEmbeddedExceptional.LocalHolomorphicEquivAt.symmAt Λ hΛ0) hΘ0

/-- Restrict the target to the requested genuine open; functions and inverse
functions remain literal and the source is their exact preimage. -/
def coordinateTargetRestriction {p : ComplexModel n}
    (Θ : LocalHolomorphicEquivAt (n:=n) p) (hΘ0 : Θ.toFun p=0)
    (O : Opens (ComplexModel n)) (h0O : (0 : ComplexModel n)∈O)
    (hO : (O : Set (ComplexModel n))⊆Θ.target) : LocalHolomorphicEquivAt (n:=n) p where
  source:=Θ.source∩Θ.toFun ⁻¹' O
  target:=O
  isOpen_source:=Θ.toFun_holomorphic.continuousOn.isOpen_inter_preimage Θ.isOpen_source O.isOpen
  isOpen_target:=O.isOpen
  center_mem_source:=⟨Θ.center_mem_source,by
    change Θ.toFun p∈(O : Set (ComplexModel n))
    rw [hΘ0]
    exact h0O⟩
  toFun:=Θ.toFun
  invFun:=Θ.invFun
  toFun_holomorphic:=Θ.toFun_holomorphic.mono inter_subset_left
  invFun_holomorphic:=Θ.invFun_holomorphic.mono hO
  mapsTo_toFun:=fun _ hz=>hz.2
  mapsTo_invFun:=fun z hz=>⟨Θ.mapsTo_invFun (hO hz),by
    change Θ.toFun (Θ.invFun z)∈O
    rwa [Θ.right_inv z (hO hz)]⟩
  left_inv:=fun z hz=>Θ.left_inv z hz.1
  right_inv:=fun z hz=>Θ.right_inv z (hO hz)

/-- The prescribed actual centre's whole HS constancy follows from the
ENTIRE actual marked-record square.  The equality at zero is also derived
from the same centre, rather than supplied as a reference certificate. -/
theorem actual_prescribed_centre_whole_hs
    {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X]
    {ι : Type} [Fintype ι] {I : Ideal (HolGerm (ComplexModel n))}
    {G : ActualAnalyticInheritedFamily n 0 (HironakaActualNormalZeroAnalyticSaturation.analyticZeroTaylorIdeal n I)}
    {w : ι → ℕ} {old : ι → HolGerm (ComplexModel n)}
    {labels : ι≃actualInitialVertices MonomialOrder.degLex
      (HironakaActualNormalZeroAnalyticSaturation.analyticZeroTaylorIdeal n I)}
    {Cg : HolGerm (ComplexModel n)≃ₐ[ℂ]HolGerm (ComplexModel n)}
    {u : HolGerm (ComplexModel n)}
    (Q : MarkedIdeal n X) (hQN : Q.N=univ) (x : X)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Θ.source⊆(chartAt (ComplexModel n) x).target)
    (hΘ0 : Θ.toFun (chartAt (ComplexModel n) x x)=0)
    (P : ActualMarkedFunctionSquare w old G.germs labels Cg u)
    (hOldTarget : (P.oldDomain : Set (ComplexModel n))⊆Θ.target)
    (hRecord : MarkedIdeal.pullback
      (fun z : P.currentDomain=>actualFlatteningInverseMap x Θ (P.chart.toFun z)) Q=
      actualCurrentNativeWeightedRecord P (fun a=>normalExponentDegree a.val)
        ((fun z : P.oldDomain=>actualFlatteningInverseMap x Θ z) ⁻¹' Q.N)
        (Q.E.map ((fun z : P.oldDomain=>actualFlatteningInverseMap x Θ z) ⁻¹' ·)))
    (A : GermIdeal n (ComplexModel n)) (R : ℕ → ℕ)
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R)
    (hFunctions : PHS.representatives=P.currentFunctions)
    (hDomain : PHS.neighborhood⊆P.currentDomain)
    (hw : ∀a : actualInitialVertices MonomialOrder.degLex
      (HironakaActualNormalZeroAnalyticSaturation.analyticZeroTaylorIdeal n I),
      0<normalExponentDegree a.val)
    (C : Set X) (hC : C⊆Q.cosupp) (hxC : x∈C) :
    ∀z∈PHS.neighborhood,actualFlatteningInverseMap x Θ (P.chart.toFun z)∈C →
      ∀ℓ,hilbertSamuelAt A z ℓ=hilbertSamuelAt A 0 ℓ := by
  let Ξ:=currentCoordinateFlattening x Θ hΘ0 P.chart P.chart_zero
  have hΞsrc : Ξ.source⊆(chartAt (ComplexModel n) x).target:=fun _ hz=>hsrc hz.1
  have hCurrent : (P.currentDomain : Set (ComplexModel n))⊆Ξ.target:=
    fun z hz=>⟨P.inside_chart hz,hOldTarget (P.inside_old hz)⟩
  have hH:=inverse_on_open_contMDiff x Ξ hΞsrc P.currentDomain hCurrent
  change ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
    (fun z : P.currentDomain=>actualFlatteningInverseMap x Θ (P.chart.toFun z)) at hH
  have hc (a) : MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ)
      (fun z : P.currentDomain=>P.currentFunctions a z) := by
    intro z
    exact ((holomorphicAt_of_mdifferentiableOn P.currentDomain.isOpen
      (mdifferentiableOn_iff_differentiableOn.mpr (P.currentHolomorphicOn a)) z.property).comp_contMDiff
      (Eventually.of_forall fun _=>(contMDiff_subtype_val (U:=P.currentDomain)).contMDiffAt)).mdifferentiableAt
  have hAt (z : ComplexModel n) (hz : z∈PHS.neighborhood)
      (hzC : actualFlatteningInverseMap x Θ (P.chart.toFun z)∈C) :
      ∀ℓ,hilbertSamuelAt A z ℓ=R ℓ := by
    let p : P.currentDomain:=⟨z,hDomain hz⟩
    have hp:=marked_cosupp_pullback_forward Q _ hH p (hC hzC)
    rw [hRecord] at hp
    simp only [MarkedIdeal.cosupp,actualCurrentNativeWeightedRecord,hQN,preimage_univ] at hp
    have hpAll : p∈⋂a,cosupport n univ
        (finiteFunctionIdeal (fun _ : Unit=>(fun z : P.currentDomain=>P.currentFunctions a z)))
        (normalExponentDegree a.val) :=
      (congrArg (fun s : Set P.currentDomain=>p∈s)
        (cosupport_weightedFunctionIdeal _ hw _ hc)).mp hp
    apply (PHS.wholeHS z hz).mp
    intro a
    have hi:=mem_iInter.mp hpAll a
    have hv:=(mem_cosupport_finiteFunctionIdeal_iff
      (fun _ : Unit=>(fun z : P.currentDomain=>P.currentFunctions a z)) p
      (normalExponentDegree a.val) (fun _=>Eventually.of_forall fun z=>hc a z)).mp hi ()
    have hf : HolAt (P.currentFunctions a) z := by
      rw [←hFunctions]
      exact PHS.holomorphicAt z hz a
    have hPower:=translated_order_of_native_order P.currentDomain p (P.currentFunctions a) hf
      (normalExponentDegree a.val) hv
    simpa only [hFunctions] using hPower
  have h0C : actualFlatteningInverseMap x Θ (P.chart.toFun 0)∈C := by
    rw [P.chart_zero,actualFlatteningInverseMap_zero x Θ hΘ0]
    exact hxC
  have hReference:=hAt 0 PHS.zero_mem h0C
  intro z hz hzC ℓ
  exact (hAt z hz hzC ℓ).trans (hReference ℓ).symm

private theorem presentation_locally_fg
    {A : GermIdeal n (ComplexModel n)} {I : Ideal (HolGerm (ComplexModel n))}
    {G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)} {R : ℕ → ℕ}
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R) : IdealFGAt A.mem (0 : ComplexModel n) :=
  ⟨PHS.neighborhood,PHS.isOpen_neighborhood,PHS.zero_mem,
    actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I),inferInstance,
    PHS.representatives,PHS.holomorphicOn,PHS.wholeGeneration⟩

private theorem source_formal_members (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I))
    (hspan : Ideal.span (Set.range G.germs)=I) :
    ∀a,actualUnshiftedTaylorAlgHom n (G.germs a)∈analyticZeroTaylorIdeal n I := by
  intro a
  apply Ideal.mem_map_of_mem (actualUnshiftedTaylorAlgHom n).toRingHom
  exact hspan.le (Ideal.subset_span ⟨a,rfl⟩)

private def source_priority (I : Ideal (HolGerm (ComplexModel n))) : Fin n≃Fin n :=
  essentialFreeFirstEquiv (fixedSelectorEssential
    (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)))

private def priority_ideal (I : Ideal (HolGerm (ComplexModel n))) :=
  Ideal.map (MvPowerSeries.rename (source_priority I)).toRingHom (analyticZeroTaylorIdeal n I)

def prescribedFlatOriginIdeal (I : Ideal (HolGerm (ComplexModel n)))
    (Φ : LocalHolomorphicEquivAt (n:=n) (0 : ComplexModel n)) (hΦ0 : Φ.toFun 0=0) :=
  Ideal.map (localGermAlgEquiv Φ hΦ0).symm.toRingEquiv.toRingHom I

/-- Output data for the SAME historical family and selector.  Its producer
derives compatible flattening from actual geometry and actual HS constancy;
none of these fields is a premise of that producer. -/
structure ActualPrescribedHistoricalFlattening
    (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I))
    (hspan : Ideal.span (Set.range G.germs)=I)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)))
    (C : Set (ComplexModel n)) (k : ℕ) where
  chart : LocalHolomorphicEquivAt (n:=n) (0 : ComplexModel n)
  chart_zero : chart.toFun 0=0
  centre : ∀z∈chart.source,z∈C ↔ chart.toFun z∈complexCoordinatePlane n k
  diagram : actualInitialDiagram MonomialOrder.degLex
      (actualInheritedCurrentSourceIdeal (prescribedFlatOriginIdeal I chart chart_zero))=
    actualInitialDiagram MonomialOrder.degLex (priority_ideal I)
  vertices : actualInitialVertices MonomialOrder.degLex (priority_ideal I)=
    actualInitialVertices MonomialOrder.degLex
      (actualInheritedCurrentSourceIdeal (prescribedFlatOriginIdeal I chart chart_zero))
  family : ActualAnalyticInheritedFamily n 0
    (actualInheritedCurrentSourceIdeal (prescribedFlatOriginIdeal I chart chart_zero))
  members : ∀a,family.germs (sourceVertexSetCast vertices
      (actualSourcePermutationVertexEquiv G (source_formal_members I G hspan)
        (source_priority I) (essentialPriority_family_lower G) a))=
    (localGermAlgEquiv chart chart_zero).symm (G.germs a)
  span : Ideal.span (range family.germs)=prescribedFlatOriginIdeal I chart chart_zero
  prefixes : ∀k,ActualInheritedPrefixReducedAt family k
  contacts : ∀k,actualFixedSelectorContactAt (sourceFixedSelectorCast vertices
    (actualSourcePermutedFixedSelector G (source_formal_members I G hspan)
      (source_priority I) (essentialPriority_family_lower G) S)) family.germs k

namespace ActualPrescribedHistoricalFlattening
variable {I : Ideal (HolGerm (ComplexModel n))}
 {G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)}
 {hspan : Ideal.span (range G.germs)=I}
 {S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I))}
 {C : Set (ComplexModel n)} {k : ℕ}

/-- The literal original label permutation followed by the proved vertex cast. -/
def historicalLabels (T : ActualPrescribedHistoricalFlattening I G hspan S C k) :=
  (actualSourcePermutationVertexEquiv G (source_formal_members I G hspan)
    (source_priority I) (essentialPriority_family_lower G)).trans (sourceVertexSetCast T.vertices)

theorem historicalLabels_degree (T : ActualPrescribedHistoricalFlattening I G hspan S C k)
    (a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)) :
    normalExponentDegree (T.historicalLabels a).val=normalExponentDegree a.val := by
  change normalExponentDegree (actualSourcePermutationVertexEquiv G (source_formal_members I G hspan)
    (source_priority I) (essentialPriority_family_lower G) a).val=normalExponentDegree a.val
  have hv:=actualSourcePermutationVertexEquiv_val G (source_formal_members I G hspan)
    (source_priority I) (essentialPriority_family_lower G) a
  exact (congrArg normalExponentDegree hv).trans
    (sourceExponentPermutation_degree (source_priority I) a.val)

theorem historicalMembers (T : ActualPrescribedHistoricalFlattening I G hspan S C k)
    (a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)) :
    T.family.germs (T.historicalLabels a)=
      (localGermAlgEquiv T.chart T.chart_zero).symm (G.germs a) := T.members a

/-- No selector is chosen anew: use the exact original permutation and cast. -/
def historicalSelector (T : ActualPrescribedHistoricalFlattening I G hspan S C k) :=
  sourceFixedSelectorCast T.vertices
    (actualSourcePermutedFixedSelector G (source_formal_members I G hspan)
      (source_priority I) (essentialPriority_family_lower G) S)

theorem historicalSelector_contact (T : ActualPrescribedHistoricalFlattening I G hspan S C k) :
    ∀r,actualFixedSelectorContactAt T.historicalSelector T.family.germs r := T.contacts

end ActualPrescribedHistoricalFlattening

private theorem compatible_flattening_of_hs
    (A : GermIdeal n (ComplexModel n)) (hfg : IdealFGAt A.mem (0 : ComplexModel n))
    (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I))
    (hI : I=originalCoherentOriginIdeal A) (hspan : Ideal.span (range G.germs)=I)
    (hred : ∀k,ActualInheritedPrefixReducedAt G k)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)))
    (hContact : ∀k,actualFixedSelectorContactAt S G.germs k)
    (C : Set (ComplexModel n)) (k : ℕ) (hreg : RegularAtDim (n:=n) C 0 k)
    (hHS : ∀ᶠz in 𝓝 (0 : ComplexModel n),z∈C →
      ∀ℓ,hilbertSamuelAt A z ℓ=hilbertSamuelAt A 0 ℓ) :
    Nonempty (ActualPrescribedHistoricalFlattening I G hspan S C k) := by
  subst I
  obtain ⟨m,e,hdim,χ,hχ0,Ψ,hΨ0,Φ,hΦ0,_hm,_he,_ht,_hi,_hs,_hft,_hfi,_hfs,hFlat,
    _hE,hDiag,hV,F,hMember,hSpan,_hMem,hPrefix,hContacts,_hJ1,_hJ2⟩:=
    exists_actual_original_hs_free_product_presentation A hfg G hspan hred S hContact C hreg hHS
  exact ⟨{
    chart := Φ
    chart_zero := hΦ0
    centre := hFlat
    diagram := hDiag
    vertices := hV
    family := F
    members := hMember
    span := hSpan
    prefixes := hPrefix
    contacts := hContacts }⟩

private theorem current_whole_stalk
    {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] (x : X)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Θ.source⊆(chartAt (ComplexModel n) x).target)
    (hΘ0 : Θ.toFun (chartAt (ComplexModel n) x x)=0)
    (Λ : LocalHolomorphicEquivAt (n:=n) (0 : ComplexModel n)) (hΛ0 : Λ.toFun 0=0)
    (W : Set X) (z : ComplexModel n)
    (hz : z∈(currentCoordinateFlattening x Θ hΘ0 Λ hΛ0).target) (v : ComplexModel n → ℂ) :
    (GermIdeal.pullback (m:=n) Λ.toFun
      (vanishingIdeal (n:=n) (actualFixedFlatteningSet x Θ W))).mem z v ↔
      (actualFlattenedOriginalSheaf (vanishingIdeal (n:=n) W) x
        (currentCoordinateFlattening x Θ hΘ0 Λ hΛ0)).mem z v := by
  have hg : ∀ᶠa in 𝓝 z,MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) Λ.toFun a :=
    eventually_of_mem (Λ.isOpen_source.mem_nhds hz.1) fun a ha=>
      (Λ.toFun_holomorphic.differentiableAt (Λ.isOpen_source.mem_nhds ha)).mdifferentiableAt
  have hf : ∀ᶠa in 𝓝 (Λ.toFun z),
      MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) (actualFlatteningInverseMap x Θ) a :=
    eventually_of_mem (Θ.isOpen_target.mem_nhds hz.2) fun a ha=>
      actualFlatteningInverseMap_mdifferentiable x Θ hsrc a ha
  have hReplace : (GermIdeal.pullback (m:=n) Λ.toFun
      (vanishingIdeal (n:=n) (actualFixedFlatteningSet x Θ W))).mem z v ↔
      (GermIdeal.pullback (m:=n) Λ.toFun
        (actualFlattenedOriginalSheaf (vanishingIdeal (n:=n) W) x Θ)).mem z v := by
    constructor
    · intro hv
      refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.mono ?_ (GermIdeal.mem_pullback_iff.mp hv))
      rintro _ ⟨a,ha,rfl⟩
      exact ⟨a,(flattened_vanishing_mem_iff x Θ hsrc W (Λ.toFun z) hz.2 a).mpr ha,rfl⟩
    · intro hv
      refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.mono ?_ (GermIdeal.mem_pullback_iff.mp hv))
      rintro _ ⟨a,ha,rfl⟩
      exact ⟨a,(flattened_vanishing_mem_iff x Θ hsrc W (Λ.toFun z) hz.2 a).mp ha,rfl⟩
  exact hReplace.trans (local_pullback_comp_at (vanishingIdeal (n:=n) W)
    (fun _ _ hg=>hg.1) (actualFlatteningInverseMap x Θ) Λ.toFun z hf hg v)

private theorem flat_whole_stalk
    {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] (x : X)
    (Ξ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Ξ.source⊆(chartAt (ComplexModel n) x).target)
    (hΞ0 : Ξ.toFun (chartAt (ComplexModel n) x x)=0)
    (Φ : LocalHolomorphicEquivAt (n:=n) (0 : ComplexModel n))
    (A : GermIdeal n (ComplexModel n)) (W : Set X)
    (hA : ∀z∈Ξ.target,∀f,A.mem z f ↔
      (actualFlattenedOriginalSheaf (vanishingIdeal (n:=n) W) x Ξ).mem z f) :
    let Ω:=LocalHolomorphicEquivAt.comp Ξ Φ hΞ0
    ∀z∈Ω.target,∀v,(GermIdeal.pullback (m:=n) Φ.invFun A).mem z v ↔
      (vanishingIdeal (n:=n) (actualFixedFlatteningSet x Ω W)).mem z v := by
  intro Ω z hz v
  have hg : ∀ᶠa in 𝓝 z,MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) Φ.invFun a :=
    eventually_of_mem (Φ.isOpen_target.mem_nhds hz.1) fun a ha=>
      (Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds ha)).mdifferentiableAt
  have hf : ∀ᶠa in 𝓝 (Φ.invFun z),
      MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) (actualFlatteningInverseMap x Ξ) a :=
    eventually_of_mem (Ξ.isOpen_target.mem_nhds hz.2) fun a ha=>
      actualFlatteningInverseMap_mdifferentiable x Ξ hsrc a ha
  have hReplace : (GermIdeal.pullback (m:=n) Φ.invFun A).mem z v ↔
      (GermIdeal.pullback (m:=n) Φ.invFun
        (actualFlattenedOriginalSheaf (vanishingIdeal (n:=n) W) x Ξ)).mem z v := by
    constructor
    · intro hv
      refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.mono ?_ (GermIdeal.mem_pullback_iff.mp hv))
      rintro _ ⟨a,ha,rfl⟩
      exact ⟨a,(hA (Φ.invFun z) hz.2 a).mp ha,rfl⟩
    · intro hv
      refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.mono ?_ (GermIdeal.mem_pullback_iff.mp hv))
      rintro _ ⟨a,ha,rfl⟩
      exact ⟨a,(hA (Φ.invFun z) hz.2 a).mpr ha,rfl⟩
  have hComp:=local_pullback_comp_at (vanishingIdeal (n:=n) W)
    (fun _ _ hg=>hg.1) (actualFlatteningInverseMap x Ξ) Φ.invFun z hf hg v
  have hΩsrc : Ω.source⊆(chartAt (ComplexModel n) x).target:=fun _ hz=>hsrc hz.1
  exact hReplace.trans (hComp.trans (flattened_vanishing_mem_iff x Ω hΩsrc W z hz v))

section Rebase
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
 [ChartedSpace (ComplexModel n) X] [ChartedSpace (ComplexModel n) Y]
 [IsComplexManifold n X] [IsComplexManifold n Y]

/-- The exact source window in the SAME actual stage. -/
def actualRebaseWindow (x : X)
    (Ω : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x)) : Opens X :=
  ⟨flatDomain Ω,isOpen_flatDomain Ω⟩

/-- The literal target of the actual flattening. -/
def actualRebaseModel (x : X)
    (Ω : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x)) : Opens (ComplexModel n) :=
  ⟨Ω.target,Ω.isOpen_target⟩

/-- Whole actual source record in true flat coordinates. -/
def actualRebasedRecord (Q : MarkedIdeal n X) (x : X)
    (Ω : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x)) :
    MarkedIdeal n (actualRebaseModel x Ω) :=
  MarkedIdeal.pullback (fun z : actualRebaseModel x Ω=>actualFlatteningInverseMap x Ω z) Q

private theorem model_centre_regular (x : X)
    (Ξ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Ξ.source⊆(chartAt (ComplexModel n) x).target)
    (h0 : Ξ.toFun (chartAt (ComplexModel n) x x)=0)
    (C : Set X) (hC : IsClosedSubmanifold n C) (hxC : x∈C) :
    ∃k,RegularAtDim (n:=n) (actualFixedFlatteningSet x Ξ C) 0 k := by
  let V:=actualRebaseWindow x Ξ
  let U:=actualRebaseModel x Ξ
  let e : V ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ U:=
    actualFlatCoordinateDiffeomorph Ξ hsrc
  have hCV:=BlowupRestrictOpen.isClosedSubmanifold_preimage_val hC V
  have hCU:=MarkedIdealBiholomorphism.isClosedSubmanifold_preimage
    e.symm.contMDiff e.contMDiff e.symm_apply_apply e.apply_symm_apply hCV
  let z0 : U:=⟨0,actualFlattening_target_zero_mem x Ξ h0⟩
  have hzC : z0∈e.symm ⁻¹' ((Subtype.val : V → X) ⁻¹' C) := by
    change actualFlatteningInverseMap x Ξ 0∈C
    rw [actualFlatteningInverseMap_zero x Ξ h0]
    exact hxC
  obtain ⟨k,hReg⟩:=hCU.2 z0 hzC
  have hSet : e.symm ⁻¹' ((Subtype.val : V → X) ⁻¹' C)=
      (Subtype.val : U → ComplexModel n) ⁻¹' actualFixedFlatteningSet x Ξ C := by
    ext z
    exact (and_iff_right z.property).symm
  rw [hSet] at hReg
  exact ⟨k,regularAtDim_preimage_val_iff.mp hReg⟩

/-- The given next blowup, on EXACTLY its inverse image of the actual window.
The whole record transform agrees with the original transform restricted to
that SAME source.  The whole strict sheaf is also transported, for any W. -/
theorem prescribed_next_blowup_rebase
    (Q : MarkedIdeal n X) (hQ : Q.ideal.IsCoherent) (x : X)
    (Ω : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Ω.source⊆(chartAt (ComplexModel n) x).target)
    (C : Set X) (ρ : Y → X) (hρ : IsBlowupAlong n C ρ) (W : Set X) :
    let V:=actualRebaseWindow x Ω
    let U:=actualRebaseModel x Ω
    let hV:=V.isOpen.preimage hρ.contMDiff.continuous
    let YV : Opens Y:=⟨ρ ⁻¹' (V : Set X),hV⟩
    let e:=actualFlatCoordinateDiffeomorph Ω hsrc
    let r : YV → V:=fun z=>⟨ρ z.val,z.property⟩
    let c : Set U:=(fun z : U=>actualFlatteningInverseMap x Ω z) ⁻¹' C
    IsBlowupAlong n c (e ∘ r) ∧
      (actualRebasedRecord Q x Ω).geoTransform c (e ∘ r)=
        MarkedIdeal.pullback (Subtype.val : YV → Y) (Q.geoTransform C ρ) ∧
      (actualRebasedRecord Q x Ω).d=Q.d ∧
      (actualRebasedRecord Q x Ω).E=
        Q.E.map ((fun z : U=>actualFlatteningInverseMap x Ω z) ⁻¹' ·) ∧
      GermIdeal.pullback (m:=n) (fun z : U=>actualFlatteningInverseMap x Ω z)
          (vanishingIdeal (n:=n) W)=
        vanishingIdeal (n:=n) ((Subtype.val : U → ComplexModel n) ⁻¹'
          actualFixedFlatteningSet x Ω W) := by
  dsimp only
  let V:=actualRebaseWindow x Ω
  let U:=actualRebaseModel x Ω
  let hV:=V.isOpen.preimage hρ.contMDiff.continuous
  let YV : Opens Y:=⟨ρ ⁻¹' (V : Set X),hV⟩
  let e : V ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ U:=
    actualFlatCoordinateDiffeomorph Ω hsrc
  let r : YV → V:=fun z=>⟨ρ z.val,z.property⟩
  let QV:=MarkedIdeal.pullback (Subtype.val : V → X) Q
  have hr:=BlowupRestrictOpen.isBlowupAlong_restrict hρ V hV
  have hQV : QV.ideal.IsCoherent:=isCoherent_pullback contMDiff_subtype_val hQ
  have hcomp : MarkedIdeal.pullback e.symm QV=actualRebasedRecord Q x Ω :=
    marked_pullback_comp_hhol (fun _ _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem hQ hg)
      contMDiff_subtype_val e.symm.contMDiff (fun _=>rfl)
  have hBlow:=isBlowupAlong_comp_inverse e.symm.contMDiff e.contMDiff
    e.symm_apply_apply e.apply_symm_apply hr
  have hTransform:=MarkedIdeal.geoTransform_pullback e.symm.contMDiff e.contMDiff
    e.symm_apply_apply e.apply_symm_apply QV hQV
      ((Subtype.val : V → X) ⁻¹' C) hr.contMDiff
  rw [hcomp] at hTransform
  have hRestrict:=geoTransform_pullback_val_of_hhol
    (X:=CMfd.of (n:=n) X) (Y:=CMfd.of (n:=n) Y)
    (fun _ _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem hQ hg) hρ V hV
  refine ⟨hBlow,hTransform.trans hRestrict,rfl,rfl,?_⟩
  have hSheaf:=pullback_vanishingIdeal_preimage e.symm.contMDiff e.contMDiff
    e.symm_apply_apply e.apply_symm_apply (m:=n) (g:=(id : U → U)) contMDiff_id
      ((Subtype.val : V → X) ⁻¹' W)
  have hOpen:=BlowupRestrictOpen.pullback_vanishingIdeal_opens (n:=n) V (m:=n) e.symm W
  have hSet : e.symm ⁻¹' ((Subtype.val : V → X) ⁻¹' W)=
      (Subtype.val : U → ComplexModel n) ⁻¹' actualFixedFlatteningSet x Ω W := by
    ext z
    exact (and_iff_right z.property).symm
  have hId : GermIdeal.pullback (m:=n) (id : U → U)
      (vanishingIdeal (n:=n) (e.symm ⁻¹' ((Subtype.val : V → X) ⁻¹' W)))=
      vanishingIdeal (n:=n) (e.symm ⁻¹' ((Subtype.val : V → X) ⁻¹' W)) :=
    GermIdeal.ext (funext fun _=>funext fun _=>propext
      BlowupExistenceCodimOne.pullback_id_vanishingIdeal_mem_iff)
  have hInv : (Subtype.val ∘ e.symm : U → X)=
      (fun z : U=>actualFlatteningInverseMap x Ω z) := rfl
  have hFinal:=hOpen.symm.trans (hSheaf.symm.trans hId)
  simpa only [Function.comp_id,hSet,hInv] using hFinal

end Rebase

section PrescribedStage
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
 [ChartedSpace (ComplexModel n) X] [ChartedSpace (ComplexModel n) Y]
 [IsComplexManifold n X] [IsComplexManifold n Y]

/-- The literal whole sheaf already used by the SAME actual current stage. -/
def actualHistoricalStageSheaf (x : X)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (Λ : LocalHolomorphicEquivAt (n:=n) (0 : ComplexModel n)) (W : Set X) :=
  GermIdeal.pullback (m:=n) Λ.toFun
    (vanishingIdeal (n:=n) (actualFixedFlatteningSet x Θ W))

/-- Transparent output laws, always constructed by the producer below.
The domain is exactly the given next blowup's inverse image of the actual
window.  The full original marked record and full vanishing sheaf occur. -/
def ActualPrescribedNextBlowupLaws
    (Q : MarkedIdeal n X) (x : X)
    (Ω : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Ω.source⊆(chartAt (ComplexModel n) x).target)
    (C : Set X) (ρ : Y → X) (hρ : IsBlowupAlong n C ρ) (W : Set X) : Prop :=
    let V:=actualRebaseWindow x Ω
    let U:=actualRebaseModel x Ω
    let hV:=V.isOpen.preimage hρ.contMDiff.continuous
    let YV : Opens Y:=⟨ρ ⁻¹' (V : Set X),hV⟩
    let e:=actualFlatCoordinateDiffeomorph Ω hsrc
    let r : YV → V:=fun z=>⟨ρ z.val,z.property⟩
    let c : Set U:=(fun z : U=>actualFlatteningInverseMap x Ω z) ⁻¹' C
    IsBlowupAlong n c (e ∘ r) ∧
      (actualRebasedRecord Q x Ω).geoTransform c (e ∘ r)=
        MarkedIdeal.pullback (Subtype.val : YV → Y) (Q.geoTransform C ρ) ∧
      (actualRebasedRecord Q x Ω).d=Q.d ∧
      (actualRebasedRecord Q x Ω).E=
        Q.E.map ((fun z : U=>actualFlatteningInverseMap x Ω z) ⁻¹' ·) ∧
      GermIdeal.pullback (m:=n) (fun z : U=>actualFlatteningInverseMap x Ω z)
          (vanishingIdeal (n:=n) W)=
        vanishingIdeal (n:=n) ((Subtype.val : U → ComplexModel n) ⁻¹'
          actualFixedFlatteningSet x Ω W)

/-- Compose the SAME actual stage, its whole Q-record square and whole HS
presentation with the prescribed actual NEXT centre and actual NEXT map.
Whole HS constancy, compatible historical flattening, the ENTIRE true
strict sheaf, full ordered Q-record and actual next blowup are outputs. -/
theorem exists_actual_prescribed_geometric_rebase
    {ι : Type} [Fintype ι] {I : Ideal (HolGerm (ComplexModel n))}
    {G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)}
    {w : ι → ℕ} {old : ι → HolGerm (ComplexModel n)}
    {labels : ι≃actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)}
    {Cg : HolGerm (ComplexModel n)≃ₐ[ℂ]HolGerm (ComplexModel n)} {u : HolGerm (ComplexModel n)}
    (Q : MarkedIdeal n X) (hQ : Q.ideal.IsCoherent) (hQN : Q.N=univ) (x : X)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Θ.source⊆(chartAt (ComplexModel n) x).target)
    (hΘ0 : Θ.toFun (chartAt (ComplexModel n) x x)=0)
    (P : ActualMarkedFunctionSquare w old G.germs labels Cg u)
    (hOldTarget : (P.oldDomain : Set (ComplexModel n))⊆Θ.target)
    (hRecord : MarkedIdeal.pullback
      (fun z : P.currentDomain=>actualFlatteningInverseMap x Θ (P.chart.toFun z)) Q=
      actualCurrentNativeWeightedRecord P (fun a=>normalExponentDegree a.val)
        ((fun z : P.oldDomain=>actualFlatteningInverseMap x Θ z) ⁻¹' Q.N)
        (Q.E.map ((fun z : P.oldDomain=>actualFlatteningInverseMap x Θ z) ⁻¹' ·)))
    (W : Set X) (hI : I=originalCoherentOriginIdeal (actualHistoricalStageSheaf x Θ P.chart W))
    (hspan : Ideal.span (range G.germs)=I) (hred : ∀k,ActualInheritedPrefixReducedAt G k)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)))
    (hContact : ∀k,actualFixedSelectorContactAt S G.germs k)
    (R : ℕ → ℕ)
    (PHS : ActualGeometricInheritedNeighborhoodHS (actualHistoricalStageSheaf x Θ P.chart W) I G R)
    (hFunctions : PHS.representatives=P.currentFunctions) (hDomain : PHS.neighborhood⊆P.currentDomain)
    (hw : ∀a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I),
      0<normalExponentDegree a.val)
    (C : Set X) (ρ : Y → X) (hρ : IsBlowupAlong n C ρ) (hxC : x∈C) (hC : C⊆Q.cosupp) :
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
      ActualPrescribedNextBlowupLaws Q x Ω hΩsrc C ρ hρ W := by
  let A:=actualHistoricalStageSheaf x Θ P.chart W
  let Base:=currentCoordinateFlattening x Θ hΘ0 P.chart P.chart_zero
  have hBase0 : Base.toFun (chartAt (ComplexModel n) x x)=0 := by
    change P.chart.invFun (Θ.toFun (chartAt (ComplexModel n) x x))=0
    rw [hΘ0]
    exact local_invFun_zero P.chart P.chart_zero
  have hBaseSrc : Base.source⊆(chartAt (ComplexModel n) x).target:=fun _ hz=>hsrc hz.1
  have hBaseTarget : PHS.neighborhood⊆Base.target:=fun z hz=>
    ⟨P.inside_chart (hDomain hz),hOldTarget (P.inside_old (hDomain hz))⟩
  let O : Opens (ComplexModel n):=⟨PHS.neighborhood,PHS.isOpen_neighborhood⟩
  let Ξ:=coordinateTargetRestriction Base hBase0 O PHS.zero_mem hBaseTarget
  have hΞsrc : Ξ.source⊆(chartAt (ComplexModel n) x).target:=fun _ hz=>hBaseSrc hz.1
  have hΞ0 : Ξ.toFun (chartAt (ComplexModel n) x x)=0:=hBase0
  obtain ⟨k,hReg⟩:=model_centre_regular x Ξ hΞsrc hΞ0 C hρ.1 hxC
  have hHSFull:=actual_prescribed_centre_whole_hs Q hQN x Θ hsrc hΘ0 P hOldTarget hRecord
    A R PHS hFunctions hDomain hw C hC hxC
  have hHS : ∀ᶠz in 𝓝 (0 : ComplexModel n),z∈actualFixedFlatteningSet x Ξ C →
      ∀ℓ,hilbertSamuelAt A z ℓ=hilbertSamuelAt A 0 ℓ :=
    Eventually.of_forall fun z hz=>hHSFull z hz.1 hz.2
  obtain ⟨T⟩:=compatible_flattening_of_hs A (presentation_locally_fg PHS) I G hI hspan
    hred S hContact (actualFixedFlatteningSet x Ξ C) k hReg hHS
  let Ω:=LocalHolomorphicEquivAt.comp Ξ T.chart hΞ0
  have hΩsrc : Ω.source⊆(chartAt (ComplexModel n) x).target:=fun _ hz=>hΞsrc hz.1
  have hΩ0 : Ω.toFun (chartAt (ComplexModel n) x x)=0 := by
    change T.chart.toFun (Ξ.toFun (chartAt (ComplexModel n) x x))=0
    rw [hΞ0]
    exact T.chart_zero
  have hFlat (z : X) (hz : z∈flatDomain Ω) : z∈C ↔
      Ω.toFun (chartAt (ComplexModel n) x z)∈complexCoordinatePlane n k := by
    let a:=Ξ.toFun (chartAt (ComplexModel n) x z)
    have ha : a∈Ξ.target:=Ξ.mapsTo_toFun hz.2.1
    have hB : a∈actualFixedFlatteningSet x Ξ C ↔ z∈C := by
      change (a∈Ξ.target ∧ actualFlatteningInverseMap x Ξ a∈C) ↔ z∈C
      have hInv : actualFlatteningInverseMap x Ξ a=z:=
        flatInverse_flat Ξ (show z∈flatDomain Ξ from ⟨hz.1,hz.2.1⟩)
      rw [hInv]
      exact and_iff_right ha
    exact hB.symm.trans (T.centre a hz.2.2)
  have hCentre : (fun z : actualRebaseModel x Ω=>actualFlatteningInverseMap x Ω z) ⁻¹' C=
      (Subtype.val : actualRebaseModel x Ω → ComplexModel n) ⁻¹' complexCoordinatePlane n k := by
    ext z
    have hz:=(flatInverse_mem Ω z.property hΩsrc)
    have h:=hFlat (actualFlatteningInverseMap x Ω z) hz.1
    have hEval : Ω.toFun (chartAt (ComplexModel n) x (actualFlatteningInverseMap x Ω z))=
        (z : ComplexModel n):=hz.2
    rw [hEval] at h
    exact h
  have hCurrent : ∀z∈Ξ.target,∀f,A.mem z f ↔
      (actualFlattenedOriginalSheaf (vanishingIdeal (n:=n) W) x Ξ).mem z f := by
    intro z hz f
    exact current_whole_stalk x Θ hsrc hΘ0 P.chart P.chart_zero W z (hBaseTarget hz) f
  have hWhole:=flat_whole_stalk x Ξ hΞsrc hΞ0 T.chart A W hCurrent
  have hOriginPull:=origin_pullback_eq_of_holomorphic_germ T.chart.invFun
    (local_invFun_holomorphic T.chart T.chart_zero) (local_invFun_zero T.chart T.chart_zero)
    A (presentation_locally_fg PHS)
  have hOrigin : prescribedFlatOriginIdeal I T.chart T.chart_zero=
      originalCoherentOriginIdeal (vanishingIdeal (n:=n) (actualFixedFlatteningSet x Ω W)) := by
    have h0T : (0 : ComplexModel n)∈Ω.target:=actualFlattening_target_zero_mem x Ω hΩ0
    have hGeometric:=originIdeal_eq_of_mem_at_zero
      (GermIdeal.pullback (m:=n) T.chart.invFun A)
      (vanishingIdeal (n:=n) (actualFixedFlatteningSet x Ω W)) (hWhole 0 h0T)
    have hMap : prescribedFlatOriginIdeal I T.chart T.chart_zero=
        originalCoherentOriginIdeal (GermIdeal.pullback (m:=n) T.chart.invFun A) :=
      (congrArg (Ideal.map (localGermAlgEquiv T.chart T.chart_zero).symm.toRingEquiv.toRingHom) hI).trans
        hOriginPull.symm
    exact hMap.trans hGeometric
  refine ⟨Ξ,hΞsrc,hΞ0,rfl,rfl,k,T,hΩsrc,hΩ0,hCentre,hWhole,hOrigin,?_⟩
  exact prescribed_next_blowup_rebase Q hQ x Ω hΩsrc C ρ hρ W

/-- The complete SAME-stage prescribed-next-centre output, for EVERY genuine
next blowup through its original point.  This property is never an input. -/
def ActualPrescribedStageRebaseLaws
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
      ActualPrescribedNextBlowupLaws Q x Ω hΩsrc C ρ hρ W

end PrescribedStage

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

/-- Original geometry produces the SAME actual stage once, then internally
constructs compatible historical geometric rebasing for every prescribed
actual next centre through y and its given actual next blowup. -/
theorem exists_actual_geometric_stage_prescribed_rebasing
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
            D.targetSpan (actualAdaptedHistoricalCurrentSource D).selector (hilbertSamuelValue I) PHS := by
  dsimp only
  intro hcut
  let w:=fun a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (d+(t+2)) I)=>
    normalExponentDegree a.val
  let M : MarkedIdeal (d+(t+2)) U:=⟨univ,E,weightedFunctionIdeal w (fun a (z : U)=>c a z),weightedCommonMark w⟩
  let ZC:=((Subtype.val : U → ComplexModel (d+(t+2))) ⁻¹' complexCoordinatePlane (d+(t+2)) d)
  let Q:=M.geoTransform ZC π
  have hcu (a) : MDifferentiable 𝓘(ℂ,ComplexModel (d+(t+2))) 𝓘(ℂ,ℂ) (fun z : U=>c a z) := by
    intro z
    exact ((holomorphicAt_of_mdifferentiableOn U.isOpen (hc a) z.property).comp_contMDiff
      (Eventually.of_forall fun _=>(contMDiff_subtype_val (U:=U)).contMDiffAt)).mdifferentiableAt
  have hSourceCoherent:=isCoherent_weightedFunctionIdeal w (fun a (z : U)=>c a z) hcu
  have hQN : Q.N=univ:=geoTransform_N_eq_univ (𝔪:=M) rfl hπ
  have hQCoherent : Q.ideal.IsCoherent := by
    rw [geoTransform_ideal_eq_controlledTransform (𝔪:=M) rfl hSourceCoherent hπ]
    exact CoherentIdealColon.isCoherent_colon_of_isCoherent
      (GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff hSourceCoherent)
      (DivisorMetric.isCoherent_of_isInvertible (isInvertible_idealPow_exceptionalDivisor hπ (weightedCommonMark w)))
  obtain ⟨e,b,Θ,hΘ0,he,hΘsrc,hSquare,hp,f,hqf,hvf,Cg,u,hu,D,P,hOldTarget,hRecord,
    hStrict,hOriginCurrent,PHS,hRepresentatives,hPHS,hMap,hFlags,hIntrinsic,hContactLaws⟩:=
    exists_actual_geometric_stage_selected_contact_centres I G hmem hw S hred hContact
      U h0U c hc hrep hCos E π hπ y hy W hWa Φ hΦsrc hΦ0 hΦid hΦdom hOrigin hcut
  refine ⟨e,b,Θ,hΘ0,he,hΘsrc,hSquare,hp,f,hqf,hvf,Cg,u,hu,D,P,hOldTarget,hRecord,
    hStrict,hOriginCurrent,PHS,hRepresentatives,hPHS,hMap,hFlags,hIntrinsic,hContactLaws,?_⟩
  intro Y _ _ _ Cnext ρ hρ hyC hC
  have hwCurrent : ∀a : actualInitialVertices MonomialOrder.degLex
      (analyticZeroTaylorIdeal (d+(t+2)) (actualAdaptedHistoricalCurrentSource D).ideal),
      0<normalExponentDegree a.val := by
    intro a
    obtain ⟨a,rfl⟩:=(actualAdaptedOriginalLabelEquiv D).surjective a
    rw [actualAdaptedOriginalLabelEquiv_degree D a]
    exact hw a
  exact exists_actual_prescribed_geometric_rebase Q hQCoherent hQN y Θ hΘsrc hΘ0
    P hOldTarget hRecord (strictTransform (d+(t+2)) π W) hOriginCurrent D.targetSpan D.targetPrefix
    (actualAdaptedHistoricalCurrentSource D).selector D.targetContact (hilbertSamuelValue I)
    PHS hRepresentatives hPHS hwCurrent Cnext ρ hρ hyC hC

end
end Hironaka.HironakaActualPrescribedCentreRebasing
