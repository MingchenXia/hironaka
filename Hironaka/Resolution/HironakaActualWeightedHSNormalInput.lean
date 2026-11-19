import Hironaka.Resolution.HironakaActualOriginalInitialHSPhase
import Hironaka.Resolution.HironakaActualSectionBoundaryGeometry
import Hironaka.Resolution.HironakaSmoothSubmersionRelativeGeometry
import Hironaka.Resolution.HironakaActualRelativeNormalGeometry
import Hironaka.Resolution.HironakaActualWeightedNormalPadding
import Hironaka.Resolution.HironakaActualRelativeNormalWindowFactory
import Hironaka.Resolution.HironakaActualOpenEmbeddingCanonicalExtension

/-! The literal actual weighted HS record on its genuine one-normal product.
Blueprint: hironaka-actual-weighted-hs-normal-input-20261102.tex. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualWeightedHSNormalInput
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaActualOriginalInitialHSPhase HironakaActualCoherentWeightedCoefficientMarked
  HironakaActualWeightedCoefficientCompression HironakaRelativeNormalMonomialBasis
  HironakaActualGeometricCurrentNeighborhoodHS HironakaActualOpenZeroSectionDifferentials
  HironakaActualHistoricalHSMarkedDomain HironakaActualRelativeNormalJetDivision
  HironakaActualFormalInitialDiagram HironakaActualRelativeNormalGeometry
  HironakaActualZeroCoordinateContactSeed HironakaActualGraphFunctionalIdeal
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  GermIdealPullbackCalculus RelativePrincipalizationSpan InvertibleIdealQuotient
  IdealOrderArithmetic HironakaSmoothSubmersionRelativeRestriction
  HironakaActualNormalZeroAnalyticSaturation RestrictedIdealExtension
  HironakaActualWeightedNormalPadding GermIdealTotalTransform
  HironakaSmoothSubmersionRelativeGeometry HironakaSmoothSubmersionMonomialOrdering
  HironakaActualSectionBoundaryGeometry BlowupTowers HironakaSmoothSubmersionOrderedChoiceImageTrace
  HironakaSmoothSubmersionCoefficientIdeals
  GermIdealOrder IdealWeightPowers OrderMultiplicativity OrderTaylor
  HironakaActualRelativeNormalWindowFactory
  HironakaActualPrescribedCentreRebasing HironakaActualFixedFlatteningHSComparison
  HironakaActualLocalHolomorphicOriginPullback HironakaActualFixedInheritedSelector
  HironakaActualInheritedNestedContactFlag HironakaActualInheritedCurrentSourceRelabel
  HironakaActualVanishingIntrinsicHSTransport HironakaEmbeddedAnalytic
  ResolutionInvariantSpec CanonicalCentres
  HironakaSmoothCentreCoherentDomain HironakaHolomorphicJetRankLoci HironakaHolomorphicJetChartInvariance
  HironakaRelativeNormalDeformationInitialRelations

private theorem normal_contMDiff {n : ℕ} (U : Opens (ComplexModel n)) :
    ContMDiff 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ℂ) ∞ (relativeNormalCoordinate U):=by
  have hEq : relativeNormalCoordinate U=
      (EuclideanSpace.proj ((0 : Fin 1).natAdd n) : ComplexModel (n+1) →L[ℂ] ℂ)∘
        (Subtype.val : productOpen U→ComplexModel (n+1)):=by
    funext z
    simp [relativeNormalCoordinate,addedCoordinate,graphFunction,zeroFunction]
  rw [hEq]
  exact (EuclideanSpace.proj ((0 : Fin 1).natAdd n) : ComplexModel (n+1) →L[ℂ] ℂ).contMDiff.comp contMDiff_subtype_val

private def normalPowerIdeal {n : ℕ} (U : Opens (ComplexModel n)) (d : ℕ) :
    GermIdeal (n+1) (productOpen U):=
  finiteFunctionIdeal (fun (_ : Unit) (z : productOpen U)=>relativeNormalCoordinate U z^d)

private theorem normalPower_coherent {n : ℕ} (U : Opens (ComplexModel n)) (d : ℕ) :
    (normalPowerIdeal U d).IsCoherent:=
  isCoherent_finiteFunctionIdeal _ (fun _=>((normal_contMDiff U).mdifferentiable (by simp)).pow d)

private theorem projection_section {n : ℕ} (U : Opens (ComplexModel n)) (x : U) :
    projection U (zeroSection U x)=x:=by
  apply Subtype.ext
  exact HironakaRelativeNormalIdeal.tangentProjection_tangentInclusion n 1 x.val

private theorem section_normal_zero {n : ℕ} (U : Opens (ComplexModel n)) (x : U) :
    relativeNormalCoordinate U (zeroSection U x)=0:=by
  have hq : HironakaActualCentreJointJets.actualJointNormalProjection n 1 (zeroSection U x).val=0:=by
    change HironakaActualCentreJointJets.actualJointNormalProjection n 1
      (HironakaRelativeNormalIdeal.tangentInclusion n 1 x.val)=0
    simp
  simpa [relativeNormalCoordinate,addedCoordinate,graphFunction,zeroFunction] using
    congrArg (fun z : ComplexModel 1=>z 0) hq

variable {n : ℕ} {A : GermIdeal n (ComplexModel n)} {I : Ideal (HolGerm (ComplexModel n))}
  {G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)} {R : ℕ→ℕ}

private theorem presentation_functions_mdifferentiable
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R) (i) :
    MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ)
      (fun z : presentationOpen PHS=>PHS.representatives i z.val):=by
  intro z
  have h:=holomorphicAt_of_mdifferentiableOn PHS.isOpen_neighborhood
    (mdifferentiableOn_iff_differentiableOn.mpr (PHS.holomorphicOn i)) z.property
  exact (h.comp_contMDiff (Eventually.of_forall fun _=>
    (contMDiff_subtype_val (U:=presentationOpen PHS)).contMDiffAt)).mdifferentiableAt

/-- The complete compressed actual normal record, with the SAME original Q. -/
def phaseNormalMarked (PHS : ActualGeometricInheritedNeighborhoodHS A I G R)
    {M : Type u} (η : presentationOpen PHS→M) (E : List (Set M)) :
    MarkedIdeal (n+1) (productOpen (presentationOpen PHS)):=
  let Q:=initialWeightedRecord PHS η E
  ⟨univ,Q.E.map (projection (presentationOpen PHS) ⁻¹' ·),
    sumIdeal (GermIdeal.pullback (m:=n+1) (projection (presentationOpen PHS)) Q.ideal)
      (normalPowerIdeal (presentationOpen PHS) Q.d),Q.d⟩

theorem phase_normal_entire_record (PHS : ActualGeometricInheritedNeighborhoodHS A I G R)
    {M : Type u} (η : presentationOpen PHS→M) (E : List (Set M)) :
    phaseNormalMarked PHS η E=
      (⟨univ,(E.map (η ⁻¹' ·)).map (projection (presentationOpen PHS) ⁻¹' ·),
        sumIdeal (GermIdeal.pullback (m:=n+1) (projection (presentationOpen PHS))
          (initialWeightedRecord PHS η E).ideal)
          (finiteFunctionIdeal (fun (_ : Unit) (z : productOpen (presentationOpen PHS))=>
            relativeNormalCoordinate (presentationOpen PHS) z^(initialWeightedRecord PHS η E).d)),
        (initialWeightedRecord PHS η E).d⟩ : MarkedIdeal (n+1) (productOpen (presentationOpen PHS))):=rfl

private theorem phase_coherent (PHS : ActualGeometricInheritedNeighborhoodHS A I G R)
    {M : Type u} (η : presentationOpen PHS→M) (E : List (Set M)) :
    (phaseNormalMarked PHS η E).ideal.IsCoherent:=
  RestrictedIdealExtension.isCoherent_sumIdeal
    (isCoherent_pullback (projection_contMDiff (presentationOpen PHS))
      (isCoherent_weightedFunctionIdeal _ _ (presentation_functions_mdifferentiable PHS)))
    (normalPower_coherent (presentationOpen PHS) (initialWeightedRecord PHS η E).d)

/-- The candidate record IS the literal SAME old HS family plus the new member. -/
theorem phase_normal_weighted_record (PHS : ActualGeometricInheritedNeighborhoodHS A I G R)
    {M : Type u} (η : presentationOpen PHS→M) (E : List (Set M)) :
    paddingMarked (presentationOpen PHS)
      (fun i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)=>normalExponentDegree i.val)
      (fun i (z : presentationOpen PHS)=>PHS.representatives i z.val) (E.map (η ⁻¹' ·))=
      phaseNormalMarked PHS η E:=
  entire_padding_record (presentationOpen PHS)
    (fun i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)=>normalExponentDegree i.val)
    (fun i (z : presentationOpen PHS)=>PHS.representatives i z.val)
    (presentation_functions_mdifferentiable PHS) (E.map (η ⁻¹' ·))

private theorem normal_trace_le {d j : ℕ} (U : Opens (ComplexModel d))
    (hj : 0<j) {J : GermIdeal d U} (hJ : J.IsCoherent) :
    (GermIdeal.pullback (m:=d) (zeroSection U) (normalPowerIdeal U j)).Le J:=by
  have hPull : GermIdeal.pullback (m:=d) (zeroSection U) (normalPowerIdeal U j)=
      finiteFunctionIdeal (fun (_ : Unit) (_ : U)=>(0 : ℂ)):=by
    rw [normalPowerIdeal,finiteFunctionIdeal_pullback
      (fun (_ : Unit) (z : productOpen U)=>relativeNormalCoordinate U z^j)
      (fun _=>((normal_contMDiff U).mdifferentiable (by simp)).pow j) (zeroSection U) (zeroSection_contMDiff U)]
    apply congrArg (finiteFunctionIdeal (n:=d))
    funext i x
    exact (congrArg (fun a : ℂ=>a^j) (section_normal_zero U x)).trans (zero_pow (Nat.ne_of_gt hj))
  intro x f hf
  rw [hPull] at hf
  apply mem_of_isInSpanAt_mem hJ
  refine IsInSpanAt.mono ?_ hf
  rintro _ ⟨i,rfl⟩
  exact mem_of_isInSpanAt_mem hJ
    ⟨holomorphicAt_const 0,0,(fun i=>i.elim0),(fun i=>i.elim0),(fun i=>i.elim0),(fun i=>i.elim0),
      Eventually.of_forall (fun _=>by simp)⟩

private theorem normal_sum_trace {d j : ℕ} (U : Opens (ComplexModel d))
    (hj : 0<j) (J : GermIdeal d U) (hJ : J.IsCoherent) :
    GermIdeal.pullback (m:=d) (zeroSection U)
      (sumIdeal (GermIdeal.pullback (m:=d+1) (projection U) J) (normalPowerIdeal U j))=J:=by
  rw [pullback_sumIdeal_dimensions (zeroSection_contMDiff U)
    (isCoherent_pullback (projection_contMDiff U) hJ) (normalPower_coherent U j)]
  have hFirst : GermIdeal.pullback (m:=d) (zeroSection U)
      (GermIdeal.pullback (m:=d+1) (projection U) J)=J:=by
    rw [←coherent_pullback_comp (projection_contMDiff U) (zeroSection_contMDiff U) J hJ,
      show (projection U)∘zeroSection U=id from funext (projection_section U),
      BlowupControlledTransform.pullback_id hJ]
  rw [hFirst]
  apply GermIdeal.ext
  funext x f
  apply propext
  constructor
  · intro hf
    exact mem_of_isInSpanAt_mem hJ (IsInSpanAt.mono
      (fun g hg=>hg.elim id (normal_trace_le U hj hJ x g)) (mem_sumIdeal_iff.mp hf))
  · exact le_sumIdeal_left hJ x f

/-- All four fields pull back to the literal ORIGINAL weighted marked record. -/
theorem phase_normal_zero_section_record (PHS : ActualGeometricInheritedNeighborhoodHS A I G R)
    (hw : ∀i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I),
      0<normalExponentDegree i.val)
    {M : Type u} (η : presentationOpen PHS→M) (E : List (Set M)) :
    markedPullback (m:=n) (zeroSection (presentationOpen PHS)) (phaseNormalMarked PHS η E)=
      initialWeightedRecord PHS η E:=by
  let U:=presentationOpen PHS
  let Q:=initialWeightedRecord PHS η E
  have hQ : Q.ideal.IsCoherent:=isCoherent_weightedFunctionIdeal _ _ (presentation_functions_mdifferentiable PHS)
  have hpos : 0<Q.d:=weightedCommonMark_pos _ hw
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl ?_ (normal_sum_trace U hpos Q.ideal hQ) rfl
  change (Q.E.map (projection U ⁻¹' ·)).map (zeroSection U ⁻¹' ·)=Q.E
  rw [List.map_map]
  change Q.E.map (fun H : Set U=>zeroSection U ⁻¹' (projection U ⁻¹' H))=Q.E
  have hFun : (fun H : Set U=>zeroSection U ⁻¹' (projection U ⁻¹' H))=id:=by
    funext H
    ext x
    change projection U (zeroSection U x)∈H ↔ x∈H
    rw [projection_section]
  rw [hFun,List.map_id]

/-- Every actual along-zero-carrier derivative pulls back to the SAME source. -/
theorem phase_normal_zero_section_derivatives (PHS : ActualGeometricInheritedNeighborhoodHS A I G R)
    (hw : ∀i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I),
      0<normalExponentDegree i.val)
    {M : Type u} (η : presentationOpen PHS→M) (E : List (Set M)) (j : ℕ) :
    GermIdeal.pullback (m:=n) (zeroSection (presentationOpen PHS))
      (DerivativeIdealAlong.iterDerivIdealAlong (liftedCarrier (univ : Set (presentationOpen PHS)))
        (phaseNormalMarked PHS η E).ideal j)=
      DerivativeIdealAlong.iterDerivIdealAlong (univ : Set (presentationOpen PHS))
        (initialWeightedRecord PHS η E).ideal j:=by
  have hTrace:=congrArg (fun K : MarkedIdeal n (presentationOpen PHS)=>K.ideal)
    (phase_normal_zero_section_record PHS hw η E)
  change GermIdeal.pullback (m:=n) (zeroSection (presentationOpen PHS))
    (phaseNormalMarked PHS η E).ideal=(initialWeightedRecord PHS η E).ideal at hTrace
  rw [zero_section_iterDerivIdealAlong (presentationOpen PHS)
    (A:=univ) HomogenizedGlueingTower.isClosedSubmanifold_univ
    (phaseNormalMarked PHS η E).ideal (phase_coherent PHS η E) j,hTrace]

/-- The original source domain yields the ACTUAL padded domain with ALL old E. -/
theorem phase_normal_original_domain (PHS : ActualGeometricInheritedNeighborhoodHS A I G R)
    {M : Type u} (η : presentationOpen PHS→M) (E : List (Set M))
    (hQ : ResolutionInvariantSpec.IsInvDomain n (initialWeightedRecord PHS η E)) :
    ResolutionInvariantSpec.IsInvDomain (n+1) (phaseNormalMarked PHS η E):=by
  let U:=presentationOpen PHS
  let Q:=initialWeightedRecord PHS η E
  have hD:=isInvDomain_markedPullback_submersion (X:=CMfd.of (n:=n) U)
    (Y:=CMfd.of (n:=n+1) (productOpen U)) (projection_isSubmersion (U:=U)) Q hQ
  have he : n+((n+1)-n)=n+1:=by omega
  rw [he] at hD
  refine ⟨⟨hD.isWellFormed.isClosedSubmanifold_N,phase_coherent PHS η E,
    hD.isWellFormed.isSNCDivisor,hD.isWellFormed.isTransverse⟩,
    hD.dimLE,hD.one_le_d,?_⟩
  intro z hz
  obtain ⟨f,hf,hfreq⟩:=hD.isNonzeroAlongAt z hz
  exact ⟨f,le_sumIdeal_left (isCoherent_pullback (projection_contMDiff U) hQ.isWellFormed.isCoherent) z f hf,hfreq⟩

private theorem normalPower_cosupport {d j : ℕ} (U : Opens (ComplexModel d)) (hj : 0<j) :
    cosupport (d+1) univ (normalPowerIdeal U j) j={z | relativeNormalCoordinate U z=0}:=by
  ext z
  have hhol : HolomorphicAt (d+1) (relativeNormalCoordinate U) z:=
    Eventually.of_forall (normalCoordinate_mdifferentiable U)
  constructor
  · intro hz
    have hMember : (normalPowerIdeal U j).mem z (fun w=>relativeNormalCoordinate U w^j):=
      isInSpanAt_self ⟨(),rfl⟩ (Eventually.of_forall ((normalCoordinate_mdifferentiable U).pow j))
    have hPower:=mem_idealPow_of_vanishesToOrderOn_univ (hz.2 _ hMember)
    have hRoot : (idealPow (pointIdeal (d+1) z) 1).mem z (relativeNormalCoordinate U):=
      mem_idealPow_of_pow_mem hhol (by omega : 1≤j) (by simpa only [Nat.mul_one] using hPower)
    exact apply_eq_zero_of_mem_idealPow_pointIdeal le_rfl hRoot
  · intro hz
    have hPoint : (pointIdeal (d+1) z).mem z (relativeNormalCoordinate U):=by
      refine ⟨hhol,Eventually.of_forall ?_⟩
      intro y hy
      obtain rfl:=Set.mem_singleton_iff.mp hy
      exact hz
    have hPow:=pow_mem_idealPow hPoint hhol j
    refine ⟨mem_univ _,fun f hf=>?_⟩
    exact IsInSpanAt.vanishesToOrderOn hf (by
      rintro _ ⟨i,rfl⟩
      exact ⟨_,hPow,Eventually.of_forall (fun _ _=>rfl)⟩)

private theorem section_projection {d : ℕ} (U : Opens (ComplexModel d))
    (z : productOpen U) (hz : relativeNormalCoordinate U z=0) :
    zeroSection U (projection U z)=z:=by
  have hZero : HironakaActualCentreJointJets.actualJointNormalProjection d 1 z.val=0:=by
    ext i
    have hi : i=0:=Fin.eq_zero i
    subst i
    simpa [relativeNormalCoordinate,addedCoordinate,graphFunction,zeroFunction] using hz
  apply Subtype.ext
  change HironakaRelativeNormalIdeal.tangentInclusion d 1
    (HironakaRelativeNormalIdeal.tangentProjection d 1 z.val)=z.val
  simpa only [HironakaActualIntrinsicStableAmbientIso.join,hZero,map_zero,add_zero] using
    (HironakaActualIntrinsicStableAmbientIso.join_projections (n:=d) (m:=1) z.val)

/-- The ENTIRE original weighted HS cut lies in precisely the true zero section. -/
theorem phase_normal_cosupp (PHS : ActualGeometricInheritedNeighborhoodHS A I G R)
    (hw : ∀i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I),
      0<normalExponentDegree i.val)
    {M : Type u} (η : presentationOpen PHS→M) (E : List (Set M)) :
    (phaseNormalMarked PHS η E).cosupp=
      zeroSection (presentationOpen PHS) '' (initialWeightedRecord PHS η E).cosupp:=by
  let U:=presentationOpen PHS
  let Q:=initialWeightedRecord PHS η E
  have hQ : Q.ideal.IsCoherent:=isCoherent_weightedFunctionIdeal _ _ (presentation_functions_mdifferentiable PHS)
  have hLeft : (GermIdeal.pullback (m:=n+1) (projection U) Q.ideal).IsCoherent:=
    isCoherent_pullback (projection_contMDiff U) hQ
  have hNormal:=(normalPower_coherent U Q.d)
  have hpos : 0<Q.d:=weightedCommonMark_pos _ hw
  change cosupport (n+1) univ
    (sumIdeal (GermIdeal.pullback (m:=n+1) (projection U) Q.ideal) (normalPowerIdeal U Q.d)) Q.d=_
  rw [cosupport_sumIdeal (fun _ _ hf=>GermIdeal.IsCoherent.holomorphicAt_mem hLeft hf)
    (fun _ _ hf=>GermIdeal.IsCoherent.holomorphicAt_mem hNormal hf),
    HironakaSmoothSubmersionOrder.cosupport_pullback_eq (projection_isSubmersion (U:=U)) hQ Q.d,
    normalPower_cosupport U hpos]
  ext z
  constructor
  · rintro ⟨hz,hzero⟩
    exact ⟨projection U z,hz,section_projection U z hzero⟩
  · rintro ⟨x,hx,rfl⟩
    refine ⟨?_,section_normal_zero U x⟩
    change projection U (zeroSection U x)∈Q.cosupp
    rw [projection_section]
    exact hx

/-- Impose an ACTUAL coordinate window, retaining the SAME family and reference. -/
def restrictedPresentation (PHS : ActualGeometricInheritedNeighborhoodHS A I G R)
    (U : Opens (ComplexModel n)) (hU : U≤presentationOpen PHS) (h0U : (0 : ComplexModel n)∈U) :
    ActualGeometricInheritedNeighborhoodHS A I G R where
  representatives:=PHS.representatives
  holomorphicAtZero:=PHS.holomorphicAtZero
  sameGerms:=PHS.sameGerms
  neighborhood:=U
  isOpen_neighborhood:=U.isOpen
  zero_mem:=h0U
  holomorphicOn:=fun i=>(PHS.holomorphicOn i).mono hU
  wholeGeneration:=fun y hy=>PHS.wholeGeneration y (hU hy)
  holomorphicAt:=fun y hy=>PHS.holomorphicAt y (hU hy)
  wholeHS:=fun y hy=>PHS.wholeHS y (hU hy)

/-- The SAME actual original Q is restricted literally, with no new family. -/
theorem restricted_phase_entire_record (PHS : ActualGeometricInheritedNeighborhoodHS A I G R)
    (U : Opens (ComplexModel n)) (hU : U≤presentationOpen PHS) (h0U : (0 : ComplexModel n)∈U)
    {M : Type u} (η : presentationOpen PHS→M) (E : List (Set M)) :
    initialWeightedRecord (restrictedPresentation PHS U hU h0U) (η∘baseInclusion hU) E=
      MarkedIdeal.pullback (baseInclusion hU) (initialWeightedRecord PHS η E):=by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl ?_ ?_ rfl
  · change E.map ((η∘baseInclusion hU) ⁻¹' ·)=(E.map (η ⁻¹' ·)).map (baseInclusion hU ⁻¹' ·)
    rw [List.map_map]
    rfl
  · exact (finiteFunctionIdeal_pullback
      (fun (i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I))
        (z : presentationOpen PHS)=>PHS.representatives i z.val^
          (weightedCommonMark (fun i : actualInitialVertices MonomialOrder.degLex
            (analyticZeroTaylorIdeal n I)=>normalExponentDegree i.val)/normalExponentDegree i.val))
      (fun i=>(presentation_functions_mdifferentiable PHS i).pow _)
      (baseInclusion hU) (baseInclusion_contMDiff hU)).symm

/-- The original domain is preserved on the actually chosen moving window. -/
theorem restricted_phase_original_domain (PHS : ActualGeometricInheritedNeighborhoodHS A I G R)
    (U : Opens (ComplexModel n)) (hU : U≤presentationOpen PHS) (h0U : (0 : ComplexModel n)∈U)
    {M : Type u} (η : presentationOpen PHS→M) (E : List (Set M))
    (hQ : ResolutionInvariantSpec.IsInvDomain n (initialWeightedRecord PHS η E)) :
    ResolutionInvariantSpec.IsInvDomain n
      (initialWeightedRecord (restrictedPresentation PHS U hU h0U) (η∘baseInclusion hU) E):=by
  have hb : HironakaBaseChange.IsOpenHoloEmbedding n (baseInclusion hU):=
    ⟨MaxLocusLocal.nestedOpens (presentationOpen PHS) U,
      (MaxLocusLocal.nestedOpensDiffeo (n:=n) hU).symm,fun _=>rfl⟩
  have h:=HironakaActualOpenEmbeddingCanonicalExtension.isInvDomain_pullback_of_isOpenHoloEmbedding
    (X:=CMfd.of (n:=n) (presentationOpen PHS)) (Y:=CMfd.of (n:=n) U) (baseInclusion hU) hb hQ
  exact (restricted_phase_entire_record PHS U hU h0U η E).symm ▸ h

/-- ONLY original analytic input constructs the literal weighted normal input;
its source native driver is retained, and no desired target CAN is supplied. -/
theorem exists_original_initial_hs_normal_input
    {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] (W : Set X) (hW : IsComplexAnalyticSubset (n:=n) W)
    (a : X) (ha : a∈singularSet (n:=n) W) (E : List (Set X)) (hE : NormalCrossings.IsSNCDivisor n E)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) a a))
    (hsrc : Φ.source⊆(chartAt (ComplexModel n) a).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) a a)=0) :
    ∃(Ψ : LocalHolomorphicEquivAt (n:=n) (0 : ComplexModel n)) (hΨ0 : Ψ.toFun 0=0),
      let Ξ:=currentCoordinateFlattening a Φ hΦ0 Ψ hΨ0
      let B0:=vanishingIdeal (n:=n) (actualFixedFlatteningSet a Ξ W)
      let I0:=originalCoherentOriginIdeal B0
      ∃(G0 : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I0))
        (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I0)))
        (PHS : ActualGeometricInheritedNeighborhoodHS B0 I0 G0
          (fun ℓ=>hilbertSamuelAt (vanishingIdeal (n:=n) W) a ℓ)),
        Ideal.span (range G0.germs)=I0 ∧
        (∀i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I0),
          0<normalExponentDegree i.val) ∧
        (∀k,ActualInheritedPrefixReducedAt G0 k) ∧
        (∀k,actualFixedSelectorContactAt S G0.germs k) ∧
      ∃(V : Opens X) (η : presentationOpen PHS ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ V),
        a∈V ∧ (∀z,(η z : X)=actualFlatteningInverseMap a Ξ z.val) ∧
        (∀z ℓ,hilbertSamuelAt B0 z.val ℓ=hilbertSamuelAt (vanishingIdeal (n:=n) W) (η z : X) ℓ) ∧
        let Q:=initialWeightedRecord PHS (fun z=>(η z : X)) E
        let J:=phaseNormalMarked PHS (fun z=>(η z : X)) E
        IsInvDomain n Q ∧
        Q.cosupp={z | ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) W) (η z : X) ℓ=
          hilbertSamuelAt (vanishingIdeal (n:=n) W) a ℓ} ∧
        Q.cosupp⊆(fun z=>(η z : X)) ⁻¹' singularSet (n:=n) W ∧
        IsInvDomain (n+1) J ∧
        markedPullback (m:=n) (zeroSection (presentationOpen PHS)) J=Q ∧
        J.cosupp=zeroSection (presentationOpen PHS) ''
          {z | ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) W) (η z : X) ℓ=
            hilbertSamuelAt (vanishingIdeal (n:=n) W) a ℓ} ∧
        zeroSection (presentationOpen PHS) (⟨0,PHS.zero_mem⟩ : presentationOpen PHS)∈J.cosupp ∧
        (∀j,GermIdeal.pullback (m:=n) (zeroSection (presentationOpen PHS))
          (DerivativeIdealAlong.iterDerivIdealAlong (liftedCarrier (univ : Set (presentationOpen PHS))) J.ideal j)=
            DerivativeIdealAlong.iterDerivIdealAlong (univ : Set (presentationOpen PHS)) Q.ideal j) ∧
        ∀(K : Set (presentationOpen PHS)),IsCompact K →
        ∀(O : Opens (presentationOpen PHS)),(O : Set (presentationOpen PHS))⊆K →
        ∃(Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n:=n) O) Y),
          IsCanonical (MarkedIdeal.pullback (Subtype.val : O→presentationOpen PHS) Q)
            ((canonicalInvariant n).inv (MarkedIdeal.pullback (Subtype.val : O→presentationOpen PHS) Q)) T ∧
          IsGeoResolution (MarkedIdeal.pullback (Subtype.val : O→presentationOpen PHS) Q) T:=by
  obtain ⟨Ψ,hΨ0,_hΞsrc,_hΞ0,G0,S,PHS,hSpan,_hGerms,hw,hPrefix,hContact,_hJac,_hU,_hRef,
      V,η,haV,hη,hCov,hQ,hCos,hSing,hZero,hResolve⟩:=
    exists_original_initial_hs_phase W hW a ha E hE Φ hsrc hΦ0
  have hJ:=phase_normal_original_domain PHS (fun z=>(η z : X)) E hQ
  have hTrace:=phase_normal_zero_section_record PHS hw (fun z=>(η z : X)) E
  have hImage:=(phase_normal_cosupp PHS hw (fun z=>(η z : X)) E).trans
    (congrArg (Set.image (zeroSection (presentationOpen PHS))) hCos)
  have hZeroJ : zeroSection (presentationOpen PHS) (⟨0,PHS.zero_mem⟩ : presentationOpen PHS)∈
      (phaseNormalMarked PHS (fun z=>(η z : X)) E).cosupp:=
    (phase_normal_cosupp PHS hw (fun z=>(η z : X)) E).symm ▸
      mem_image_of_mem (zeroSection (presentationOpen PHS)) hZero
  exact ⟨Ψ,hΨ0,G0,S,PHS,hSpan,hw,hPrefix,hContact,V,η,haV,hη,hCov,
    hQ,hCos,hSing,hJ,hTrace,hImage,hZeroJ,
    (fun j=>phase_normal_zero_section_derivatives PHS hw (fun z=>(η z : X)) E j),hResolve⟩

end
end Hironaka.HironakaActualWeightedHSNormalInput
