import Hironaka.Resolution.HironakaActualWeightedHSNormalInput
import Hironaka.Resolution.HironakaActualHistoricalInitialNativePointWindow
import Hironaka.Resolution.HironakaActualHistoricalNativeOpenRestriction

/-! The RAW native order of the SAME actual initial weighted HS record.
Blueprint: hironaka-actual-weighted-hs-native-order-20261102.tex. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualWeightedHSNativeOrder
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
  HironakaActualWeightedHSNormalInput HironakaActualHistoricalInitialNativePointWindow
  HironakaActualHistoricalNativeOpenRestriction HironakaActualHistoricalNativeStageStep
  HironakaActualHistoricalNormalizedWeakPresentation HironakaActualFixedInheritedSelector
  HironakaActualGeometricCurrentNeighborhoodHS HironakaActualRelativeNormalJetDivision
  HironakaActualNormalZeroAnalyticSaturation HironakaActualFormalInitialDiagram
  HironakaActualHistoricalHSMarkedDomain HironakaActualOriginalInitialHSPhase
  HironakaActualWeightedCoefficientCompression HironakaActualCoherentWeightedCoefficientMarked
  HironakaHolomorphicJetRankLoci HironakaHolomorphicJetChartInvariance
  HironakaActualInheritedNeighborhoodMarkedHS HironakaSmoothSubmersionGermIdealColon
  HironakaRelativeNormalMonomialBasis HironakaActualCoefficientPresentationCentrePower
  GermIdealOrder IdealWeightPowers OrderTaylor OrderMultiplicativity CompanionReduction
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  ResolutionInvariantSpec NonmonomialOrderLocal HironakaSharpOriginalProductTraceOrder
  InvertibleIdealQuotient RelativePrincipalizationSpan BlowupTowers MonomialPartEtale
  HironakaSmoothCentreCoherentDomain HadamardBridge HironakaActualCauchyMonomialDivision
  HironakaActualOriginalFormalHSTransfer
  HironakaActualRelativeNormalWindowFactory HironakaActualOpenEmbeddingCanonicalExtension
  HironakaSmoothSubmersionOrderedChoiceImageTrace GermIdealPullbackCalculus InvDomainTowerAlong
  MarkedIdealRestrictOpen
  HironakaActualInheritedCurrentSourceRelabel HironakaActualInheritedNestedContactFlag
  HironakaActualHistoricalSortedPrefixFrames HironakaActualHistoricalWholeJetFrames
  HironakaActualInheritedSmallTails HironakaActualFiniteDegLexWeights
  HironakaActualWeightedVertexSmallTails HironakaActualOriginalScaledAnalyticDivision

/-- Actual original point powers pass through the TRUE inverse coordinates. -/
theorem adaptedGerm_point_power {n q : ℕ} {X : Type}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    (x : X) (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source⊆(chartAt (ComplexModel n) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0)
    (F : X→ℂ) (hF : HolomorphicAt n F x)
    (hPow : (idealPow (pointIdeal n x) q).mem x F) :
    adaptedGerm x Φ h0 F hF∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^q:=by
  let f:=actualFlatteningInverseMap x Φ
  let H:=F∘f
  have h0T : (0 : ComplexModel n)∈Φ.target:=by
    simpa only [h0] using Φ.mapsTo_toFun Φ.center_mem_source
  have hf : ∀ᶠz in 𝓝 (0 : ComplexModel n),MDifferentiableAt
      𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) f z:=
    eventually_of_mem (Φ.isOpen_target.mem_nhds h0T)
      (fun z hz=>actualFlatteningInverseMap_mdifferentiable x Φ hsrc z hz)
  have hf0 : f 0=x:=actualFlatteningInverseMap_zero x Φ h0
  have hSource : (idealPow (pointIdeal n (f 0)) q).mem (f 0) F:=hf0.symm ▸ hPow
  have hPull : (idealPow (pointIdeal n (0 : ComplexModel n)) q).mem 0 H:=
    comp_mem_idealPow_pointIdeal hf q hSource
  have hH : ∀ᶠz in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ H z:=
    (holomorphic_adapted_iff x Φ h0 F).mpr hF
  have hEq : translatedGerm 0 H hH=adaptedGerm x Φ h0 F hF:=by
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall (fun z=>by simp [H,f,actualFlatteningInverseMap])
  exact hEq ▸ (translatedGerm_mem_maximalIdeal_pow_iff_pointIdeal 0 H hH q).mpr hPull

private theorem adaptedGerm_pow {n : ℕ} {X : Type}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    (x : X) (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0)
    (F : X→ℂ) (hF : HolomorphicAt n F x) (j : ℕ) :
    adaptedGerm x Φ h0 (fun z=>F z^j) (holomorphicAt_pow_of hF j)=
      (adaptedGerm x Φ h0 F hF)^j:=by
  exact HolGerm.mk_pow _ ((holomorphic_adapted_iff x Φ h0 F).mpr hF) j

variable {n : ℕ} {I : Ideal (HolGerm (ComplexModel n))}
  {G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)}

private theorem phase_index_nonempty {B : GermIdeal n (ComplexModel n)} {R : ℕ→ℕ}
    (PHS : ActualGeometricInheritedNeighborhoodHS B I G R)
    {M : Type*} (η : presentationOpen PHS→M)
    (hQ : IsInvDomain n (initialWeightedRecord PHS η [])) :
    Nonempty (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)):=by
  by_contra hNo
  let x : presentationOpen PHS:=⟨0,PHS.zero_mem⟩
  obtain ⟨f,hf,hFreq⟩:=hQ.isNonzeroAlongAt x (mem_univ _)
  obtain ⟨_hhol,K,s,a,hs,_ha,hSum⟩:=hf
  apply hFreq
  filter_upwards [hSum] with y hy
  rintro ⟨_,hne⟩
  apply hne
  rw [hy]
  apply Finset.sum_eq_zero
  intro i _
  obtain ⟨v,_⟩:=hs i
  exact False.elim (hNo ⟨v⟩)

/-- At a TRUE actual native five-law point the original RAW order is M.
The initial E is literally empty; no external-boundary claim is made. -/
theorem actual_weighted_hs_native_order {B : GermIdeal n (ComplexModel n)} {R : ℕ→ℕ}
    (PHS : ActualGeometricInheritedNeighborhoodHS B I G R)
    {M : Type*} (η : presentationOpen PHS→M)
    (hQ : IsInvDomain n (initialWeightedRecord PHS η []))
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)))
    {k : ℕ} (a : Fin k ≃ actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I))
    (w : Fin k → CoordinateWord n) (hWords : ∀i,wordExponent (w i)=(a i).val)
    (W : Set (presentationOpen PHS)) (x : presentationOpen PHS)
    (hx : x∈(initialWeightedRecord PHS η []).cosupp)
    (hAt : ActualHistoricalNativePointPresentation S a w W (initialWeightedRecord PHS η []) x) :
    nmOrd (M:=CMfd.of (n:=n) (presentationOpen PHS)) (initialWeightedRecord PHS η []) x=
      weightedCommonMark (fun v : actualInitialVertices MonomialOrder.degLex
        (analyticZeroTaylorIdeal n I)=>normalExponentDegree v.val):=by
  let Q:=initialWeightedRecord PHS η []
  let μ:=fun v : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)=>normalExponentDegree v.val
  let d:=weightedCommonMark μ
  obtain ⟨Φ,hΦsrc,hΦ0,Γ,hFive,_hSpan,hCompression⟩:=hAt
  obtain ⟨v⟩:=phase_index_nonempty PHS η hQ
  let i:=a.symm v
  have hDegree : normalExponentDegree (wordExponent (w i))=μ v:=by
    rw [hWords]
    exact congrArg (fun z=>normalExponentDegree z.val) (a.apply_symm_apply v)
  obtain ⟨F,hF,hFΓ⟩:=exists_original_adapted_representative x Φ hΦ0 (Γ v)
  have hFnot : ¬(idealPow (pointIdeal n x) (μ v+1)).mem x F:=by
    intro h
    have hGerm:=adaptedGerm_point_power x Φ hΦsrc hΦ0 F hF h
    rw [hFΓ] at hGerm
    have hTaylor : actualUnshiftedTaylorAlgHom n (Γ v)∈genuineFormalVariables n^(μ v+1):=by
      rw [←map_actualUnshifted_maximal_pow n (μ v+1)]
      exact Ideal.mem_map_of_mem _ hGerm
    have hHigh:=(hFive.1 i).2
    rw [hDegree] at hHigh
    have hV : a i=v:=a.apply_symm_apply v
    rw [hV] at hHigh
    exact hHigh hTaylor
  let e:=d/μ v
  have hPowerNot:=pow_notMem_idealPow hF hFnot e
  have hNumber : e*μ v=d:=by
    exact (Nat.mul_comm e (μ v)).trans (weight_mul_compressionExponent μ v)
  rw [hNumber] at hPowerNot
  have hPow : adaptedGerm x Φ hΦ0 (fun y=>F y^e) (holomorphicAt_pow_of hF e)=(Γ v)^e:=
    (adaptedGerm_pow x Φ hΦ0 F hF e).trans (congrArg (fun g=>g^e) hFΓ)
  have hIn : (Γ v)^e∈adaptedIdeal Q.ideal x Φ hΦ0:=by
    rw [hCompression]
    exact Ideal.subset_span ⟨v,rfl⟩
  have hNativeMember : Q.ideal.mem x (fun y=>F y^e):=
    (mem_adaptedIdeal_iff Q.ideal hQ.isWellFormed.isCoherent x Φ hΦ0 _ (holomorphicAt_pow_of hF e)).mp
      (hPow.symm ▸ hIn)
  have hGe (j : ℕ) : ordGe (M:=CMfd.of (n:=n) (presentationOpen PHS)) Q j=
      cosupport n univ Q.ideal j:=by
    change ordGe (ordinaryTraceMarked (X:=CMfd.of (n:=n) (presentationOpen PHS)) univ Q.ideal) j=
      cosupport n univ Q.ideal j
    exact ordGe_ordinaryTraceMarked_eq_cosupport (X:=CMfd.of (n:=n) (presentationOpen PHS))
      univ Q.ideal hQ.isWellFormed.isCoherent j
  have hUpper : x∉ordGe (M:=CMfd.of (n:=n) (presentationOpen PHS)) Q (d+1):=by
    rw [hGe]
    intro h
    exact hPowerNot (mem_idealPow_of_vanishesToOrderOn_univ (h.2 _ hNativeMember))
  have hLower : d≤nmOrd (M:=CMfd.of (n:=n) (presentationOpen PHS)) Q x:=
    (mem_ordGe_iff (M:=CMfd.of (n:=n) (presentationOpen PHS)) hQ.isWellFormed hQ.isNonzeroAlongAt
      (mem_univ _) d).mp ((hGe d).symm ▸ hx)
  exact (nmOrd_le_of_notMem (M:=CMfd.of (n:=n) (presentationOpen PHS)) hUpper).antisymm hLower

private theorem presentation_functions_mdifferentiable {B : GermIdeal n (ComplexModel n)} {R : ℕ→ℕ}
    (PHS : ActualGeometricInheritedNeighborhoodHS B I G R) (i) :
    MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ)
      (fun z : presentationOpen PHS=>PHS.representatives i z.val):=by
  intro z
  have h:=holomorphicAt_of_mdifferentiableOn PHS.isOpen_neighborhood
    (mdifferentiableOn_iff_differentiableOn.mpr (PHS.holomorphicOn i)) z.property
  exact (h.comp_contMDiff (Eventually.of_forall fun _=>
    (contMDiff_subtype_val (U:=presentationOpen PHS)).contMDiffAt)).mdifferentiableAt

private theorem source_cosupp_native_profile (B : Set (ComplexModel n)) {R : ℕ→ℕ}
    (PHS : ActualGeometricInheritedNeighborhoodHS (vanishingIdeal (n:=n) B) I G R)
    (hw : ∀v : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I),
      0<normalExponentDegree v.val)
    {M : Type*} (η : presentationOpen PHS→M) (x : presentationOpen PHS)
    (hx : x∈(initialWeightedRecord PHS η []).cosupp) :
    ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n)
      ((Subtype.val : presentationOpen PHS→ComplexModel n) ⁻¹' B)) x ℓ=R ℓ:=by
  let U:=presentationOpen PHS
  let μ:=fun v : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)=>normalExponentDegree v.val
  let c:=fun i (z : U)=>PHS.representatives i z.val
  change x∈cosupport n univ (weightedFunctionIdeal μ c) (weightedCommonMark μ) at hx
  rw [cosupport_weightedFunctionIdeal μ hw c (presentation_functions_mdifferentiable PHS)] at hx
  have hProfile : ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) B) x.val ℓ=R ℓ:=by
    apply (PHS.wholeHS x.val x.property).mp
    intro i
    have hc : HolomorphicAt n (c i) x:=Eventually.of_forall (presentation_functions_mdifferentiable PHS i)
    have hOrder:=((mem_cosupport_finiteFunctionIdeal_iff (fun _ : Unit=>c i) x (μ i) (fun _=>hc)).mp
      ((mem_iInter.mp hx) i)) ()
    apply (translatedGerm_mem_maximalIdeal_pow_iff_pointIdeal x.val (PHS.representatives i)
      (PHS.holomorphicAt _ x.property i) (μ i)).mpr
    have hExtend:=mem_idealPow_pointIdeal_extendOpens U (μ i)
      (mem_idealPow_of_vanishesToOrderOn_univ hOrder)
    apply mem_idealPow_congr hExtend
    filter_upwards [U.isOpen.mem_nhds x.property] with z hz
    change extendOpens U (fun y : U=>PHS.representatives i y.val) (⟨z,hz⟩ : U).val=PHS.representatives i z
    rw [extendOpens_val]
  intro ℓ
  exact (HironakaActualVanishingIntrinsicHSTransport.hilbertSamuelAt_vanishing_actual_open_any U B x ℓ).trans (hProfile ℓ)

private theorem nativeOrder_open_embedding {d k : ℕ} {X Y : CMfd.{0} d} (hd : 0<d)
    (Q : MarkedIdeal d X) (hQ : IsInvDomain k Q) (b : Y→X)
    (hb : HironakaBaseChange.IsOpenHoloEmbedding d b) (y : Y) :
    nmOrd (MarkedIdeal.pullback b Q) y=nmOrd Q (b y):=by
  obtain ⟨O,Φ,hΦ⟩:=hb
  let D : MarkedIdeal d (CMfd.of (n:=d) O):=MarkedIdeal.pullback (Subtype.val : O→X) Q
  have hD : IsInvDomain k D:=isInvDomain_pullback_val O hQ
  have hbEq : b=Subtype.val∘Φ:=funext hΦ
  have hRecord : MarkedIdeal.pullback Φ D=MarkedIdeal.pullback b Q:=by
    dsimp only [D]
    rw [hbEq]
    exact MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl List.map_map
      (coherent_pullback_comp contMDiff_subtype_val Φ.contMDiff Q.ideal hQ.isWellFormed.isCoherent).symm rfl
  exact (congrArg (fun K : MarkedIdeal d Y=>nmOrd K y) hRecord).symm.trans
    ((nmOrd_pullback_diffeo hd Φ hD.isWellFormed hD.isNonzeroAlongAt y).trans
      ((nmOrd_pullback_val hd hQ.isWellFormed hQ.isNonzeroAlongAt O (Φ y)).trans
        (congrArg (nmOrd Q) (hΦ y).symm)))

private theorem maximal_of_orders {B : GermIdeal n (ComplexModel n)} {R : ℕ→ℕ}
    (PHS : ActualGeometricInheritedNeighborhoodHS B I G R)
    {M : Type*} (η : presentationOpen PHS→M)
    (hQ : IsInvDomain n (initialWeightedRecord PHS η []))
    (hOrder : ∀x∈(initialWeightedRecord PHS η []).cosupp,
      nmOrd (M:=CMfd.of (n:=n) (presentationOpen PHS)) (initialWeightedRecord PHS η []) x=
        (initialWeightedRecord PHS η []).d) :
    HomogenizedIdealAlong.IsMaximalOrderAlong (initialWeightedRecord PHS η []).N
      (initialWeightedRecord PHS η []).ideal (initialWeightedRecord PHS η []).d:=by
  let Q:=initialWeightedRecord PHS η []
  intro x hNext
  have hx : x∈Q.cosupp:=cosupport_anti (Nat.le_succ Q.d) hNext
  have hGe : ordGe (M:=CMfd.of (n:=n) (presentationOpen PHS)) Q (Q.d+1)=
      cosupport n univ Q.ideal (Q.d+1):=by
    change ordGe (ordinaryTraceMarked (X:=CMfd.of (n:=n) (presentationOpen PHS)) univ Q.ideal) (Q.d+1)=_
    exact ordGe_ordinaryTraceMarked_eq_cosupport (X:=CMfd.of (n:=n) (presentationOpen PHS))
      univ Q.ideal hQ.isWellFormed.isCoherent (Q.d+1)
  have hHigh : Q.d+1≤nmOrd (M:=CMfd.of (n:=n) (presentationOpen PHS)) Q x:=
    (mem_ordGe_iff (M:=CMfd.of (n:=n) (presentationOpen PHS)) hQ.isWellFormed hQ.isNonzeroAlongAt
      (mem_univ _) (Q.d+1)).mp (hGe.symm ▸ hNext)
  rw [hOrder x hx] at hHigh
  change Q.d+1≤Q.d at hHigh
  exact Nat.not_succ_le_self Q.d hHigh

/-- ONLY original source family/presentation/domain data internally select a
TRUE moving window with RAW order M and actual maximal order BEFORE CAN. -/
theorem exists_actual_weighted_hs_native_order_window
    (B : Set (ComplexModel n)) {R : ℕ→ℕ}
    (hSpan : Ideal.span (range G.germs)=I)
    (PHS : ActualGeometricInheritedNeighborhoodHS (vanishingIdeal (n:=n) B) I G R)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)))
    (hRed : ∀r,ActualInheritedPrefixReducedAt G r)
    (hContact : ∀r,actualFixedSelectorContactAt S G.germs r)
    (hw : ∀v : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I),
      0<normalExponentDegree v.val)
    {M : Type*} (η : presentationOpen PHS→M)
    (hQ : IsInvDomain n (initialWeightedRecord PHS η [])) :
    ∃(A : Opens (ComplexModel n)) (hA : A≤presentationOpen PHS) (h0A : (0 : ComplexModel n)∈A),
      let Pa:=restrictedPresentation PHS A hA h0A
      let ηa:=η∘baseInclusion hA
      let Qa:=initialWeightedRecord Pa ηa []
      IsInvDomain n Qa ∧
      (∀x∈Qa.cosupp,nmOrd (M:=CMfd.of (n:=n) A) Qa x=
        weightedCommonMark (fun v : actualInitialVertices MonomialOrder.degLex
          (analyticZeroTaylorIdeal n I)=>normalExponentDegree v.val)) ∧
      HomogenizedIdealAlong.IsMaximalOrderAlong Qa.N Qa.ideal Qa.d:=by
  obtain ⟨P,s,hs0,_hs,δ,hBound,_hδ,hOpen,hZero,hSubset,hWords,_hOwner,hPoints⟩:=
    exists_actual_initial_native_point_window B hSpan PHS S hRed hContact η []
  let A : Opens (ComplexModel n):=⟨historicalNativeJetWindow P s hs0 δ,hOpen⟩
  have hA : A≤presentationOpen PHS:=hSubset
  have h0A : (0 : ComplexModel n)∈A:=hZero
  let Pa:=restrictedPresentation PHS A hA h0A
  let ηa:=η∘baseInclusion hA
  let Qa:=initialWeightedRecord Pa ηa []
  let Q:=initialWeightedRecord PHS η []
  have hQa : IsInvDomain n Qa:=restricted_phase_original_domain PHS A hA h0A η [] hQ
  have hb : HironakaBaseChange.IsOpenHoloEmbedding n (baseInclusion hA):=
    ⟨MaxLocusLocal.nestedOpens (presentationOpen PHS) A,
      (MaxLocusLocal.nestedOpensDiffeo (n:=n) hA).symm,fun _=>rfl⟩
  have hRecord : Qa=MarkedIdeal.pullback (baseInclusion hA) Q:=
    restricted_phase_entire_record PHS A hA h0A η []
  have hCos:=cosupp_pullback_of_isOpenHoloEmbedding (X:=CMfd.of (n:=n) (presentationOpen PHS))
    (Y:=CMfd.of (n:=n) A) (baseInclusion hA) hb Q hQ.isWellFormed
  have hOrders : ∀x∈Qa.cosupp,nmOrd (M:=CMfd.of (n:=n) A) Qa x=
      weightedCommonMark (fun v : actualInitialVertices MonomialOrder.degLex
        (analyticZeroTaylorIdeal n I)=>normalExponentDegree v.val):=by
    intro x hx
    by_cases hn : 0<n
    · have hPull : x∈(MarkedIdeal.pullback (baseInclusion hA) Q).cosupp:=
        (congrArg (fun K : MarkedIdeal n (CMfd.of (n:=n) A)=>K.cosupp) hRecord) ▸ hx
      have hxQ : baseInclusion hA x∈Q.cosupp:=(Set.ext_iff.mp hCos x).mp hPull
      have hProfile:=source_cosupp_native_profile B PHS hw η (baseInclusion hA x) hxQ
      have hAt:=hPoints (baseInclusion hA x) x.property hProfile
      have hOldOrder:=actual_weighted_hs_native_order PHS η hQ S _ _ hWords
        ((Subtype.val : presentationOpen PHS→ComplexModel n) ⁻¹' B) (baseInclusion hA x) hxQ hAt
      exact (congrArg (fun K : MarkedIdeal n (CMfd.of (n:=n) A)=>nmOrd K x) hRecord).trans
        ((nativeOrder_open_embedding (X:=CMfd.of (n:=n) (presentationOpen PHS)) (Y:=CMfd.of (n:=n) A)
          hn Q hQ (baseInclusion hA) hb x).trans hOldOrder)
    · have hn0 : n=0:=by omega
      have hZeroDomain : IsInvDomain 0 Qa:=
        (congrArg (fun k : ℕ=>IsInvDomain k Qa) hn0) ▸ hQa
      have hEmpty:=cosupp_eq_empty_of_dimLE_zero hZeroDomain
      rw [hEmpty] at hx
      exact False.elim hx
  exact ⟨A,hA,h0A,hQa,hOrders,maximal_of_orders Pa ηa hQa hOrders⟩

end
end Hironaka.HironakaActualWeightedHSNativeOrder
