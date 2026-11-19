import Hironaka.Resolution.HironakaG1OriginalWeightedInitialization
import Hironaka.Resolution.HironakaActualHistoricalNativeOrdinaryOrder
import Hironaka.Resolution.HironakaActualCommonMarkPersistentCosupport
import Hironaka.Resolution.HironakaActualInvertibleIntrinsicHS

/-! Maximal order of the SAME original HS weighted record on its WHOLE PHS open.
Blueprint FIRST: hironaka-g1-original-weighted-maximal-order.tex.
No shrinking, deleted boundary, native five-law or desired-order packet. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1OriginalWeightedMaximalOrder
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
  RelativePrincipalizationSpan InvertibleIdealQuotient GermIdealPullbackCalculus
  IdealWeightPowers IdealOrderArithmetic GermIdealOrder OrderTaylor OrderMultiplicativity
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealOperationsAlong HomogenizedIdealAlong
  ResolutionInvariantSpec HironakaActualRelativeNormalJetDivision HironakaActualFormalInitialDiagram
  HironakaActualNormalZeroAnalyticSaturation HironakaRelativeNormalMonomialBasis
  HironakaActualOriginalFormalHSTransfer HironakaActualGeometricCurrentNeighborhoodHS
  HironakaActualHistoricalHSMarkedDomain HironakaActualOriginalInitialHSPhase
  HironakaActualHistoricalNativeOrdinaryOrder HironakaG1OriginalWeightedInitialization
  HironakaActualCoherentWeightedCoefficientMarked HironakaActualWeightedCoefficientCompression
  HironakaHolomorphicJetRankLoci HironakaHolomorphicJetChartInvariance HironakaHolomorphicPointJets
  HironakaActualCoefficientPresentationCentrePower
  HironakaActualInheritedNeighborhoodMarkedHS HironakaActualCauchyCoefficientLimits
  HironakaActualVanishingIntrinsicHSTransport HironakaActualCommonMarkPersistentCosupport
  HironakaActualInvertibleIntrinsicHS MarkedIdealRestrictOpen HadamardBridge

variable {n : ℕ} {W : Set (ComplexModel n)} {I : Ideal (HolGerm (ComplexModel n))}
  {G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)} {R : ℕ→ℕ}

private theorem native_generator_orders
    (P : ActualGeometricInheritedNeighborhoodHS (vanishingIdeal (n:=n) W) I G R)
    (hw : ∀i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I),
      0<normalExponentDegree i.val)
    {M : Type*} (η : presentationOpen P→M) (E : List (Set M))
    (x : presentationOpen P) (hx : x∈(initialWeightedRecord P η E).cosupp) :
    ∀i,(idealPow (pointIdeal n x) (normalExponentDegree i.val)).mem x
      (fun y : presentationOpen P=>P.representatives i y.val) := by
  let μ:=fun i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)=>normalExponentDegree i.val
  let c:=fun i (y : presentationOpen P)=>P.representatives i y.val
  change x∈cosupport n univ (weightedFunctionIdeal μ c) (weightedCommonMark μ) at hx
  rw [cosupport_weightedFunctionIdeal μ hw c (presentation_functions_holomorphic P)] at hx
  intro i
  have hi:=((mem_cosupport_finiteFunctionIdeal_iff (fun _ : Unit=>c i) x (μ i)
    (fun _=>Eventually.of_forall (presentation_functions_holomorphic P i))).mp ((mem_iInter.mp hx) i)) ()
  exact mem_idealPow_of_vanishesToOrderOn_univ hi

private theorem native_power_to_translated
    (P : ActualGeometricInheritedNeighborhoodHS (vanishingIdeal (n:=n) W) I G R)
    (i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I))
    (x : presentationOpen P) (q : ℕ)
    (hPow : (idealPow (pointIdeal n x) q).mem x (fun y : presentationOpen P=>P.representatives i y.val)) :
    translatedGerm x.val (P.representatives i) (P.holomorphicAt x.val x.property i)∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^q := by
  apply (translatedGerm_mem_maximalIdeal_pow_iff_pointIdeal x.val (P.representatives i)
    (P.holomorphicAt x.val x.property i) q).mpr
  have hExt:=mem_idealPow_pointIdeal_extendOpens (presentationOpen P) q hPow
  apply mem_idealPow_congr hExt
  filter_upwards [P.isOpen_neighborhood.mem_nhds x.property] with y hy
  change extendOpens (presentationOpen P) (fun z=>P.representatives i z.val) (⟨y,hy⟩ : presentationOpen P).val=
    P.representatives i y
  exact extendOpens_val _ _ _

private theorem native_whole_hs_eq
    (P : ActualGeometricInheritedNeighborhoodHS (vanishingIdeal (n:=n) W) I G R)
    (hw : ∀i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I),
      0<normalExponentDegree i.val)
    (hRef : ∀ℓ,hilbertSamuelValue I ℓ=R ℓ)
    {M : Type*} (η : presentationOpen P→M) (E : List (Set M))
    (x : presentationOpen P) (hx : x∈(initialWeightedRecord P η E).cosupp) :
    ∀ℓ,hilbertSamuelValue
      (wholeChartStalkIdeal (vanishingIdeal (n:=n) ((Subtype.val : presentationOpen P→ComplexModel n) ⁻¹' W))
        x x (mem_chart_source _ x)) ℓ=hilbertSamuelValue I ℓ := by
  have hOrders:=native_generator_orders P hw η E x hx
  have hHS:=(P.wholeHS x.val x.property).mp (fun i=>native_power_to_translated P i x _ (hOrders i))
  intro ℓ
  exact ((hilbertSamuelAt_vanishing_actual_open_any (presentationOpen P) W x ℓ).trans
    (hHS ℓ)).trans (hRef ℓ).symm

/-- A literal MINIMAL-degree original representative has exact order on the WHOLE actual cosupport. -/
theorem initialWeightedRecord_exact_minimal_generator {k : ℕ}
    (P : ActualGeometricInheritedNeighborhoodHS (vanishingIdeal (n:=n) W) I G R)
    (hSpan : Ideal.span (range G.germs)=I) (hRef : ∀ℓ,hilbertSamuelValue I ℓ=R ℓ)
    (hw : ∀i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I),
      0<normalExponentDegree i.val)
    {M : Type*} (η : presentationOpen P→M) (E : List (Set M))
    (hQ : IsInvDomain k (initialWeightedRecord P η E))
    (x : presentationOpen P) (hx : x∈(initialWeightedRecord P η E).cosupp) :
    ∃i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I),
      (∀j : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I),
        normalExponentDegree i.val≤normalExponentDegree j.val) ∧
      (idealPow (pointIdeal n x) (normalExponentDegree i.val)).mem x
        (fun y : presentationOpen P=>P.representatives i y.val) ∧
      ¬(idealPow (pointIdeal n x) (normalExponentDegree i.val+1)).mem x
        (fun y : presentationOpen P=>P.representatives i y.val) := by
  let μ:=fun i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)=>normalExponentDegree i.val
  let c:=fun i (y : presentationOpen P)=>P.representatives i y.val
  obtain ⟨v⟩:=initial_phase_labels_nonempty P η E hQ
  have hExists : ∃m : ℕ,∃i,μ i=m:=⟨μ v,v,rfl⟩
  let m:=Nat.find hExists
  obtain ⟨v₀,hv₀⟩:=Nat.find_spec hExists
  have hMin (j) : m≤μ j:=Nat.find_min' hExists ⟨j,rfl⟩
  have hInot : ¬I≤IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^(m+1) := by
    intro hI
    have hG : G.germs v₀∈Ideal.span (range G.germs):=Ideal.subset_span ⟨v₀,rfl⟩
    rw [hSpan] at hG
    have hFormal : actualUnshiftedTaylorAlgHom n (G.germs v₀)∈genuineFormalVariables n^(m+1) := by
      rw [←map_actualUnshifted_maximal_pow n (m+1)]
      exact Ideal.mem_map_of_mem _ (hI hG)
    have hZero:=(mem_genuineFormalVariables_pow_iff_coefficients_zero n (m+1) _).mp hFormal
      v₀.val (by change μ v₀<m+1; omega)
    exact one_ne_zero ((G.monic v₀).symm.trans hZero)
  let A:=vanishingIdeal (n:=n) ((Subtype.val : presentationOpen P→ComplexModel n) ⁻¹' W)
  let J:=wholeChartStalkIdeal A x x (mem_chart_source _ x)
  have hJnot : ¬J≤IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^(m+1) := by
    intro hJ
    exact hInot ((le_maximal_pow_iff_of_entire_hs_eq J I (native_whole_hs_eq P hw hRef η E x hx) (m+1)).mp hJ)
  have hSome : ∃j,¬(idealPow (pointIdeal n x) (m+1)).mem x (c j) := by
    by_contra! hAll
    apply hJnot
    apply (wholeChartStalkIdeal_le_maximal_pow_iff A x (fun _ hf=>hf.1) (m+1)).mpr
    intro F hF
    apply IsInSpanAt.vanishesToOrderOn ((presentation_vanishing_generators P x F).mp hF)
    rintro f ⟨j,rfl⟩
    exact ⟨c j,hAll j,Eventually.of_forall fun _ _=>rfl⟩
  obtain ⟨j,hj⟩:=hSome
  have hOrders:=native_generator_orders P hw η E x hx
  have hjm : μ j=m := by
    by_contra hne
    have hle : m+1≤μ j:=by have:=hMin j; omega
    exact hj (idealPow_le_of_le (fun _ _ hg=>holomorphicAt_of_mem_pointIdeal hg) hle x (c j) (hOrders j))
  refine ⟨j,?_,hOrders j,?_⟩
  · intro i
    change μ j≤μ i
    rw [hjm]
    exact hMin i
  · change ¬(idealPow (pointIdeal n x) (μ j+1)).mem x (c j)
    rwa [hjm]

/-- An ACTUAL literal compressed generator in Q has the TRUE common mark as exact order. -/
theorem initialWeightedRecord_exact_compression_generator {k : ℕ}
    (P : ActualGeometricInheritedNeighborhoodHS (vanishingIdeal (n:=n) W) I G R)
    (hSpan : Ideal.span (range G.germs)=I) (hRef : ∀ℓ,hilbertSamuelValue I ℓ=R ℓ)
    (hw : ∀i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I),
      0<normalExponentDegree i.val)
    {M : Type*} (η : presentationOpen P→M) (E : List (Set M))
    (hQ : IsInvDomain k (initialWeightedRecord P η E))
    (x : presentationOpen P) (hx : x∈(initialWeightedRecord P η E).cosupp) :
    let Q:=initialWeightedRecord P η E
    ∃i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I),
      let f : presentationOpen P→ℂ:=fun y=>P.representatives i y.val^(Q.d/normalExponentDegree i.val)
      Q.ideal.mem x f ∧ (idealPow (pointIdeal n x) Q.d).mem x f ∧
        ¬(idealPow (pointIdeal n x) (Q.d+1)).mem x f := by
  let Q:=initialWeightedRecord P η E
  let μ:=fun i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)=>normalExponentDegree i.val
  let c:=fun i (y : presentationOpen P)=>P.representatives i y.val
  obtain ⟨i,_hMin,_hLow,hNot⟩:=initialWeightedRecord_exact_minimal_generator P hSpan hRef hw η E hQ x hx
  have hc : HolomorphicAt n (c i) x:=Eventually.of_forall (presentation_functions_holomorphic P i)
  have hm : (Q.d/μ i)*μ i=Q.d:=(Nat.mul_comm _ _).trans (weight_mul_compressionExponent μ i)
  have hHigh:=CompanionReduction.pow_notMem_idealPow hc hNot (Q.d/μ i)
  rw [hm] at hHigh
  have hMem : Q.ideal.mem x (fun y=>c i y^(Q.d/μ i)):=
    isInSpanAt_self ⟨i,rfl⟩ (CompanionReduction.holomorphicAt_pow_of hc _)
  exact ⟨i,hMem,mem_idealPow_of_vanishesToOrderOn_univ (hx.2 _ hMem),hHigh⟩

/-- THIS unchanged original full-boundary HS Q is maximal-order on its ENTIRE existing PHS window. -/
theorem initialWeightedRecord_maximalOrder {k : ℕ}
    (P : ActualGeometricInheritedNeighborhoodHS (vanishingIdeal (n:=n) W) I G R)
    (hSpan : Ideal.span (range G.germs)=I) (hRef : ∀ℓ,hilbertSamuelValue I ℓ=R ℓ)
    (hw : ∀i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I),
      0<normalExponentDegree i.val)
    {M : Type*} (η : presentationOpen P→M) (E : List (Set M))
    (hQ : IsInvDomain k (initialWeightedRecord P η E)) :
    IsMaximalOrderAlong (initialWeightedRecord P η E).N
      (initialWeightedRecord P η E).ideal (initialWeightedRecord P η E).d := by
  let Q:=initialWeightedRecord P η E
  intro x hNext
  have hx : x∈Q.cosupp:=cosupport_anti (Nat.le_succ Q.d) hNext
  obtain ⟨i,hMem,_hLow,hNot⟩:=initialWeightedRecord_exact_compression_generator P hSpan hRef hw η E hQ x hx
  exact hNot (mem_idealPow_of_vanishesToOrderOn_univ (hNext.2 _ hMem))

/-- Exact ORDINARY ideal order; no nonmonomial or alternate evaluator is substituted. -/
theorem initialWeightedRecord_ordinary_order {k : ℕ}
    (P : ActualGeometricInheritedNeighborhoodHS (vanishingIdeal (n:=n) W) I G R)
    (hSpan : Ideal.span (range G.germs)=I) (hRef : ∀ℓ,hilbertSamuelValue I ℓ=R ℓ)
    (hw : ∀i : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I),
      0<normalExponentDegree i.val)
    {M : Type*} (η : presentationOpen P→M) (E : List (Set M))
    (hQ : IsInvDomain k (initialWeightedRecord P η E))
    (x : presentationOpen P) (hx : x∈(initialWeightedRecord P η E).cosupp) :
    let Q:=initialWeightedRecord P η E
    order n Q.N Q.ideal x=(Q.d : ℕ∞) := by
  let Q:=initialWeightedRecord P η E
  have hMax:=initialWeightedRecord_maximalOrder P hSpan hRef hw η E hQ
  apply le_antisymm
  · apply iSup₂_le
    intro q hq
    have hqd : q≤Q.d := by
      by_contra hgt
      exact hMax x (cosupport_anti (by omega : Q.d+1≤q) ⟨mem_univ x,hq⟩)
    exact_mod_cast hqd
  · exact (le_order_iff (fun _ hf=>GermIdeal.IsCoherent.holomorphicAt_mem hQ.isWellFormed.isCoherent hf)).mpr hx.2

end
end Hironaka.HironakaG1OriginalWeightedMaximalOrder
