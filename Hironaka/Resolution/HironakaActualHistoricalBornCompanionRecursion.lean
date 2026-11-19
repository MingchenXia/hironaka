import Hironaka.Resolution.HironakaActualHistoricalOriginalNativePhase
import Hironaka.Resolution.HironakaActualNativeBornWeightedExponents
import Hironaka.Resolution.HironakaActualHistoricalNativeOrdinaryOrder

/-! Genuine born-boundary companion recursion on the SAME actual weighted
HS history. Empty INITIAL boundary is essential, but insufficient without
the actual native HS/singular-centre geometry used below. No normal-padding
history or general G1 closure is asserted. Blueprint precedes this source. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualHistoricalBornCompanionRecursion
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
  HironakaEmbeddedAnalytic HironakaActualCoherentWeightedCoefficientMarked
  HironakaActualHistoricalOriginalNativePhase HironakaActualNativeBornWeightedExponents
  HironakaActualHistoricalNativeOrdinaryOrder HironakaActualHistoricalNativeGivenTower
  HironakaActualHistoricalNativeStageStep HironakaActualFixedInheritedSelector
  HironakaActualWeightedCoefficientCompression HironakaActualCoefficientPresentationCentrePower
  HironakaRelativeNormalMonomialBasis HironakaActualCauchyMonomialDivision
  HironakaActualHistoricalNativeFunctionTower HironakaActualHistoricalNativeFunctionSuccessor
  HironakaActualHistoricalSortedPrefixFrames HironakaActualHistoricalWholeJetFrames
  HironakaActualHistoricalPrefixJetFrames HironakaActualGeometricCurrentNeighborhoodHS
  HironakaActualRelativeNormalJetDivision HironakaActualInheritedNestedContactFlag
  HironakaActualNormalZeroAnalyticSaturation HironakaActualFormalInitialDiagram
  HironakaActualInheritedSmallTails HironakaActualWeightedVertexSmallTails
  HironakaActualFiniteDegLexWeights HironakaActualOriginalInitialHSPhase
  HironakaActualHistoricalHSMarkedDomain HironakaActualPrescribedCentreRebasing
  HironakaActualFixedFlatteningHSComparison HironakaSmoothCentreCoherentDomain
  HironakaRelativeNormalDeformationInitialRelations HironakaHolomorphicJetChartInvariance
  HironakaSmoothSubmersionGermIdealColon HironakaActualOriginalFormalHSTransfer
  HironakaActualOriginalScaledAnalyticDivision
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec
  MonomialPartAlong DivisorExponentAlong IdealWeightPowers RelativePrincipalizationSpan
  RestrictedIdealExtension RestrictedIdealQuotient InvertibleIdealQuotient
  CompanionRebase CompanionReductionAlong NonmonomialOrderLocal GermIdealOrder
  HironakaSharpOriginalProductTraceOrder HironakaStageCenters NormalCrossings
  InvDomainTowerAlong MarkedIdealRestrictOpen GermIdealTotalTransform

variable {n : ℕ} {X : CMfd.{0} n}

private theorem nonmonomial_mem_iff_of_one (I : GermIdeal n X) (hI : I.IsCoherent)
    (E : List (Set X)) (x : X)
    (h1 : (monomialPartAlong n univ I E).mem x (fun _=>1)) (g : X→ℂ) :
    (nonmonomialPartAlong n univ I E).mem x g ↔ I.mem x g := by
  constructor
  · intro hg
    have h := hg.2 (fun _=>1) h1
    obtain ⟨k,s,a,hs,ha,heq⟩ := h.2
    apply mem_of_isInSpanAt_mem hI
    refine ⟨hg.1,k,s,a,hs,ha,?_⟩
    filter_upwards [heq] with y hy
    simpa only [one_mul] using hy (mem_univ y)
  · intro hg
    exact ⟨GermIdeal.IsCoherent.holomorphicAt_mem hI hg,
      fun a ha=>restrictOn_mul_left ha.1 (le_restrictOn hI x g hg)⟩

private theorem monomial_one_of_zero_exponents (Q : MarkedIdeal n X)
    (x : X) (hzero : ∀i : Fin Q.E.length,divExpAlong n univ Q.ideal (Q.E.get i) x=0) :
    (monomialPartAlong n univ Q.ideal Q.E).mem x (fun _=>1) := by
  refine ⟨holomorphicAt_const 1,fun i _ _=>?_⟩
  rw [hzero i,idealPow_zero]
  exact IsInSpanAt.restrict (isInSpanAt_self (holomorphicAt_const 1) (holomorphicAt_const 1))

/-- Genuine whole native companion on a derived open, with every boundary
position and the unchanged original mark. -/
theorem exists_companion_window_of_zero_exponents (hn : 0<n)
    (Q : MarkedIdeal n X) (hQ : IsInvDomain n Q) (hN : Q.N=univ)
    (x : X) (O : Opens X) (hxO : x∈O)
    (hzero : ∀i : Fin Q.E.length,divExpAlong n univ Q.ideal (Q.E.get i) x=0) :
    ∃U : Opens X,x∈U ∧ (U : Set X)⊆O ∧
      MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U→X) (companionOf n Q Q.d)=
        MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U→X) Q ∧
      companionOf n (M:=CMfd.of (n:=n) U)
        (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U→X) Q) Q.d=
        MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U→X) Q := by
  have hNreg : IsClosedSubmanifold n (univ : Set X) := hN ▸ hQ.isWellFormed.isClosedSubmanifold_N
  have hTrans : IsTransverse n (univ : Set X) Q.E := hN ▸ hQ.isWellFormed.isTransverse
  have hNZ : ∀y∈(univ : Set X),IsNonzeroAlongAt univ Q.ideal y := hN ▸ hQ.isNonzeroAlongAt
  have hevent (i : Fin Q.E.length) : ∀ᶠy in 𝓝 x,y∈Q.E.get i →
      divExpAlong n univ Q.ideal (Q.E.get i) y=0 := by
    by_cases hi : x∈Q.E.get i
    · filter_upwards [eventually_divExpAlong_get_eq hn hNreg hQ.isWellFormed.isSNCDivisor
        hTrans hQ.isWellFormed.isCoherent hNZ i (mem_univ x) hi] with y hy hyE
      exact (hy (mem_univ y) hyE).trans (hzero i)
    · have hclosed := (MonomialPart.isClosedSubmanifold_get hn hQ.isWellFormed.isSNCDivisor i).1
      filter_upwards [hclosed.isOpen_compl.mem_nhds hi] with y hy hyE
      exact False.elim (hy hyE)
  obtain ⟨Uset,hUsub,hUopen,hxU⟩ := mem_nhds_iff.mp
    ((eventually_all.mpr hevent).and (O.isOpen.mem_nhds hxO))
  let U : Opens X := ⟨Uset,hUopen⟩
  have hstalk (y : X) (hy : y∈U) (g : X→ℂ) :
      (nonmonomialPartAlong n univ Q.ideal Q.E).mem y g ↔ Q.ideal.mem y g := by
    apply nonmonomial_mem_iff_of_one Q.ideal hQ.isWellFormed.isCoherent Q.E y
    refine ⟨holomorphicAt_const 1,fun i _ hi=>?_⟩
    rw [(hUsub hy).1 i hi,idealPow_zero]
    exact IsInSpanAt.restrict (isInSpanAt_self (holomorphicAt_const 1) (holomorphicAt_const 1))
  have hComp : companionOf n Q Q.d=⟨Q.N,Q.E,nonmonomialPartAlong n Q.N Q.ideal Q.E,Q.d⟩ := by
    simp only [companionOf,companionAlong,lt_self_iff_false,if_false]
  have hrec : MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U→X)
      (companionOf n Q Q.d)=MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U→X) Q := by
    rw [hComp]
    refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of
      (𝔪:=MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U→X)
        (⟨Q.N,Q.E,nonmonomialPartAlong n Q.N Q.ideal Q.E,Q.d⟩ : MarkedIdeal n X))
      (𝔫:=MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U→X) Q) rfl rfl ?_ rfl
    rw [hN]
    ext y g
    constructor
    · intro hg
      apply GermIdeal.mem_pullback_iff.mpr
      refine IsInSpanAt.mono ?_ (GermIdeal.mem_pullback_iff.mp hg)
      rintro s ⟨a,ha,rfl⟩
      exact ⟨a,(hstalk y.val y.property a).mp ha,rfl⟩
    · intro hg
      apply GermIdeal.mem_pullback_iff.mpr
      refine IsInSpanAt.mono ?_ (GermIdeal.mem_pullback_iff.mp hg)
      rintro s ⟨a,ha,rfl⟩
      exact ⟨a,(hstalk y.val y.property a).mpr ha,rfl⟩
  refine ⟨U,hxU,(fun _ hy=>(hUsub hy).2),hrec,?_⟩
  rw [← pullback_val_companionOf hn hQ.isWellFormed hQ.isNonzeroAlongAt U Q.d]
  exact hrec

private theorem stageCentres_of_native_centres (W : Set X) :
    ∀{Y : CMfd.{0} n}(T : BlowupTower X Y),ActualHistoricalNativeTowerCentres W T →
      StageCentres (fun P C=>C⊆HironakaEmbeddedAnalytic.singularSet (n:=n)
        (strictTransform n P.proj W)) T
  | _,.refl,_=>trivial
  | _,.step T _ _ _,h=>⟨stageCentres_of_native_centres W T h.1,h.2⟩

/-- Derived full companion recursion at a point of EVERY GIVEN true
weighted HS history. Empty initial E is not a replacement for these actual
HS/singular-centre premises. -/
theorem actual_native_history_companion_window
    {m : ℕ} {Xref : Type} [TopologicalSpace Xref]
    [ChartedSpace (ComplexModel m) Xref] [IsComplexManifold m Xref]
    (hn : 0<n) (Wref : Set Xref) (hWref : IsComplexAnalyticSubset (n:=m) Wref)
    (aref : Xref) (hSing : aref∈HironakaEmbeddedAnalytic.singularSet (n:=m) Wref)
    (W : Set X) (hW : IsComplexAnalyticSubset (n:=n) W)
    (Q : MarkedIdeal n X) (hQ : IsInvDomain n Q) (hQN : Q.N=univ) (hQE : Q.E=[])
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (hV : V.Nonempty) {k : ℕ} (a : Fin k ≃ V) (w : Fin k→CoordinateWord n)
    (hWords : ∀i,wordExponent (w i)=(a i).val)
    (hPositive : ∀v : V,0<normalExponentDegree v.val)
    (hOwn : ∀i,historicalOwner w (wordExponent (w i))=some i)
    (hQMark : Q.d=weightedCommonMark (fun v : V=>normalExponentDegree v.val))
    (hCut : Q.cosupp={x | ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) W) x ℓ=
      hilbertSamuelAt (vanishingIdeal (n:=m) Wref) aref ℓ})
    (hUpper : ∀x ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) W) x ℓ≤
      hilbertSamuelAt (vanishingIdeal (n:=m) Wref) aref ℓ)
    (hAt : ∀x∈Q.cosupp,ActualHistoricalNativePointPresentation S a w W Q x)
    {Y : CMfd.{0} n} (T : BlowupTower X Y) (hT : IsGeoTestTower Q T) :
    ActualHistoricalNativeTowerCentres W T ∧
      (geoTransformAlong Q T).cosupp={z | ∀ℓ,
        hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n T.proj W)) z ℓ=
          hilbertSamuelAt (vanishingIdeal (n:=m) Wref) aref ℓ} ∧
      ∀x∈(geoTransformAlong Q T).cosupp,
        nmOrd (geoTransformAlong Q T) x=Q.d ∧
        ∃U : Opens Y,x∈U ∧
          (U : Set Y)⊆NonmonomialOrderTail.ordMask (geoTransformAlong Q T) Q.d ∧
          MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U→Y)
            (companionOf n (geoTransformAlong Q T) Q.d)=
            MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U→Y) (geoTransformAlong Q T) ∧
          companionOf n (M:=CMfd.of (n:=n) U)
            (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U→Y) (geoTransformAlong Q T)) Q.d=
            MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U→Y) (geoTransformAlong Q T) ∧
          let Q' := MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U→Y) (geoTransformAlong Q T)
          ∀(Z : CMfd.{0} n)(P : BlowupTower (CMfd.of (n:=n) U) Z),
            (∀z,(CanonicalCentres.canonicalInvariant n).inv (companionOf n Q' Q.d) P z=
              (CanonicalCentres.canonicalInvariant n).inv Q' P z) ∧
            (IsCanonical (companionOf n Q' Q.d)
                ((CanonicalCentres.canonicalInvariant n).inv (companionOf n Q' Q.d)) P ↔
              IsCanonical Q' ((CanonicalCentres.canonicalInvariant n).inv Q') P) ∧
            ResolutionDriver.maxLocus ((CanonicalCentres.canonicalInvariant n).inv (companionOf n Q' Q.d) P)
              (geoTransformAlong (companionOf n Q' Q.d) P).cosupp=
              ResolutionDriver.maxLocus ((CanonicalCentres.canonicalInvariant n).inv Q' P)
                (geoTransformAlong Q' P).cosupp := by
  obtain ⟨⟨_hWT,hNT,hIT,hMarkT,_hUpperT,hCutT,hAtT,_hSingT⟩,hCentres⟩ :=
    actual_native_given_test_tower_state Wref hWref aref hSing W hW Q hQN
      hQ.isWellFormed.isCoherent S a w hWords hPositive hOwn hQMark hCut hUpper hAt T hT
  have hDomT := isInvDomain_geoTransformAlong hQ T hT
  have hStage := stageCentres_of_native_centres W T hCentres
  refine ⟨hCentres,hCutT,?_⟩
  intro x hx
  have hzero (i : Fin (geoTransformAlong Q T).E.length) :
      divExpAlong n univ (geoTransformAlong Q T).ideal ((geoTransformAlong Q T).E.get i) x=0 := by
    apply actual_native_born_weighted_exponent_zero Q W hW T hStage hIT
      hDomT.isWellFormed.isSNCDivisor S a w hPositive x
      (hNT ▸ hDomT.isNonzeroAlongAt x (hNT.symm ▸ mem_univ x)) (hAtT x hx)
    simpa only [hQE,List.length_nil,List.drop_zero] using (List.get_mem (geoTransformAlong Q T).E i)
  have h1 := monomial_one_of_zero_exponents (geoTransformAlong Q T) x hzero
  have hStalk := nonmonomial_mem_iff_of_one (geoTransformAlong Q T).ideal hIT
    (geoTransformAlong Q T).E x h1
  have hOrd : nmOrd (geoTransformAlong Q T) x=
      ordinaryTraceOrder (X:=Y) univ (geoTransformAlong Q T).ideal x := by
    apply nmOrd_congr
    intro j
    rw [ordGe_ordinaryTraceMarked_eq_cosupport univ _ hIT]
    change (x∈(geoTransformAlong Q T).N ∧
      ∀g,(nonmonomialPartAlong n (geoTransformAlong Q T).N (geoTransformAlong Q T).ideal
        (geoTransformAlong Q T).E).mem x g → VanishesToOrderOn n (geoTransformAlong Q T).N x j g) ↔ _
    rw [hNT]
    constructor
    · intro h
      exact ⟨h.1,fun g hg=>h.2 g ((hStalk g).mpr hg)⟩
    · intro h
      exact ⟨h.1,fun g hg=>h.2 g ((hStalk g).mp hg)⟩
  have hRaw := (actual_native_point_ordinary_order S hV a w hWords
    (strictTransform n T.proj W) (geoTransformAlong Q T) hNT hIT hMarkT x hx (hAtT x hx)).1
  have hOrder : nmOrd (geoTransformAlong Q T) x=Q.d := hOrd.trans (hRaw.trans hQMark.symm)
  have hxMask : x∈NonmonomialOrderTail.ordMask (geoTransformAlong Q T) (geoTransformAlong Q T).d := by
    apply (NonmonomialOrderTail.mem_ordMask_iff hn hDomT.isWellFormed hDomT.isNonzeroAlongAt _ x).mpr
    intro hxHigh
    have hLe := (mem_ordGe_iff hDomT.isWellFormed hDomT.isNonzeroAlongAt
      (hNT.symm ▸ mem_univ x) ((geoTransformAlong Q T).d+1)).mp hxHigh
    rw [hOrder,d_geoTransformAlong] at hLe
    omega
  obtain ⟨U,hxU,hSub,hPull,hComp⟩ :=
    exists_companion_window_of_zero_exponents hn (geoTransformAlong Q T) hDomT hNT x
      (NonmonomialOrderTail.ordMask (geoTransformAlong Q T) (geoTransformAlong Q T).d) hxMask hzero
  simp only [d_geoTransformAlong] at hSub hPull hComp
  refine ⟨hOrder,U,hxU,hSub,hPull,hComp,?_⟩
  dsimp only
  intro Z P
  rw [hComp]
  exact ⟨fun _=>rfl,Iff.rfl,rfl⟩

/-- Derived actual recursive values, canonical histories and maximum-locus
centres on one actual companion window. No comparison certificate is input. -/
theorem companion_values_and_centres_of_zero_exponents (hn : 0<n)
    (Q : MarkedIdeal n X) (hQ : IsInvDomain n Q) (hN : Q.N=univ)
    (x : X) (O : Opens X) (hxO : x∈O)
    (hzero : ∀i : Fin Q.E.length,divExpAlong n univ Q.ideal (Q.E.get i) x=0) :
    ∃U : Opens X,x∈U ∧ (U : Set X)⊆O ∧
      let Q' := MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U→X) Q
      companionOf n (M:=CMfd.of (n:=n) U) Q' Q.d=Q' ∧
      ∀(Y : CMfd.{0} n)(T : BlowupTower (CMfd.of (n:=n) U) Y),
        (∀y,(CanonicalCentres.canonicalInvariant n).inv (companionOf n Q' Q.d) T y=
          (CanonicalCentres.canonicalInvariant n).inv Q' T y) ∧
        (IsCanonical (companionOf n Q' Q.d)
            ((CanonicalCentres.canonicalInvariant n).inv (companionOf n Q' Q.d)) T ↔
          IsCanonical Q' ((CanonicalCentres.canonicalInvariant n).inv Q') T) ∧
        ResolutionDriver.maxLocus ((CanonicalCentres.canonicalInvariant n).inv (companionOf n Q' Q.d) T)
          (geoTransformAlong (companionOf n Q' Q.d) T).cosupp=
          ResolutionDriver.maxLocus ((CanonicalCentres.canonicalInvariant n).inv Q' T)
            (geoTransformAlong Q' T).cosupp := by
  obtain ⟨U,hxU,hSub,_hPull,hComp⟩ :=
    exists_companion_window_of_zero_exponents hn Q hQ hN x O hxO hzero
  refine ⟨U,hxU,hSub,hComp,?_⟩
  intro Y T
  rw [hComp]
  exact ⟨fun _=>rfl,Iff.rfl,rfl⟩

private theorem restricted_phase_labels_nonempty
    {A : GermIdeal n (ComplexModel n)} {I : Ideal (HolGerm (ComplexModel n))}
    {G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)} {R : ℕ→ℕ}
    (PHS : ActualGeometricInheritedNeighborhoodHS A I G R)
    {M : Type} (η : presentationOpen PHS→M) (O : Opens (presentationOpen PHS))
    (h0 : (⟨0,PHS.zero_mem⟩ : presentationOpen PHS)∈O)
    (hQ : IsInvDomain n (MarkedIdealBiholomorphism.MarkedIdeal.pullback
      (Subtype.val : O→presentationOpen PHS) (initialWeightedRecord PHS η []))) :
    Nonempty (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)) := by
  by_contra hNo
  let x : O := ⟨⟨0,PHS.zero_mem⟩,h0⟩
  have hx : x∈(MarkedIdealBiholomorphism.MarkedIdeal.pullback
      (Subtype.val : O→presentationOpen PHS) (initialWeightedRecord PHS η [])).N := mem_univ _
  obtain ⟨f,hf,hFreq⟩ := hQ.isNonzeroAlongAt x hx
  obtain ⟨_hhol,K,t,c,ht,_hc,hEq⟩ := hf
  have hZero (i : Fin K) : ∀ᶠy in 𝓝 x,t i y=0 := by
    obtain ⟨g,hg,htg⟩ := ht i
    rw [htg]
    obtain ⟨_hgh,L,v,b,hv,_hb,hSum⟩ := hg
    have hGzero : ∀ᶠz in 𝓝 x.val,g z=0 := by
      filter_upwards [hSum] with z hz
      rw [hz]
      apply Finset.sum_eq_zero
      intro j _
      obtain ⟨a,_ha⟩ := hv j
      exact False.elim (hNo ⟨a⟩)
    exact continuous_subtype_val.continuousAt.eventually hGzero
  apply hFreq
  filter_upwards [hEq,eventually_all.mpr hZero] with y hy hz
  rintro ⟨_hyN,hne⟩
  apply hne
  rw [hy]
  exact Finset.sum_eq_zero (fun i _=>by rw [hz i,mul_zero])

section Original
variable {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- ORIGINAL source-facing companion producer for the SAME full weighted HS phase. -/
theorem exists_original_born_companion_phase
    (hn : 0<n) (W : Set M) (hW : IsComplexAnalyticSubset (n:=n) W) (a₀ : M)
    (ha₀ : a₀∈singularSet (n:=n) W)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) a₀ a₀))
    (hΦsrc : Φ.source⊆(chartAt (ComplexModel n) a₀).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) a₀ a₀)=0) :
    ∃(Ψ : LocalHolomorphicEquivAt (n:=n) (0 : ComplexModel n))(hΨ0 : Ψ.toFun 0=0),
      let Ξ:=currentCoordinateFlattening a₀ Φ hΦ0 Ψ hΨ0
      let Bset:=actualFixedFlatteningSet a₀ Ξ W
      let I:=originalCoherentOriginIdeal (vanishingIdeal (n:=n) Bset)
      ∃(G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I))
        (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)))
        (PHS : ActualGeometricInheritedNeighborhoodHS (vanishingIdeal (n:=n) Bset) I G
          (fun ℓ=>hilbertSamuelAt (vanishingIdeal (n:=n) W) a₀ ℓ))
        (V : Opens M)(η : presentationOpen PHS ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ V),
        Ideal.span (range G.germs)=I ∧ PHS.neighborhood⊆Ξ.target ∧
        (∀z,(η z : M)=actualFlatteningInverseMap a₀ Ξ z.val) ∧
        ∃(P : ActualInheritedWeightedTailData G)(s : ℂ)(hs0 : s≠0)
          (_hs : s∈Metric.ball 0 P.radius)(δ : ℝ)
          (hBound : ∀j : Fin (actualVertexCount n I),normalExponentDegree
            (wordExponent (actualVertexWords n I j))≤P.germs.degreeBound),
          let aFull : Fin (historicalDegreePrefixCount (actualVertexWords n I) P.germs.degreeBound) ≃
            actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I):=
            (historicalDegreeFullLabelEquiv (actualVertexWords n I) P.germs.degreeBound hBound).trans
              (actualVertexEnumeration n I)
          let wFull:=historicalDegreePrefixWords (actualVertexWords n I) P.germs.degreeBound
          let F₀:=fun (v : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I))
            (x : presentationOpen PHS)=>
              (s^weightedDegree (degLexWeight n P.germs.degreeBound) v.val)⁻¹*PHS.representatives v x.val
          ∃hF₀ : ∀v x,HolomorphicAt n (F₀ v) x,
          ∃O : Opens (presentationOpen PHS),
            (⟨0,PHS.zero_mem⟩ : presentationOpen PHS)∈O ∧
            (∃K : Set (presentationOpen PHS),IsCompact K ∧ (O : Set (presentationOpen PHS))⊆K) ∧
            (∀x∈O,x.val∈historicalNativeJetWindow P s hs0 δ) ∧
            let ι : O → M:=fun x=>(η x.val : M)
            let Q:=MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : O → presentationOpen PHS)
              (initialWeightedRecord PHS (fun z=>(η z : M)) ([] : List (Set M)))
            let Wphase:=(Subtype.val : O → presentationOpen PHS) ⁻¹'
              ((Subtype.val : presentationOpen PHS → ComplexModel n) ⁻¹' Bset)
            ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ ι ∧
            Topology.IsOpenEmbedding ι ∧ a₀∈range ι ∧
            IsInvDomain n Q ∧ Q.N=univ ∧ Q.E=([] : List (Set M)).map (ι ⁻¹' ·) ∧
            Q.d=weightedCommonMark (fun v : actualInitialVertices MonomialOrder.degLex
              (analyticZeroTaylorIdeal n I)=>normalExponentDegree v.val) ∧
            IsComplexAnalyticSubset (n:=n) Wphase ∧
            Q.cosupp={x | ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) Wphase) x ℓ=
              hilbertSamuelAt (vanishingIdeal (n:=n) W) a₀ ℓ} ∧
            (∀x ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) Wphase) x ℓ≤
              hilbertSamuelAt (vanishingIdeal (n:=n) W) a₀ ℓ) ∧
            (∃(Y : CMfd.{0} n)(T : BlowupTower (CMfd.of (n:=n) O) Y),
              IsCanonical Q ((CanonicalCentres.canonicalInvariant n).inv Q) T ∧ IsGeoResolution Q T) ∧
            (∀(Y : CMfd.{0} n)(T : BlowupTower (CMfd.of (n:=n) O) Y),IsGeoTestTower Q T →
              ActualNativeOriginalFunctionTowerHistory S aFull wFull Wphase Q F₀ hF₀
                (Subtype.val : O → presentationOpen PHS) contMDiff_subtype_val T) ∧
            (∀(Y : CMfd.{0} n)(T : BlowupTower (CMfd.of (n:=n) O) Y),IsGeoResolution Q T →
              ActualHistoricalNativeTowerCentres Wphase T ∧
              ∀z : Y,toLex (hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n T.proj Wphase)) z)<
                toLex (hilbertSamuelAt (vanishingIdeal (n:=n) W) a₀)) ∧
            (∀(Y : CMfd.{0} n)(T : BlowupTower (CMfd.of (n:=n) O) Y),IsGeoTestTower Q T →
              ActualHistoricalNativeTowerCentres Wphase T ∧
              (geoTransformAlong Q T).cosupp={z | ∀ℓ,
                hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n T.proj Wphase)) z ℓ=
                  hilbertSamuelAt (vanishingIdeal (n:=n) W) a₀ ℓ} ∧
              ∀x∈(geoTransformAlong Q T).cosupp,
                nmOrd (geoTransformAlong Q T) x=Q.d ∧
                ∃U : Opens Y,x∈U ∧
                  (U : Set Y)⊆NonmonomialOrderTail.ordMask (geoTransformAlong Q T) Q.d ∧
                  MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U→Y)
                    (companionOf n (geoTransformAlong Q T) Q.d)=
                    MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U→Y) (geoTransformAlong Q T) ∧
                  companionOf n (M:=CMfd.of (n:=n) U)
                    (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U→Y) (geoTransformAlong Q T)) Q.d=
                    MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U→Y) (geoTransformAlong Q T) ∧
                  let Q' := MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U→Y) (geoTransformAlong Q T)
                  ∀(Z : CMfd.{0} n)(P : BlowupTower (CMfd.of (n:=n) U) Z),
                    (∀z,(CanonicalCentres.canonicalInvariant n).inv (companionOf n Q' Q.d) P z=
                      (CanonicalCentres.canonicalInvariant n).inv Q' P z) ∧
                    (IsCanonical (companionOf n Q' Q.d)
                        ((CanonicalCentres.canonicalInvariant n).inv (companionOf n Q' Q.d)) P ↔
                      IsCanonical Q' ((CanonicalCentres.canonicalInvariant n).inv Q') P) ∧
                    ResolutionDriver.maxLocus ((CanonicalCentres.canonicalInvariant n).inv (companionOf n Q' Q.d) P)
                      (geoTransformAlong (companionOf n Q' Q.d) P).cosupp=
                      ResolutionDriver.maxLocus ((CanonicalCentres.canonicalInvariant n).inv Q' P)
                        (geoTransformAlong Q' P).cosupp) := by
  obtain ⟨Ψ,hΨ0,G,S,PHS,V,η,hSpan,hPHS,hη,P,s,hs0,hs,δ,hBound,hF₀,O,hOzero,hCompact,hOwindow,
      hMap,hOpen,haImage,hDom,hN,hBoundary,hQMark,hWphase,hCut,hUpper,hCan,hHist,hDrop⟩ :=
    exists_actual_original_native_anchored_hs_phase W hW a₀ ha₀ [] isSNCDivisor_nil Φ hΦsrc hΦ0
  let Ξ := currentCoordinateFlattening a₀ Φ hΦ0 Ψ hΨ0
  let Bset := actualFixedFlatteningSet a₀ Ξ W
  let I := originalCoherentOriginIdeal (vanishingIdeal (n:=n) Bset)
  let aFull : Fin (historicalDegreePrefixCount (actualVertexWords n I) P.germs.degreeBound) ≃
      actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I) :=
    (historicalDegreeFullLabelEquiv (actualVertexWords n I) P.germs.degreeBound hBound).trans
      (actualVertexEnumeration n I)
  let wFull := historicalDegreePrefixWords (actualVertexWords n I) P.germs.degreeBound
  let F₀ := fun (v : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I))
      (x : presentationOpen PHS)=>
    (s^weightedDegree (degLexWeight n P.germs.degreeBound) v.val)⁻¹*PHS.representatives v x.val
  let Q := MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : O→presentationOpen PHS)
    (initialWeightedRecord PHS (fun z=>(η z : M)) [])
  let Wphase := (Subtype.val : O→presentationOpen PHS) ⁻¹'
    ((Subtype.val : presentationOpen PHS→ComplexModel n) ⁻¹' Bset)
  have hWords (j : Fin (historicalDegreePrefixCount (actualVertexWords n I) P.germs.degreeBound)) :
      wordExponent (wFull j)=(aFull j).val := by
    let v := actualVertexEnumeration n I (historicalDegreePrefixLabel (actualVertexWords n I) P.germs.degreeBound j)
    change wordExponent (wordOfExponent v.val)=v.val
    exact wordExponent_wordOfExponent v.val
  have hOwn := HironakaActualHistoricalInitialFiveLawWindow.actual_initial_vertex_heads_have_historical_owner
    MonomialOrder.degLex (analyticZeroTaylorIdeal n I) aFull wFull hWords
  have hNonempty := restricted_phase_labels_nonempty PHS (fun z=>(η z : M)) O hOzero hDom
  have hV : (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)).Nonempty := by
    obtain ⟨v⟩ := hNonempty
    exact ⟨v.val,v.property⟩
  have hProduct : weightedCommonMark (fun v : actualInitialVertices MonomialOrder.degLex
      (analyticZeroTaylorIdeal n I)=>normalExponentDegree v.val)≠0 := by
    rw [← hQMark]
    exact Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hDom.one_le_d)
  have hPositive (v : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)) :
      0<normalExponentDegree v.val :=
    Nat.pos_of_ne_zero ((Finset.prod_ne_zero_iff.mp hProduct) v (Finset.mem_univ v))
  have hSource (x : O) (hx : x∈Q.cosupp) :
      ActualHistoricalNativePointPresentation S aFull wFull Wphase Q x := by
    have hRefl := hHist (CMfd.of (n:=n) O) (.refl) trivial
    have hFunction : ActualHistoricalNativeFunctionPresentation S aFull wFull
        (strictTransform n (id : O→O) Wphase) Q F₀ hF₀
        (Subtype.val : O→presentationOpen PHS) contMDiff_subtype_val x := hRefl.1 x hx
    obtain ⟨Θ,hΘsrc,hΘ0,Γ,_d,hFive,hSpanAt,hCompAt,_hd,_hEq⟩ := hFunction
    have hid : strictTransform n (id : O→O) Wphase=Wphase := by
      rw [strictTransform,exceptionalLocus_id,sdiff_empty,preimage_id,hWphase.isClosed.closure_eq]
    exact hid ▸ ⟨Θ,hΘsrc,hΘ0,Γ,hFive,hSpanAt,hCompAt⟩
  have hEmpty : Q.E=[] := by simpa only [List.map_nil] using hBoundary
  refine ⟨Ψ,hΨ0,G,S,PHS,V,η,hSpan,hPHS,hη,P,s,hs0,hs,δ,hBound,hF₀,O,hOzero,hCompact,hOwindow,
    hMap,hOpen,haImage,hDom,hN,hBoundary,hQMark,hWphase,hCut,hUpper,hCan,hHist,hDrop,?_⟩
  intro Y T hTest
  exact (actual_native_history_companion_window hn W hW a₀ ha₀ Wphase hWphase Q hDom hN hEmpty
    S hV aFull wFull hWords hPositive hOwn hQMark hCut hUpper hSource T hTest)

end Original

end
end Hironaka.HironakaActualHistoricalBornCompanionRecursion
