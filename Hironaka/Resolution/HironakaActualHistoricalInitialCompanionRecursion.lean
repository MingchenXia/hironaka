import Hironaka.Resolution.HironakaActualHistoricalBornCompanionRecursion

/-! Actual ORIGINAL-clock initial companion recursion for the genuine weighted
HS source. The full value, original order run and Step One canonical history
are derived; no weighted coefficient-recoding or normal-padding CAN is claimed.
Blueprint FIRST: hironaka-actual-historical-initial-companion-recursion.tex. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualHistoricalInitialCompanionRecursion
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
  HironakaActualHistoricalBornCompanionRecursion HironakaActualHistoricalOriginalNativePhase
  HironakaActualHistoricalNativeFunctionTower HironakaActualHistoricalNativeGivenTower
  HironakaActualHistoricalSortedPrefixFrames HironakaActualHistoricalWholeJetFrames
  HironakaActualHistoricalPrefixJetFrames HironakaActualGeometricCurrentNeighborhoodHS
  HironakaActualRelativeNormalJetDivision HironakaActualFixedInheritedSelector
  HironakaActualInheritedNestedContactFlag HironakaActualNormalZeroAnalyticSaturation
  HironakaActualFormalInitialDiagram HironakaActualInheritedSmallTails
  HironakaActualWeightedVertexSmallTails HironakaActualFiniteDegLexWeights
  HironakaActualCauchyMonomialDivision HironakaRelativeNormalMonomialBasis
  HironakaActualCoefficientPresentationCentrePower HironakaActualOriginalInitialHSPhase
  HironakaActualHistoricalHSMarkedDomain HironakaActualPrescribedCentreRebasing
  HironakaActualFixedFlatteningHSComparison HironakaSmoothCentreCoherentDomain
  HironakaRelativeNormalDeformationInitialRelations HironakaHolomorphicJetChartInvariance
  HironakaSmoothSubmersionGermIdealColon HironakaActualOriginalFormalHSTransfer
  HironakaActualOriginalScaledAnalyticDivision HironakaActualWeightedCoefficientCompression
  HironakaEmbeddedAnalytic HironakaSharpOriginalProductTraceOrder
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec CanonicalCentres CompanionRebase CompanionReductionAlong GeneralCompare
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen InvDomainTowerAlong
  NonmonomialOrderLocal NonmonomialOrderTail NonmonomialOrderRegime
  GeneralValue StepOneRegime StepOneLowerDomain StepOneWellFounded NormalCrossings HomogenizedIdealAlong

variable {n : ℕ} {X : CMfd.{0} n}

private def positiveValue (k M : ℕ) (v : ℕ ×ₗ WithTop (ValTy k)) : ValTy (k+1) :=
  toLex (M,toLex (Sum.inr (v : WithTop (ℕ ×ₗ WithTop (ValTy k)))))

private theorem strictMono_positiveValue (k M : ℕ) : StrictMono (positiveValue k M) := by
  intro a b h
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr
    ⟨rfl,Sum.Lex.inr_lt_inr_iff.mpr (WithTop.coe_lt_coe.mpr h)⟩)

private theorem initial_companion (Q : MarkedIdeal n X) (hI : Q.ideal.IsCoherent)
    (hN : Q.N=univ) (hE : Q.E=[]) : companionOf n Q Q.d=Q := by
  have hComp : companionOf n Q Q.d=
      ⟨Q.N,Q.E,MonomialPartAlong.nonmonomialPartAlong n Q.N Q.ideal Q.E,Q.d⟩ := by
    simp only [companionOf,companionAlong,lt_self_iff_false,if_false]
  rw [hComp]
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · rfl
  · rfl
  · rw [hE,hN,nonmonomialPartAlong_nil_eq_restrictOn,
      BlowupTowerTransforms.restrictOn_univ hI]
  · rfl

private theorem split_full : ∀{Y : CMfd.{0} n}(T : BlowupTower X Y),
    split T T.length=⟨X,.refl,T⟩
  | _,.refl=>rfl
  | _,.step T C π hπ=>by
    change (⟨(split T T.length).1,(split T T.length).2.1,
      .step (split T T.length).2.2 C π hπ⟩ : Σ A : CMfd.{0} n,BlowupTower X A × BlowupTower A _)=_
    rw [split_full T]

private theorem native_full_run {Λ : Type} [LinearOrder Λ]
    (F : ∀{A : CMfd.{0} n},MarkedIdeal n A → ∀{B : CMfd.{0} n},BlowupTower A B → B→Λ)
    (Q : MarkedIdeal n X) (q : ℕ) (hq : q≠0) {Y : CMfd.{0} n}
    (T : BlowupTower X Y)(x : Y)(hRaw : nmOrd (geoTransformAlong Q T) x=q)
    (hRun : regimeRun (OrdRegime Q q) T x=T.length)
    (hm : T.proj x∈ordMask Q q) :
    genInv F Q T x=toLex (q,toLex (Sum.inr
      ((F (companionOf n (M:=CMfd.of (n:=n) (ordMask Q q))
          (MarkedIdeal.pullback (Subtype.val : ordMask Q q→X) Q) q)
        (restrict (ordMask Q q) T) ⟨x,hm⟩ : Λ) : WithTop Λ))) := by
  rw [genInv_of_nmOrd_ne_zero F Q T hRaw hq,hRun]
  unfold head tail
  rw [split_full T]
  have hm' : T.proj x∈ordMask (geoTransformAlong Q (.refl : BlowupTower X X)) q := hm
  rw [genLowerValue_eq_of_mem (o:=q) (T₀:=(.refl : BlowupTower X X)) (T₁:=T) F Q hm']
  rfl

private theorem full_run (Q : MarkedIdeal n X) (hQ : IsInvDomain n Q)
    (hOrder : ∀{Y : CMfd.{0} n}(T : BlowupTower X Y),IsGeoTestTower Q T →
      ∀x∈(geoTransformAlong Q T).cosupp,nmOrd (geoTransformAlong Q T) x=Q.d) :
    ∀{Y : CMfd.{0} n}(T : BlowupTower X Y),IsGeoTestTower Q T →
      ∀x∈(geoTransformAlong Q T).cosupp,regimeRun (OrdRegime Q Q.d) T x=T.length
  | _,.refl,_,_,_=>rfl
  | _,.step T C π hπ,hT,x,hx=>by
    have hp := proj_mem_cosupp_step hQ.isWellFormed.isClosedSubmanifold_N
      hQ.isWellFormed.isCoherent T C π hπ hT hx
    rw [regimeRun_step_of (OrdRegime Q Q.d) T C π hπ ⟨hp,hOrder T hT.1 _ hp⟩,
      full_run Q hQ hOrder T hT.1 _ hp]
    rfl

private theorem initial_mask (hn : 0<n) (Q : MarkedIdeal n X) (hQ : IsInvDomain n Q)
    (hOrder : ∀{Y : CMfd.{0} n}(T : BlowupTower X Y),IsGeoTestTower Q T →
      ∀x∈(geoTransformAlong Q T).cosupp,nmOrd (geoTransformAlong Q T) x=Q.d)
    {Y : CMfd.{0} n}(T : BlowupTower X Y)(hT : IsGeoTestTower Q T)
    (x : Y)(hx : x∈(geoTransformAlong Q T).cosupp) : T.proj x∈ordMask Q Q.d := by
  have hp := proj_mem_cosupp_of_mem_cosupp hQ.isWellFormed.isClosedSubmanifold_N
    hQ.isWellFormed.isCoherent T hT hx
  apply (mem_ordMask_iff hn hQ.isWellFormed hQ.isNonzeroAlongAt Q.d (T.proj x)).mpr
  intro hHigh
  have hLe := (mem_ordGe_iff hQ.isWellFormed hQ.isNonzeroAlongAt
    (Q.cosupp_subset_N hp) (Q.d+1)).mp hHigh
  have hRaw := hOrder (.refl : BlowupTower X X) trivial _ hp
  change nmOrd Q (T.proj x)=Q.d at hRaw
  rw [hRaw] at hLe
  omega

private theorem initial_record (Q : MarkedIdeal n X) (hQ : IsInvDomain n Q)
    (hN : Q.N=univ) (hE : Q.E=[]) :
    companionOf n (M:=CMfd.of (n:=n) (ordMask Q Q.d)) (MarkedIdeal.pullback (Subtype.val : ordMask Q Q.d→X) Q) Q.d=
      MarkedIdeal.pullback (Subtype.val : ordMask Q Q.d→X) Q := by
  have hA := isInvDomain_pullback_val (ordMask Q Q.d) hQ
  apply initial_companion _ hA.isWellFormed.isCoherent
  · change (Subtype.val : ordMask Q Q.d→X) ⁻¹' Q.N=univ
    rw [hN,preimage_univ]
  · change Q.E.map ((Subtype.val : ordMask Q Q.d→X) ⁻¹' ·)=[]
    rw [hE,List.map_nil]

private theorem actual_full_value (hn : 0<n) (k : ℕ) (Q : MarkedIdeal n X)
    (hQ : IsInvDomain n Q)
    (hOrder : ∀{Y : CMfd.{0} n}(T : BlowupTower X Y),IsGeoTestTower Q T →
      ∀x∈(geoTransformAlong Q T).cosupp,nmOrd (geoTransformAlong Q T) x=Q.d)
    {Y : CMfd.{0} n}(T : BlowupTower X Y)(hT : IsGeoTestTower Q T)
    (x : Y)(hx : x∈(geoTransformAlong Q T).cosupp)
    (hm : T.proj x∈ordMask Q Q.d) :
    (invFamily hn (k+1)).inv Q T x=positiveValue k Q.d
      (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k)
        (companionOf n (M:=CMfd.of (n:=n) (ordMask Q Q.d)) (MarkedIdeal.pullback (Subtype.val : ordMask Q Q.d→X) Q) Q.d) (restrict (ordMask Q Q.d) T) ⟨x,hm⟩) := by
  exact native_full_run
    (fun {A} L {B} S y=>Seq.StepOneValueMasked.stepOneInvM (X:=A) (invFamily hn k) L (Y:=B) S y)
    Q Q.d (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hQ.one_le_d)) T x
    (hOrder T hT x hx) (full_run Q hQ hOrder T hT x hx) hm

private theorem actual_centre_eq (hn : 0<n) (k : ℕ) (Q : MarkedIdeal n X)
    (hQ : IsInvDomain n Q) (hN : Q.N=univ) (hE : Q.E=[])
    (hOrder : ∀{Y : CMfd.{0} n}(T : BlowupTower X Y),IsGeoTestTower Q T →
      ∀x∈(geoTransformAlong Q T).cosupp,nmOrd (geoTransformAlong Q T) x=Q.d)
    {Y : CMfd.{0} n}(T : BlowupTower X Y)(hT : IsGeoTestTower Q T) :
    (Subtype.val : openPreimage T (ordMask Q Q.d)→Y) ⁻¹'
        ResolutionDriver.maxLocus ((invFamily hn (k+1)).inv Q T) (geoTransformAlong Q T).cosupp=
      ResolutionDriver.maxLocus
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) (companionOf n (M:=CMfd.of (n:=n) (ordMask Q Q.d)) (MarkedIdeal.pullback (Subtype.val : ordMask Q Q.d→X) Q) Q.d)
          (restrict (ordMask Q Q.d) T))
        (geoTransformAlong (companionOf n (M:=CMfd.of (n:=n) (ordMask Q Q.d)) (MarkedIdeal.pullback (Subtype.val : ordMask Q Q.d→X) Q) Q.d) (restrict (ordMask Q Q.d) T)).cosupp := by
  have hCurrent := isInvDomain_geoTransformAlong hQ T hT
  have hTransform := geoTransformAlong_restrict (ordMask Q Q.d)
    hQ.isWellFormed.isClosedSubmanifold_N hQ.isWellFormed.isCoherent T hT
  have hCos : (geoTransformAlong (companionOf n (M:=CMfd.of (n:=n) (ordMask Q Q.d)) (MarkedIdeal.pullback (Subtype.val : ordMask Q Q.d→X) Q) Q.d) (restrict (ordMask Q Q.d) T)).cosupp=
      (Subtype.val : openPreimage T (ordMask Q Q.d)→Y) ⁻¹' (geoTransformAlong Q T).cosupp := by
    have hRec := congrArg (fun L : MarkedIdeal n (CMfd.of (n:=n) (ordMask Q Q.d))=>
      geoTransformAlong L (restrict (ordMask Q Q.d) T)) (initial_record Q hQ hN hE)
    exact (congrArg MarkedIdeal.cosupp (hRec.trans hTransform)).trans
      (cosupp_pullback_val _
        (fun _ _ h=>RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hCurrent.isWellFormed.isCoherent h) _)
  rw [hCos]
  ext x
  constructor
  · rintro ⟨hx,hmax⟩
    refine ⟨hx,fun y hy=>?_⟩
    have h := hmax y.val hy
    rw [actual_full_value hn k Q hQ hOrder T hT y.val hy y.property,
      actual_full_value hn k Q hQ hOrder T hT x.val hx x.property] at h
    exact (strictMono_positiveValue k Q.d).le_iff_le.mp h
  · rintro ⟨hx,hmax⟩
    refine ⟨hx,fun y hy=>?_⟩
    have hm := initial_mask hn Q hQ hOrder T hT y hy
    have h := hmax ⟨y,hm⟩ hy
    rw [actual_full_value hn k Q hQ hOrder T hT y hy hm,
      actual_full_value hn k Q hQ hOrder T hT x.val hx x.property]
    exact (strictMono_positiveValue k Q.d).monotone h

private theorem actual_initial_can (hn : 0<n) (k : ℕ) (Q : MarkedIdeal n X)
    (hQ : IsInvDomain n Q) (hN : Q.N=univ) (hE : Q.E=[])
    (hOrder : ∀{Y : CMfd.{0} n}(T : BlowupTower X Y),IsGeoTestTower Q T →
      ∀x∈(geoTransformAlong Q T).cosupp,nmOrd (geoTransformAlong Q T) x=Q.d) :
    ∀{Y : CMfd.{0} n}(T : BlowupTower X Y),IsGeoTestTower Q T →
      IsCanonical Q ((invFamily hn (k+1)).inv Q) T →
      IsCanonical (companionOf n (M:=CMfd.of (n:=n) (ordMask Q Q.d)) (MarkedIdeal.pullback (Subtype.val : ordMask Q Q.d→X) Q) Q.d)
        (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) (companionOf n (M:=CMfd.of (n:=n) (ordMask Q Q.d)) (MarkedIdeal.pullback (Subtype.val : ordMask Q Q.d→X) Q) Q.d))
        (restrict (ordMask Q Q.d) T)
  | _,.refl,_,_=>trivial
  | _,.step T C π hπ,hT,hCan=>by
    refine ⟨actual_initial_can hn k Q hQ hN hE hOrder T hT.1 hCan.1,?_⟩
    rcases hCan.2 with hC | hC
    · left
      rw [hC,preimage_empty]
    · right
      rw [hC]
      exact actual_centre_eq hn k Q hQ hN hE hOrder T hT.1

private theorem initial_history_data (hn : 0<n) (Q : MarkedIdeal n X)
    (hDom : IsInvDomain n Q) (hN : Q.N=univ) (hEmpty : Q.E=[])
    (hOrder : ∀{Y : CMfd.{0} n}(T : BlowupTower X Y),IsGeoTestTower Q T →
      ∀x∈(geoTransformAlong Q T).cosupp,nmOrd (geoTransformAlong Q T) x=Q.d)
    (k : ℕ) (hnk : n≤k+1) {Y : CMfd.{0} n} (T : BlowupTower X Y)
    (hCanT : IsCanonical Q ((invFamily hn (k+1)).inv Q) T) :
    let U:=ordMask Q Q.d
    let J : MarkedIdeal n (CMfd.of (n:=n) U):=companionOf n (M:=CMfd.of (n:=n) U)
      (MarkedIdeal.pullback (Subtype.val : U→X) Q) Q.d
    J=MarkedIdeal.pullback (Subtype.val : U→X) Q ∧
    IsInvDomain (k+1) J ∧ IsMaximalOrderAlong J.N J.ideal J.d ∧
    IsGeoTestTower J (restrict U T) ∧
    (restrict U T).length=T.length ∧
    IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J) (restrict U T) ∧
    (geoTransformAlong J (restrict U T)).cosupp=
      (Subtype.val : openPreimage T U→Y) ⁻¹' (geoTransformAlong Q T).cosupp ∧
    (geoTransformAlong J (restrict U T)).E=(geoTransformAlong Q T).E.map
      ((Subtype.val : openPreimage T U→Y) ⁻¹' ·) ∧
    (geoTransformAlong J (restrict U T)).d=Q.d ∧
    (∀x∈(geoTransformAlong Q T).cosupp,
      nmOrd (geoTransformAlong Q T) x=Q.d ∧ regimeRun (OrdRegime Q Q.d) T x=T.length ∧
      ∃hm : T.proj x∈U,(invFamily hn (k+1)).inv Q T x=
        toLex (Q.d,toLex (Sum.inr
          ((Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J (restrict U T)
            ⟨x,hm⟩ : ℕ ×ₗ WithTop (ValTy k)) : WithTop (ℕ ×ₗ WithTop (ValTy k)))))) ∧
    (Subtype.val : openPreimage T U→Y) ⁻¹'
        ResolutionDriver.maxLocus ((invFamily hn (k+1)).inv Q T) (geoTransformAlong Q T).cosupp=
      ResolutionDriver.maxLocus (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J (restrict U T))
        (geoTransformAlong J (restrict U T)).cosupp := by
  dsimp only
  have hDomk : IsInvDomain (k+1) Q := by
    refine ⟨hDom.isWellFormed,?_,hDom.one_le_d,hDom.isNonzeroAlongAt⟩
    intro x hx
    obtain ⟨j,hj,hReg⟩ := hDom.dimLE x hx
    exact ⟨j,hj.trans hnk,hReg⟩
  have hTest := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
    (invFamily hn (k+1)).isInvValue hDomk T hCanT
  have hJ := initial_record (X:=X) Q hDom hN hEmpty
  have hCurrent := isInvDomain_geoTransformAlong hDom T hTest
  have hTransform := geoTransformAlong_restrict (ordMask Q Q.d)
    hDom.isWellFormed.isClosedSubmanifold_N hDom.isWellFormed.isCoherent T hTest
  have hTestJ : IsGeoTestTower (companionOf n (M:=CMfd.of (n:=n) (ordMask Q Q.d))
      (MarkedIdeal.pullback (Subtype.val : ordMask Q Q.d→X) Q) Q.d)
      (restrict (ordMask Q Q.d) T) := by
    rw [hJ]
    exact isGeoTestTower_restrict (ordMask Q Q.d) hDom.isWellFormed.isClosedSubmanifold_N
      hDom.isWellFormed.isCoherent T hTest
  refine ⟨hJ,isInvDomain_compAt hn hDom.one_le_d .refl hDomk,
    isMaximalOrderAlong_compAt hn Q.d .refl hDomk,hTestJ,length_restrict (ordMask Q Q.d) T,
    actual_initial_can hn k Q hDom hN hEmpty hOrder T hTest hCanT,?_,?_,?_,?_,
    actual_centre_eq hn k Q hDom hN hEmpty hOrder T hTest⟩
  · rw [hJ,hTransform]
    exact cosupp_pullback_val _
      (fun _ _ h=>RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hCurrent.isWellFormed.isCoherent h) _
  · rw [hJ,hTransform]
    rfl
  · rw [d_geoTransformAlong]
    rw [hJ]
    rfl
  · intro x hx
    exact ⟨hOrder T hTest x hx,full_run Q hDom hOrder T hTest x hx,
      initial_mask hn Q hDom hOrder T hTest x hx,
      actual_full_value hn k Q hDom hOrder T hTest x hx (initial_mask hn Q hDom hOrder T hTest x hx)⟩


section Original
variable {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- ORIGINAL-only full native initial-companion recursion, retaining the SAME given histories and clocks. -/
theorem exists_original_initial_companion_recursion
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
            (∀(k : ℕ),n≤k+1 → ∀(Y : CMfd.{0} n)(T : BlowupTower (CMfd.of (n:=n) O) Y),
              IsCanonical Q ((invFamily hn (k+1)).inv Q) T →
              let U:=ordMask Q Q.d
              let J : MarkedIdeal n (CMfd.of (n:=n) U):=companionOf n (M:=CMfd.of (n:=n) U)
                (MarkedIdeal.pullback (Subtype.val : U→O) Q) Q.d
              J=MarkedIdeal.pullback (Subtype.val : U→O) Q ∧
              IsInvDomain (k+1) J ∧ IsMaximalOrderAlong J.N J.ideal J.d ∧
              IsGeoTestTower J (restrict U T) ∧
              (restrict U T).length=T.length ∧
              IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J) (restrict U T) ∧
              (geoTransformAlong J (restrict U T)).cosupp=
                (Subtype.val : openPreimage T U→Y) ⁻¹' (geoTransformAlong Q T).cosupp ∧
              (geoTransformAlong J (restrict U T)).E=(geoTransformAlong Q T).E.map
                ((Subtype.val : openPreimage T U→Y) ⁻¹' ·) ∧
              (geoTransformAlong J (restrict U T)).d=Q.d ∧
              (∀x∈(geoTransformAlong Q T).cosupp,
                nmOrd (geoTransformAlong Q T) x=Q.d ∧ regimeRun (OrdRegime Q Q.d) T x=T.length ∧
                ∃hm : T.proj x∈U,(invFamily hn (k+1)).inv Q T x=
                  toLex (Q.d,toLex (Sum.inr
                    ((Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J (restrict U T)
                      ⟨x,hm⟩ : ℕ ×ₗ WithTop (ValTy k)) : WithTop (ℕ ×ₗ WithTop (ValTy k)))))) ∧
              (Subtype.val : openPreimage T U→Y) ⁻¹'
                  ResolutionDriver.maxLocus ((invFamily hn (k+1)).inv Q T) (geoTransformAlong Q T).cosupp=
                ResolutionDriver.maxLocus (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J (restrict U T))
                  (geoTransformAlong J (restrict U T)).cosupp) := by
  obtain ⟨Ψ,hΨ0,G,S,PHS,V,η,hSpan,hPHS,hη,P,s,hs0,hs,δ,hBound,hF₀,O,hOzero,hCompact,hOwindow,
      hMap,hOpen,haImage,hDom,hN,hBoundary,hQMark,hWphase,hCut,hUpper,hCan,hHist,hDrop,hRec⟩ :=
    exists_original_born_companion_phase hn W hW a₀ ha₀ Φ hΦsrc hΦ0
  let Q:=MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : O→presentationOpen PHS)
    (initialWeightedRecord PHS (fun z=>(η z : M)) [])
  have hEmpty : Q.E=[] := by simpa only [List.map_nil] using hBoundary
  have hOrder : ∀{Y : CMfd.{0} n}(T : BlowupTower (CMfd.of (n:=n) O) Y),IsGeoTestTower Q T →
      ∀x∈(geoTransformAlong Q T).cosupp,nmOrd (geoTransformAlong Q T) x=Q.d := by
    intro Y T hT x hx
    exact ((hRec Y T hT).2.2 x hx).1
  refine ⟨Ψ,hΨ0,G,S,PHS,V,η,hSpan,hPHS,hη,P,s,hs0,hs,δ,hBound,hF₀,O,hOzero,hCompact,hOwindow,
    hMap,hOpen,haImage,hDom,hN,hBoundary,hQMark,hWphase,hCut,hUpper,hCan,hHist,hDrop,?_⟩
  intro k hnk Y T hCanT
  exact initial_history_data (X:=CMfd.of (n:=n) O) hn Q hDom hN hEmpty hOrder k hnk T hCanT

end Original

end
end Hironaka.HironakaActualHistoricalInitialCompanionRecursion
