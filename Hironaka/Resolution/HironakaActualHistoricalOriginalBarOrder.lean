import Hironaka.Resolution.HironakaActualHistoricalBornCompanionRecursion
import Hironaka.Resolution.HironakaActualNormalPaddingNativeCompanion

/-! Historical raw orders of ORIGINAL coefficient/homogenized records.
The factorial marks remain literal; there is no native suffix/CAN comparison.
Blueprint FIRST: hironaka-actual-historical-original-bar-order.tex. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualHistoricalOriginalBarOrder
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaActualHistoricalBornCompanionRecursion HironakaActualHistoricalNativeGivenTower
  HironakaActualHistoricalNativeOrdinaryOrder HironakaActualNativeBornWeightedExponents
  HironakaActualHistoricalNativeStageStep HironakaActualFixedInheritedSelector
  HironakaRelativeNormalMonomialBasis HironakaActualCoefficientPresentationCentrePower
  HironakaActualWeightedCoefficientCompression HironakaActualCauchyMonomialDivision
  HironakaActualHistoricalWholeJetFrames HironakaActualHistoricalSortedPrefixFrames
  HironakaStageCenters HironakaEmbeddedAnalytic HironakaHolomorphicJetChartInvariance
  RelativePrincipalizationSpan InvertibleIdealQuotient GermIdealTotalTransform
  GermIdealOrder IdealWeightPowers IdealOrderArithmetic DerivativeIdealTower
  CoefficientIdeal HomogenizedEquivalence HomogenizedIdealAlong HomogenizedIdealAlongTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealEquivalence.MarkedIdeal
  MarkedIdealOperationsTransform BlowupTowers BlowupTowerTransforms
  StepOneValue StepOneRegime StepOneLowerDomain DivisorExponent DivisorExponentAlong
  OrderTaylor BlowupDerivativeIdeal
  MonomialPartAlong RestrictedIdealExtension RestrictedIdealQuotient
  ResolutionInvariantSpec InvDomainTowerAlong NonmonomialOrderLocal CanonicalCentres

variable {n : ℕ} {X : CMfd.{0} n}

private theorem coefficient_mark (Q : MarkedIdeal n X) :
    (coeffMarkedAlong Q).d=(Finset.range Q.d).prod (fun j=>Q.d-j) := rfl

/-- The actual ORIGINAL coefficient transform contains the literal zeroth
derivative power of the SAME given history. No current-record reset. -/
theorem original_coefficient_history_power_le (Q : MarkedIdeal n X)
    (hN : Q.N=univ) (hI : Q.ideal.IsCoherent) (hd : 1≤Q.d)
    {Y : CMfd.{0} n}(T : BlowupTower X Y)(hT : IsGeoTestTower Q T) :
    let e:=sumExp (fun j=>Q.d-j) Q.d 0
    1≤e ∧ Q.d*e=(coeffMarkedAlong Q).d ∧
      IsGeoTestTower (coeffMarkedAlong Q) T ∧
      (geoTransformAlong (coeffMarkedAlong Q) T).E=(geoTransformAlong Q T).E ∧
      (idealPow (geoTransformAlong Q T).ideal e).Le
        (geoTransformAlong (coeffMarkedAlong Q) T).ideal := by
  let e:=sumExp (fun j=>Q.d-j) Q.d 0
  have hEq : coeffMarkedAlong Q=coeffMarked Q :=
    coeffMarkedAlong_eq_coeffMarked hN (fun _ _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem hI hg)
  have hFam:=isAmbientFamily_derivMarked hN hI
  have hAll : ∀i<Q.d,IsGeoTestTower (derivMarked Q i) T :=
    fun i hi=>(inclusions_tower Q hN hI hi.le T hT).1
  obtain ⟨hWhole,hCurrentFam⟩:=
    (geoTransformAlong_msum (fun i=>derivMarked Q i) hd hFam T).2 hAll
  have hPower : (idealPow (geoTransformAlong Q T).ideal e).Le
      (geoTransformAlong (coeffMarked Q) T).ideal := by
    change (idealPow (geoTransformAlong Q T).ideal e).Le
      (geoTransformAlong (msum (fun i=>derivMarked Q i) Q.d) T).ideal
    rw [hWhole]
    intro z f hf
    change IsInSpanAt (n:=n)
      (fun g=>∃i,i<Q.d ∧ (idealPow (geoTransformAlong (derivMarked Q i) T).ideal
        (sumExp (fun j=>(geoTransformAlong (derivMarked Q j) T).d) Q.d i)).mem z g) z f
    refine isInSpanAt_self ⟨0,hd,?_⟩ (holomorphicAt_of_mem_idealPow hf)
    simpa only [d_geoTransformAlong,derivMarked_d,derivMarked_zero] using hf
  refine ⟨one_le_sumExp (fun j hj=>by omega) 0,?_,?_,?_,?_⟩
  · rw [coefficient_mark]
    simpa only [Nat.sub_zero] using mul_sumExp (fun j=>Q.d-j) (show 0<Q.d by omega)
  · rw [hEq]
    exact (coeff_tower Q hN hI hd T).1.mpr hT
  · exact E_geoTransformAlong_eq (𝔪:=coeffMarkedAlong Q) (𝔫:=Q) rfl T
  · rw [hEq]
    exact hPower

private theorem original_bar_power_le (Q : MarkedIdeal n X)
    (hN : Q.N=univ) (hI : Q.ideal.IsCoherent) (hd : 1≤Q.d)
    {Y : CMfd.{0} n}(T : BlowupTower X Y)(hT : IsGeoTestTower Q T) :
    let e:=sumExp (fun j=>Q.d-j) Q.d 0
    1≤e ∧ Q.d*e=(barMarked Q).d ∧
      IsGeoTestTower (barMarked Q) T ∧
      (idealPow (geoTransformAlong Q T).ideal e).Le
        (geoTransformAlong (barMarked Q) T).ideal := by
  have hHomEq : homMarkedAlong Q=homMarked Q :=
    homMarkedAlong_eq_homMarked hN (fun _ _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem hI hg)
  obtain ⟨hHT,_hHNT,hForm⟩:=hom_tower Q hN hI hd T hT
  have hInc : (geoTransformAlong Q T).ideal.Le
      (geoTransformAlong (homMarkedAlong Q) T).ideal := by
    rw [hHomEq]
    exact le_of_eq_homSum Q hN hI hd hT hForm
  have hHI : (homMarkedAlong Q).ideal.IsCoherent := by
    rw [hHomEq]
    exact HomogenizedGlueing.isCoherent_homogenizedIdeal hI Q.d
  have hHT' : IsGeoTestTower (homMarkedAlong Q) T := hHomEq.symm ▸ hHT
  obtain ⟨he,hm,hBT,_hE,hPow⟩:=original_coefficient_history_power_le
    (homMarkedAlong Q) hN hHI hd T hHT'
  refine ⟨he,hm,hBT,?_⟩
  intro z f hf
  exact hPow z f ((idealPow_mono hInc _) z f hf)

private theorem power_nonzero (I J : GermIdeal n X) (hI : I.IsCoherent)
    (r : ℕ) (_hr : 0<r) (hPow : (idealPow I r).Le J) (x : X)
    (hNZ : IsNonzeroAlongAt (n:=n) univ I x) :
    IsNonzeroAlongAt (n:=n) univ J x := by
  obtain ⟨f,hf,hFreq⟩:=hNZ
  refine ⟨fun z=>f z^r,hPow x _
    (OrderMultiplicativity.pow_mem_idealPow hf (GermIdeal.IsCoherent.holomorphicAt_mem hI hf) r),?_⟩
  apply hFreq.mono
  rintro z ⟨hz,hne⟩
  exact ⟨hz,pow_ne_zero r hne⟩

private theorem zero_exponent_of_power_le (I J : GermIdeal n X)
    (hI : I.IsCoherent) (hJ : J.IsCoherent) (r : ℕ) (hr : 0<r)
    (hPow : (idealPow I r).Le J) (H : Set X) (hH : IsClosed H)
    (x : X) (hNZ : IsNonzeroAlongAt (n:=n) univ I x)
    (hz : divExpAlong n univ I H x=0) : divExpAlong n univ J H x=0 := by
  rw [divExpAlong_univ] at hz ⊢
  have hIhol : ∀y f,I.mem y f→HolomorphicAt n f y :=
    fun _ _ hf=>GermIdeal.IsCoherent.holomorphicAt_mem hI hf
  have hJhol : ∀y f,J.mem y f→HolomorphicAt n f y :=
    fun _ _ hf=>GermIdeal.IsCoherent.holomorphicAt_mem hJ hf
  by_cases hxH : x∈H
  · have hNot : ¬IsDivNear n J H 1 x := by
      intro hDiv
      have hDivI : IsDivNear n I H 1 x := by
        filter_upwards [hDiv] with z hzH hz
        refine ⟨mem_univ z,?_⟩
        intro f hf
        have hPower := (hzH hz).2 _ (hPow z _ (OrderMultiplicativity.pow_mem_idealPow hf (hIhol z f hf) r))
        have hZero := (vanishesToOrderOn_one_iff (mem_univ z)
          (holomorphicAt_pow (hIhol z f hf) r)).mp hPower
        exact (vanishesToOrderOn_one_iff (mem_univ z) (hIhol z f hf)).mpr
          ((pow_eq_zero_iff (Nat.ne_of_gt hr)).mp hZero)
      have hNotI:=not_isDivNear_divExp_succ hIhol hxH
        (isNonzeroAlongAt_univ_iff.mp hNZ)
      rw [hz] at hNotI
      exact hNotI hDivI
    by_contra hne
    exact hNot ((isDivNear_divExp hJhol x).mono (Nat.one_le_iff_ne_zero.mpr hne))
  · have hNone : ¬∃e,¬IsDivNear n J H (e+1) x := by
      rintro ⟨e,he⟩
      exact he (isDivNear_of_notMem hH hxH (e+1))
    simp only [divExp,dif_neg hNone]

private theorem nonmonomial_iff (I : GermIdeal n X) (hI : I.IsCoherent)
    (E : List (Set X)) (x : X)
    (hzero : ∀i : Fin E.length,divExpAlong n univ I (E.get i) x=0) (f : X→ℂ) :
    (nonmonomialPartAlong n univ I E).mem x f ↔ I.mem x f := by
  have hOne : (monomialPartAlong n univ I E).mem x (fun _=>1) := by
    refine ⟨holomorphicAt_const 1,fun i _ _=>?_⟩
    rw [hzero i,idealPow_zero]
    exact IsInSpanAt.restrict (isInSpanAt_self (holomorphicAt_const 1) (holomorphicAt_const 1))
  constructor
  · intro hf
    obtain ⟨k,s,a,hs,ha,heq⟩:=(hf.2 (fun _=>1) hOne).2
    apply mem_of_isInSpanAt_mem hI
    refine ⟨hf.1,k,s,a,hs,ha,?_⟩
    filter_upwards [heq] with y hy
    simpa only [one_mul] using hy (mem_univ y)
  · intro hf
    exact ⟨GermIdeal.IsCoherent.holomorphicAt_mem hI hf,
      fun a ha=>restrictOn_mul_left ha.1 (le_restrictOn hI x f hf)⟩

private theorem raw_order_of_maximal (Q : MarkedIdeal n X)
    (hN : Q.N=univ) (hI : Q.ideal.IsCoherent)
    (hMax : IsMaximalOrderAlong Q.N Q.ideal Q.d) (x : X)(hx : x∈Q.cosupp)
    (hzero : ∀i : Fin Q.E.length,divExpAlong n univ Q.ideal (Q.E.get i) x=0) :
    nmOrd Q x=Q.d := by
  have hGe (j : ℕ) : x∈ordGe Q j ↔ x∈cosupport n Q.N Q.ideal j := by
    change (x∈Q.N ∧ ∀f,(nonmonomialPartAlong n Q.N Q.ideal Q.E).mem x f→
      VanishesToOrderOn n Q.N x j f) ↔ _
    rw [hN]
    constructor
    · intro h
      exact ⟨h.1,fun f hf=>h.2 f ((nonmonomial_iff Q.ideal hI Q.E x hzero f).mpr hf)⟩
    · intro h
      exact ⟨h.1,fun f hf=>h.2 f ((nonmonomial_iff Q.ideal hI Q.E x hzero f).mp hf)⟩
  have hNot : x∉ordGe Q (Q.d+1) := fun h=>hMax x ((hGe _).mp h)
  refine (nmOrd_le_of_notMem hNot).antisymm ?_
  cases hd : Q.d with
  | zero => exact Nat.zero_le _
  | succ j =>
    have hLow : x∈ordGe Q (j+1) := (hGe _).mpr (hd ▸ hx)
    exact succ_le_nmOrd_of_mem ⟨Q.d,hNot⟩ hLow

private theorem native_stage_centres (W : Set X) :
    ∀{Y : CMfd.{0} n}(T : BlowupTower X Y),ActualHistoricalNativeTowerCentres W T →
      StageCentres (fun P C=>C⊆singularSet (n:=n) (strictTransform n P.proj W)) T
  | _,.refl,_=>trivial
  | _,.step T _ _ _,h=>⟨native_stage_centres W T h.1,h.2⟩

private theorem coefficient_mark_gt {d : ℕ} (hd : 3≤d) :
    d<(Finset.range d).prod (fun j=>d-j) := by
  have hEq : (Finset.range d).prod (fun j=>d-j)=d.factorial := by
    rw [Nat.factorial_eq_prod_range_add_one,
      ←Finset.prod_range_reflect (fun j : ℕ=>j+1) d]
    apply Finset.prod_congr rfl
    intro j hj
    have hjd:=Finset.mem_range.mp hj
    omega
  rw [hEq]
  exact Nat.lt_factorial_self hd

/-- Actual source geometry derives the historical ORIGINAL bar and C²H
orders at their exact product marks. This is not full suffix/CAN transport. -/
theorem actual_native_history_original_bar_order
    {m : ℕ} {Xref : Type} [TopologicalSpace Xref]
    [ChartedSpace (ComplexModel m) Xref] [IsComplexManifold m Xref]
    (hn : 0<n) (Wref : Set Xref) (hWref : IsComplexAnalyticSubset (n:=m) Wref)
    (aref : Xref) (hSing : aref∈singularSet (n:=m) Wref)
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
    {Y : CMfd.{0} n}(T : BlowupTower X Y)(hT : IsGeoTestTower Q T) :
    let B:=barMarked Q
    let C:=coeffMarkedAlong B
    let e:=sumExp (fun j=>Q.d-j) Q.d 0
    let f:=sumExp (fun j=>B.d-j) B.d 0
    1≤e ∧ 1≤f ∧ Q.d*e=B.d ∧ B.d*f=C.d ∧
      B.d=(Finset.range Q.d).prod (fun j=>Q.d-j) ∧
      C.d=(Finset.range B.d).prod (fun j=>B.d-j) ∧
      IsInvDomain n B ∧ IsInvDomain n C ∧ IsGeoTestTower B T ∧ IsGeoTestTower C T ∧
      (geoTransformAlong B T).N=univ ∧ (geoTransformAlong C T).N=univ ∧
      (geoTransformAlong B T).cosupp=(geoTransformAlong Q T).cosupp ∧
      (geoTransformAlong C T).cosupp=(geoTransformAlong Q T).cosupp ∧
      (geoTransformAlong B T).E=(geoTransformAlong Q T).E ∧
      (geoTransformAlong C T).E=(geoTransformAlong Q T).E ∧
      (geoTransformAlong B T).E.length=T.length ∧
      (geoTransformAlong C T).E.length=T.length ∧
      (geoTransformAlong B T).d=B.d ∧ (geoTransformAlong C T).d=C.d ∧
      (idealPow (geoTransformAlong Q T).ideal e).Le (geoTransformAlong B T).ideal ∧
      (idealPow (geoTransformAlong B T).ideal f).Le (geoTransformAlong C T).ideal ∧
      (idealPow (geoTransformAlong Q T).ideal (e*f)).Le (geoTransformAlong C T).ideal ∧
      ∀x∈(geoTransformAlong Q T).cosupp,
        (∀i : Fin (geoTransformAlong B T).E.length,
          divExpAlong n univ (geoTransformAlong B T).ideal ((geoTransformAlong B T).E.get i) x=0) ∧
        (∀i : Fin (geoTransformAlong C T).E.length,
          divExpAlong n univ (geoTransformAlong C T).ideal ((geoTransformAlong C T).E.get i) x=0) ∧
        nmOrd (geoTransformAlong Q T) x=Q.d ∧
        nmOrd (geoTransformAlong B T) x=B.d ∧
        nmOrd (geoTransformAlong C T) x=C.d ∧
        B.d*nmOrd (geoTransformAlong Q T) x=Q.d*nmOrd (geoTransformAlong B T) x ∧
        C.d*nmOrd (geoTransformAlong B T) x=B.d*nmOrd (geoTransformAlong C T) x ∧
        (3≤Q.d → ∀q : ℕ,(invFamily hn (q+1)).inv Q T x<
          (invFamily hn (q+1)).inv B T x) := by
  let B:=barMarked Q
  let C:=coeffMarkedAlong B
  let e:=sumExp (fun j=>Q.d-j) Q.d 0
  let f:=sumExp (fun j=>B.d-j) B.d 0
  obtain ⟨he,hMe,hBT,hPB⟩:=original_bar_power_le Q hQN hQ.isWellFormed.isCoherent hQ.one_le_d T hT
  have hBWF:=isWellFormed_barMarked Q hQ.isWellFormed
  have hBN : B.N=univ := hQN
  have hBd : 1≤B.d := ContactIndependenceAlong.one_le_coeffMarkedAlong_d _
  obtain ⟨hf,hDf,hCT,_hCE,hPC⟩:=original_coefficient_history_power_le B hBN hBWF.isCoherent hBd T hBT
  obtain ⟨hBNT,hBIT,_⟩:=MarkedIdeals.MarkedIdeal.pullback_eq_mul_geoTransformAlong B hBN hBWF.isCoherent T hBT
  have hCWF : C.IsWellFormed :=
    ⟨hBWF.isClosedSubmanifold_N,
      isCoherent_coeffMarkedAlong hBWF.isCoherent hBWF.isClosedSubmanifold_N,
      hBWF.isSNCDivisor,hBWF.isTransverse⟩
  have hCN : C.N=univ := hBN
  have hBP0 := (original_bar_power_le Q hQN hQ.isWellFormed.isCoherent hQ.one_le_d
    (.refl : BlowupTower X X) trivial).2.2.2
  have hBDom : IsInvDomain n B := by
    refine ⟨hBWF,hQ.dimLE,hBd,?_⟩
    intro x hx
    exact hBN.symm ▸ power_nonzero Q.ideal B.ideal hQ.isWellFormed.isCoherent e (by omega) hBP0 x
      (hQN ▸ hQ.isNonzeroAlongAt x hx)
  have hCP0 := (original_coefficient_history_power_le B hBN hBWF.isCoherent hBd
    (.refl : BlowupTower X X) trivial).2.2.2.2
  have hCDom : IsInvDomain n C := by
    refine ⟨hCWF,hQ.dimLE,ContactIndependenceAlong.one_le_coeffMarkedAlong_d _,?_⟩
    intro x hx
    exact hCN.symm ▸ power_nonzero B.ideal C.ideal hBWF.isCoherent f (by omega) hCP0 x
      (hBN ▸ hBDom.isNonzeroAlongAt x hx)
  obtain ⟨hCNT,hCIT,_⟩:=MarkedIdeals.MarkedIdeal.pullback_eq_mul_geoTransformAlong C hCN hCWF.isCoherent T hCT
  have hCB : (geoTransformAlong B T).cosupp=(geoTransformAlong Q T).cosupp :=
    ((StepOneBridge.barMarked_wEquiv Q hQ).2 T).2 hBT
  have hCC : (geoTransformAlong C T).cosupp=(geoTransformAlong Q T).cosupp :=
    ((coeffAlong_tower B hBWF.isClosedSubmanifold_N hBWF.isCoherent hBd T).2 hBT).trans hCB
  have hEB : (geoTransformAlong B T).E=(geoTransformAlong Q T).E :=
    E_geoTransformAlong_eq (𝔪:=B) (𝔫:=Q) rfl T
  have hEC : (geoTransformAlong C T).E=(geoTransformAlong Q T).E :=
    E_geoTransformAlong_eq (𝔪:=C) (𝔫:=Q) rfl T
  have hMB : B.d=(Finset.range Q.d).prod (fun j=>Q.d-j) := rfl
  have hMC : C.d=(Finset.range B.d).prod (fun j=>B.d-j) := rfl
  obtain ⟨⟨_hWT,hNT,hIT,_hMarkT,_hUpperT,_hCutT,hAtT,_hSingT⟩,hCentres⟩:=
    actual_native_given_test_tower_state Wref hWref aref hSing W hW Q hQN hQ.isWellFormed.isCoherent
      S a w hWords hPositive hOwn hQMark hCut hUpper hAt T hT
  have hStage:=native_stage_centres W T hCentres
  have hDomT:=isInvDomain_geoTransformAlong hQ T hT
  have hQMax:=actual_native_current_maximal_order S hV a w hWords W Q hQN
    hQ.isWellFormed.isCoherent hQMark hAt
  have hMaxQ:=isMaximalOrderAlong_geoTransformAlong hQ.isWellFormed.isClosedSubmanifold_N
    hQ.isWellFormed.isCoherent hQMax T hT
  have hBMax:=isMaximalOrderAlong_barMarked Q hQ.isWellFormed hQ.one_le_d hQMax
  have hMaxB:=isMaximalOrderAlong_geoTransformAlong hBWF.isClosedSubmanifold_N hBWF.isCoherent hBMax T hBT
  have hCMax:=IsMaximalOrderAlong.coeffMarkedAlong (𝔪:=B) hBWF.isClosedSubmanifold_N.2
    (fun _ _ hg=>GermIdeal.IsCoherent.holomorphicAt_mem hBWF.isCoherent hg) hBd hBMax
  have hMaxC:=isMaximalOrderAlong_geoTransformAlong hCWF.isClosedSubmanifold_N hCWF.isCoherent hCMax T hCT
  have hPCB : (idealPow (geoTransformAlong Q T).ideal (e*f)).Le (geoTransformAlong C T).ideal := by
    rw [←idealPow_idealPow hIT e f]
    intro z g hg
    exact hPC z g ((idealPow_mono hPB f) z g hg)
  refine ⟨he,hf,hMe,hDf,hMB,hMC,hBDom,hCDom,hBT,hCT,hBNT,hCNT,hCB,hCC,hEB,hEC,?_,?_,
    d_geoTransformAlong B T,d_geoTransformAlong C T,hPB,hPC,hPCB,?_⟩
  · rw [hEB,length_E_geoTransformAlong,hQE,List.length_nil,Nat.zero_add]
  · rw [hEC,length_E_geoTransformAlong,hQE,List.length_nil,Nat.zero_add]
  intro x hx
  have hNZ : IsNonzeroAlongAt (n:=n) univ (geoTransformAlong Q T).ideal x :=
    hNT ▸ hDomT.isNonzeroAlongAt x (hNT.symm ▸ mem_univ x)
  have hZeroQ (i : Fin (geoTransformAlong Q T).E.length) :
      divExpAlong n univ (geoTransformAlong Q T).ideal ((geoTransformAlong Q T).E.get i) x=0 := by
    apply actual_native_born_weighted_exponent_zero Q W hW T hStage hIT
      hDomT.isWellFormed.isSNCDivisor S a w hPositive x hNZ (hAtT x hx)
    simpa only [hQE,List.length_nil,List.drop_zero] using (List.get_mem (geoTransformAlong Q T).E i)
  have hZeroB (i : Fin (geoTransformAlong B T).E.length) :
      divExpAlong n univ (geoTransformAlong B T).ideal ((geoTransformAlong B T).E.get i) x=0 := by
    let H:=(geoTransformAlong B T).E.get i
    have hHQ : H∈(geoTransformAlong Q T).E := hEB ▸ List.get_mem (geoTransformAlong B T).E i
    obtain ⟨j,hj⟩:=List.mem_iff_get.mp hHQ
    exact zero_exponent_of_power_le _ _ hIT hBIT e (by omega) hPB H
      (hDomT.isWellFormed.isSNCDivisor.1 H hHQ) x hNZ (hj ▸ hZeroQ j)
  have hNZB:=power_nonzero _ _ hIT e (by omega) hPB x hNZ
  have hZeroC (i : Fin (geoTransformAlong C T).E.length) :
      divExpAlong n univ (geoTransformAlong C T).ideal ((geoTransformAlong C T).E.get i) x=0 := by
    let H:=(geoTransformAlong C T).E.get i
    have hHB : H∈(geoTransformAlong B T).E := (hEC.trans hEB.symm) ▸ List.get_mem (geoTransformAlong C T).E i
    obtain ⟨j,hj⟩:=List.mem_iff_get.mp hHB
    have hHQ : H∈(geoTransformAlong Q T).E := hEB ▸ hHB
    exact zero_exponent_of_power_le _ _ hBIT hCIT f (by omega) hPC H
      (hDomT.isWellFormed.isSNCDivisor.1 H hHQ) x hNZB (hj ▸ hZeroB j)
  have hRawQ : nmOrd (geoTransformAlong Q T) x=Q.d :=
    (raw_order_of_maximal _ hNT hIT hMaxQ x hx hZeroQ).trans (d_geoTransformAlong Q T)
  have hRawB : nmOrd (geoTransformAlong B T) x=B.d :=
    (raw_order_of_maximal _ hBNT hBIT hMaxB x (hCB.symm ▸ hx) hZeroB).trans (d_geoTransformAlong B T)
  have hRawC : nmOrd (geoTransformAlong C T) x=C.d :=
    (raw_order_of_maximal _ hCNT hCIT hMaxC x (hCC.symm ▸ hx) hZeroC).trans (d_geoTransformAlong C T)
  refine ⟨hZeroB,hZeroC,hRawQ,hRawB,hRawC,?_,?_,?_⟩
  · rw [hRawQ,hRawB,Nat.mul_comm]
  · rw [hRawB,hRawC,Nat.mul_comm]
  intro hLarge q
  have hStrict : Q.d<B.d := hMB.symm ▸ coefficient_mark_gt hLarge
  apply Prod.Lex.toLex_lt_toLex.mpr
  exact Or.inl (show nmOrd (geoTransformAlong Q T) x<nmOrd (geoTransformAlong B T) x from
    by rw [hRawQ,hRawB];exact hStrict)

end
end Hironaka.HironakaActualHistoricalOriginalBarOrder
