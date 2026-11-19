import Hironaka.Resolution.HironakaActualOriginalCoefficientHistoryOrder
import Hironaka.Resolution.HironakaActualHistoricalOriginalZeroRegime

/-! ORIGINAL coefficient order thresholds along the SAME actual proper carrier.
The chosen contact carrier is retained; no current coefficient reset or raw
nonmonomial/CAN comparison. Blueprint FIRST. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualOriginalCoefficientHistoryAlong
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan InvertibleIdealQuotient GermIdealOrder IdealOrderArithmetic IdealWeightPowers
  DerivativeIdealAlong TangentDirectionAlong HomogenizedIdealAlong HomogenizedIdealAlongTower
  CoefficientIdeal CoefficientIdealRestriction HomogenizedGlueing MarkedIdealOperationsAlong
  DivisorExponentAlong CompanionReductionAlong
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  ResolutionInvariantSpec StepOneValue StepOneValueMasked StepOneRegime BoundaryCount
  CodimOneSupportAlong HironakaActualHistoricalOriginalZeroRegime
  HironakaSharpOriginalProductTraceOrder NonmonomialOrderLocal
  HironakaEmbeddedAnalytic
  CompanionRebase CompanionReductionAlong CompanionOpen GeneralValue
  InvDomainCompanion InvDomainTowerAlong NonmonomialOrderTail NonmonomialOrderRegime
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen StepOneLowerDomain StepOneWellFounded

variable {n : ℕ} {X : CMfd.{0} n}

private theorem hol {Y : CMfd.{0} n} {I : GermIdeal n Y} (hI : I.IsCoherent) :
    ∀x f,I.mem x f→HolomorphicAt n f x :=
  fun _ _ hf=>GermIdeal.IsCoherent.holomorphicAt_mem hI hf

private theorem exponent_inequality {M e p i r : ℕ} (hM : 0<M)
    (hr : M≤r) (hi : i<M) (hBalance : (M-i)*p=M*e) : r*e≤(r-i)*p := by
  have hLe : M*e≤M*p := by
    rw [←hBalance]
    exact Nat.mul_le_mul_right p (Nat.sub_le M i)
  have hep : e≤p := by
    by_contra h
    have hlt : M*p<M*e:=Nat.mul_lt_mul_of_pos_left (Nat.lt_of_not_ge h) hM
    exact Nat.not_lt_of_ge hLe hlt
  calc
    r*e=M*e+(r-M)*e:=by rw [←Nat.add_mul,Nat.add_sub_of_le hr]
    _=(M-i)*p+(r-M)*e:=by rw [hBalance]
    _≤(M-i)*p+(r-M)*p:=Nat.add_le_add_left (Nat.mul_le_mul_left (r-M) hep) _
    _=(r-i)*p:=by rw [←Nat.add_mul];congr 1;omega

/-- EVERY threshold above the ORIGINAL mark along the SAME transformed
carrier, which may be the proper original contact carrier. -/
theorem original_coefficient_history_threshold_along (Q : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n Q.N) (hI : Q.ideal.IsCoherent) (hd : 1≤Q.d)
    {Y : CMfd.{0} n}(T : BlowupTower X Y)(hT : IsGeoTestTower Q T)
    (r : ℕ)(hr : Q.d≤r) :
    let e:=sumExp (fun j=>Q.d-j) Q.d 0
    cosupport n (geoTransformAlong Q T).N (geoTransformAlong (coeffMarkedAlong Q) T).ideal (r*e)=
      cosupport n (geoTransformAlong Q T).N (geoTransformAlong Q T).ideal r := by
  let e:=sumExp (fun j=>Q.d-j) Q.d 0
  let F:=fun i=>geoTransformAlong (derivMarkedAlong Q i) T
  have he : 1≤e:=one_le_sumExp (fun j hj=>by omega) 0
  have hMark : Q.d*e=(Finset.range Q.d).prod (fun j=>Q.d-j):=by
    simpa only [Nat.sub_zero] using mul_sumExp (fun j=>Q.d-j) (show 0<Q.d by omega)
  have hAll : ∀i<Q.d,IsGeoTestTower (derivMarkedAlong Q i) T:=
    fun i hi=>(inclusions_tower_along Q hN hI hi.le T hT).1
  obtain ⟨hWhole,_hC,_hFam⟩:=(geoTransformAlong_msum_along
    (fun i=>derivMarkedAlong Q i) hd (isSubmanifoldFamily_derivMarkedAlong hN hI) T).2 hAll
  have hWholeN : (geoTransformAlong (coeffMarkedAlong Q) T).N=(geoTransformAlong Q T).N :=
    hWhole.N_eq
  have hLe:=hWhole.le
  have hGe:=hWhole.ge
  change RestrictedIdealWeight.RestrictLe (geoTransformAlong (coeffMarkedAlong Q) T).N
    (geoTransformAlong (coeffMarkedAlong Q) T).ideal (msum F Q.d).ideal at hLe
  change RestrictedIdealWeight.RestrictLe (geoTransformAlong (coeffMarkedAlong Q) T).N
    (msum F Q.d).ideal (geoTransformAlong (coeffMarkedAlong Q) T).ideal at hGe
  rw [hWholeN] at hLe hGe
  have hSum (q : ℕ) :
      cosupport n (geoTransformAlong Q T).N (geoTransformAlong (coeffMarkedAlong Q) T).ideal q=
        cosupport n (geoTransformAlong Q T).N (msum F Q.d).ideal q :=
    Subset.antisymm (cosupport_subset_of_restrictLe hGe q) (cosupport_subset_of_restrictLe hLe q)
  obtain ⟨_h0,_hN0,_hE0,hNT,hA,_hD0,_hInc0⟩:=
    inclusions_tower_along Q hN hI (show 0≤Q.d by omega) T hT
  change cosupport n (geoTransformAlong Q T).N
    (geoTransformAlong (coeffMarkedAlong Q) T).ideal (r*e)=_
  rw [hSum]
  change cosupport n (geoTransformAlong Q T).N
    (finSumIdeal (fun i=>idealPow (F i).ideal (sumExp (fun j=>(F j).d) Q.d i)) Q.d) (r*e)=_
  ext y
  constructor
  · intro hy
    have hZero:=((mem_cosupport_finSumIdeal
      (fun _ _ _ _ h=>holomorphicAt_of_mem_idealPow h)).mp hy).2 0 hd
    have hPow : y∈cosupport n (geoTransformAlong Q T).N
        (idealPow (geoTransformAlong Q T).ideal e) (r*e):=by
      simpa only [F,d_geoTransformAlong,derivMarkedAlong_d,derivMarkedAlong_zero] using hZero
    rwa [cosupport_idealPow_mul_eq_along hNT.2 (hol hA) he r] at hPow
  · intro hy
    apply (mem_cosupport_finSumIdeal (fun _ _ _ _ h=>holomorphicAt_of_mem_idealPow h)).mpr
    refine ⟨hy.1,?_⟩
    intro i hi
    obtain ⟨_hTest,_hNi,_hEi,_hNT,_hCA,_hCI,hDeriv⟩:=
      inclusions_tower_along Q hN hI hi.le T hT
    have hCurrent : y∈cosupport n (geoTransformAlong Q T).N
        (iterDerivIdealAlong (geoTransformAlong Q T).N (geoTransformAlong Q T).ideal i) (r-i):=
      cosupport_add_subset_cosupport_iterDerivIdealAlong (hol hA) (r-i) i
        (by simpa only [Nat.sub_add_cancel (show i≤r by omega)] using hy)
    have hOriginal : y∈cosupport n (geoTransformAlong Q T).N (F i).ideal (r-i):=
      cosupport_subset_of_restrictLe hDeriv (r-i) hCurrent
    let p:=sumExp (fun j=>Q.d-j) Q.d i
    have hP : y∈cosupport n (geoTransformAlong Q T).N (idealPow (F i).ideal p) ((r-i)*p):=
      cosupport_subset_cosupport_idealPow (r-i) p hOriginal
    have hBalance : (Q.d-i)*p=Q.d*e:=(mul_sumExp (fun j=>Q.d-j) hi).trans hMark.symm
    have hBound : r*e≤(r-i)*p:=exponent_inequality (by omega) hr hi hBalance
    simpa only [F,d_geoTransformAlong,derivMarkedAlong_d] using cosupport_anti hBound hP

private theorem zeroth_order (Q : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n Q.N) (hI : Q.ideal.IsCoherent) (hd : 1≤Q.d)
    {Y : CMfd.{0} n}(T : BlowupTower X Y)(hT : IsGeoTestTower Q T)(q : ℕ) :
    cosupport n (geoTransformAlong Q T).N (geoTransformAlong (coeffMarkedAlong Q) T).ideal q ⊆
      cosupport n (geoTransformAlong Q T).N
        (idealPow (geoTransformAlong Q T).ideal (sumExp (fun j=>Q.d-j) Q.d 0)) q := by
  have hAll : ∀i<Q.d,IsGeoTestTower (derivMarkedAlong Q i) T:=
    fun i hi=>(inclusions_tower_along Q hN hI hi.le T hT).1
  obtain ⟨hWhole,_hC,_hFam⟩:=(geoTransformAlong_msum_along
    (fun i=>derivMarkedAlong Q i) hd (isSubmanifoldFamily_derivMarkedAlong hN hI) T).2 hAll
  have hWholeN : (geoTransformAlong (coeffMarkedAlong Q) T).N=(geoTransformAlong Q T).N:=hWhole.N_eq
  have hGe:=hWhole.ge
  change RestrictedIdealWeight.RestrictLe (geoTransformAlong (coeffMarkedAlong Q) T).N
    (msum (fun i=>geoTransformAlong (derivMarkedAlong Q i) T) Q.d).ideal
    (geoTransformAlong (coeffMarkedAlong Q) T).ideal at hGe
  rw [hWholeN] at hGe
  intro y hy
  have hSum:=cosupport_subset_of_restrictLe hGe q hy
  have hZero:=((mem_cosupport_finSumIdeal
    (fun _ _ _ _ h=>holomorphicAt_of_mem_idealPow h)).mp hSum).2 0 hd
  simpa only [d_geoTransformAlong,derivMarkedAlong_d,derivMarkedAlong_zero] using hZero

/-- Actual ENat ORDINARY order of the ORIGINAL coefficient along the SAME
possibly proper carrier. The true order can exceed the ORIGINAL literal mark. -/
theorem original_coefficient_history_order_along (Q : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n Q.N) (hI : Q.ideal.IsCoherent) (hd : 1≤Q.d)
    {Y : CMfd.{0} n}(T : BlowupTower X Y)(hT : IsGeoTestTower Q T)
    (y : Y)(hy : y∈(geoTransformAlong Q T).cosupp) :
    let e:=sumExp (fun j=>Q.d-j) Q.d 0
    GermIdealOrder.order n (geoTransformAlong Q T).N (geoTransformAlong (coeffMarkedAlong Q) T).ideal y=
      (e : ℕ∞)*GermIdealOrder.order n (geoTransformAlong Q T).N (geoTransformAlong Q T).ideal y := by
  let N:=(geoTransformAlong Q T).N
  let A:=(geoTransformAlong Q T).ideal
  let B:=(geoTransformAlong (coeffMarkedAlong Q) T).ideal
  let e:=sumExp (fun j=>Q.d-j) Q.d 0
  obtain ⟨_h0,_hN0,_hE0,hNT,hA,_hD0,_hInc0⟩:=
    inclusions_tower_along Q hN hI (show 0≤Q.d by omega) T hT
  have hCT:=(coeffAlong_tower Q hN hI hd T).1.mpr hT
  have hB : B.IsCoherent:=
    (inclusions_tower_along (coeffMarkedAlong Q) hN (isCoherent_coeffMarkedAlong hI hN)
      (show 0≤(coeffMarkedAlong Q).d by omega) T hCT).2.2.2.2.1
  have he : 1≤e:=one_le_sumExp (fun j hj=>by omega) 0
  have hyM : y∈cosupport n N A Q.d:=by
    simpa only [MarkedIdeal.cosupp,d_geoTransformAlong] using hy
  have hThresh (r : ℕ)(hr : Q.d≤r) :
      y∈cosupport n N B (r*e) ↔ y∈cosupport n N A r:=by
    rw [original_coefficient_history_threshold_along Q hN hI hd T hT r hr]
  by_cases hTop : GermIdealOrder.order n N A y=⊤
  · have hBTop : GermIdealOrder.order n N B y=⊤:=by
      apply ENat.eq_top_iff_forall_ge.mpr
      intro q
      have hSource : OrderGE n N A y (q+Q.d):=
        (le_order_iff (hol hA y)).mp (by rw [hTop];exact le_top)
      have hTarget:=((hThresh (q+Q.d) (by omega)).mpr ⟨hyM.1,hSource⟩).2
      have hLower : ((q+Q.d)*e : ℕ∞)≤GermIdealOrder.order n N B y:=
        (le_order_iff (hol hB y)).mpr hTarget
      have hq : q≤(q+Q.d)*e:=by nlinarith
      exact (show (q : ℕ∞)≤((q+Q.d)*e : ℕ∞) by exact_mod_cast hq).trans hLower
    have he0 : (e : ℕ∞)≠0:=by exact_mod_cast (show e≠0 by omega)
    change GermIdealOrder.order n N B y=(e : ℕ∞)*GermIdealOrder.order n N A y
    rw [hBTop,hTop,ENat.mul_top he0]
  · obtain ⟨s,hs⟩:=ENat.ne_top_iff_exists.mp hTop
    have hM : Q.d≤s:=by
      have hLe:=(le_order_iff (hol hA y)).mpr hyM.2
      rw [←hs] at hLe
      exact_mod_cast hLe
    have hAtS : OrderGE n N A y s:=
      (le_order_iff (hol hA y)).mp (by rw [←hs])
    have hCAtS:=((hThresh s hM).mpr ⟨hyM.1,hAtS⟩).2
    have hNot : y∉cosupport n N A (s+1):=by
      intro h
      have hLe:=(le_order_iff (hol hA y)).mpr h.2
      rw [←hs] at hLe
      exact Nat.not_succ_le_self s (by exact_mod_cast hLe)
    obtain ⟨f,hf,hNotf⟩:=exists_not_vanishesToOrderOn_of_notMem hyM.1 hNot
    obtain ⟨k,hk⟩:=hNT.2 y hyM.1
    obtain ⟨ρ,hρ⟩:=exists_isLocalRetraction hk
    have hfr : ¬(idealPow (pointIdeal n y) (s+1)).mem y (f ∘ ρ):=
      fun h=>hNotf (hρ.vanishesToOrderOn_iff.mpr h)
    have hNotC : ¬OrderGE n N B y (e*s+1):=by
      intro h
      have hPow:=zeroth_order Q hN hI hd T hT (e*s+1) ⟨hyM.1,h⟩
      have hMember:=OrderMultiplicativity.pow_mem_idealPow hf (hol hA y f hf) e
      have hV:=hρ.vanishesToOrderOn_iff.mp (hPow.2 _ hMember)
      exact CompanionReduction.pow_notMem_idealPow (hρ.holomorphicAt_comp (hol hA y f hf)) hfr e hV
    have hUpper : GermIdealOrder.order n N B y≤((e*s : ℕ) : ℕ∞):=by
      apply ENat.lt_natCast_add_one_iff.mp
      apply lt_of_not_ge
      intro h
      exact hNotC ((le_order_iff (hol hB y)).mp (by simpa only [Nat.cast_add,Nat.cast_one] using h))
    have hLower : ((s*e : ℕ) : ℕ∞)≤GermIdealOrder.order n N B y:=
      (le_order_iff (hol hB y)).mpr hCAtS
    have hEq : GermIdealOrder.order n N B y=((e*s : ℕ) : ℕ∞):=
      le_antisymm hUpper (by simpa only [Nat.mul_comm] using hLower)
    change GermIdealOrder.order n N B y=(e : ℕ∞)*GermIdealOrder.order n N A y
    rw [←hs,←Nat.cast_mul]
    exact hEq

private theorem initial_order (L : MarkedIdeal n X) {k : ℕ}
    (hL : IsInvDomain k L) (hE : L.E=[]) (x : X)(hx : x∈L.cosupp) :
    L.d≤nmOrd L x ∧ GermIdealOrder.order n L.N L.ideal x=(nmOrd L x : ℕ∞) := by
  have hGe (r : ℕ) : ordGe L r=cosupport n L.N L.ideal r:=by
    change cosupport n L.N (MonomialPartAlong.nonmonomialPartAlong n L.N L.ideal L.E) r=_
    rw [hE,nonmonomialPartAlong_nil_eq_restrictOn]
    exact Subset.antisymm
      (cosupport_subset_of_restrictLe
        (RestrictedIdealExtension.restrictLe_self_restrictOn hL.isWellFormed.isCoherent) r)
      (cosupport_subset_of_restrictLe RestrictedIdealExtension.restrictLe_restrictOn r)
  have hDict:=mem_ordGe_iff hL.isWellFormed hL.isNonzeroAlongAt (L.cosupp_subset_N hx)
  have hMark : L.d≤nmOrd L x:= (hDict L.d).mp ((hGe L.d).symm ▸ hx)
  refine ⟨hMark,le_antisymm ?_ ?_⟩
  · apply ENat.lt_natCast_add_one_iff.mp
    apply lt_of_not_ge
    intro h
    have hHigh : x∈cosupport n L.N L.ideal (nmOrd L x+1):=
      ⟨L.cosupp_subset_N hx,(le_order_iff (hol hL.isWellFormed.isCoherent x)).mp
        (by simpa only [Nat.cast_add,Nat.cast_one] using h)⟩
    have hBad:=(hDict (nmOrd L x+1)).mp ((hGe _).symm ▸ hHigh)
    omega
  · exact (le_order_iff (hol hL.isWellFormed.isCoherent x)).mpr
      ((hGe _ ▸ (hDict (nmOrd L x)).mpr le_rfl).2)

/-- Literal original lowerMarkedB, its SAME chosen proper carrier and mask,
and its genuine initial order, which may exceed the original literal mark. -/
theorem original_lower_coefficient_history_along (hn : 0<n) (Q : MarkedIdeal n X)
    {k : ℕ}(hQ : IsInvDomain k Q) (hN : Q.N=univ) (hE : Q.E=[])
    (hMax : IsMaximalOrderAlong Q.N Q.ideal Q.d)
    (W : Set X)(hW : IsComplexAnalyticSubset (n:=n) W)
    (hSing : Q.cosupp⊆singularSet (n:=n) W)(a : X)(ha : a∈Q.cosupp) :
    ∃hm : a∈maskB Q (.refl : BlowupTower X X) a,
      let L : MarkedIdeal n (CMfd.of (n:=n) (maskB Q (.refl : BlowupTower X X) a)):=
        lowerMarkedB Q (.refl : BlowupTower X X) a
      let x : maskB Q (.refl : BlowupTower X X) a:=⟨a,hm⟩
      let μ:=nmOrd L x
      IsInvDomain (k-1) L ∧ L.E=[] ∧ L.d=(coeffMarkedAlong (barMarked Q)).d ∧
      x∈L.cosupp ∧ L.d≤μ ∧ GermIdealOrder.order n L.N L.ideal x=(μ : ℕ∞) ∧
      GermIdealOrder.order n L.N (coeffMarkedAlong L).ideal x=
        ((sumExp (fun j=>L.d-j) L.d 0 : ℕ) : ℕ∞)*(μ : ℕ∞) ∧
      ∀{Y : CMfd.{0} n}(T : BlowupTower (CMfd.of (n:=n) (maskB Q (.refl : BlowupTower X X) a)) Y),
        IsGeoTestTower L T →
        (∀r,L.d≤r →
          cosupport n (geoTransformAlong L T).N (geoTransformAlong (coeffMarkedAlong L) T).ideal
            (r*sumExp (fun j=>L.d-j) L.d 0)=
          cosupport n (geoTransformAlong L T).N (geoTransformAlong L T).ideal r) ∧
        ∀y∈(geoTransformAlong L T).cosupp,
          GermIdealOrder.order n (geoTransformAlong L T).N
            (geoTransformAlong (coeffMarkedAlong L) T).ideal y=
          ((sumExp (fun j=>L.d-j) L.d 0 : ℕ) : ℕ∞)*
            GermIdealOrder.order n (geoTransformAlong L T).N (geoTransformAlong L T).ideal y := by
  have hEq:=HomogenizedIdealAlongTower.coeff_homAlong_wEquiv Q
    hQ.isWellFormed.isClosedSubmanifold_N hQ.isWellFormed.isCoherent hQ.one_le_d
  have hCos : (barMarked Q).cosupp=Q.cosupp:=
    (hEq.2 (.refl : BlowupTower X X)).2 trivial
  have hZero:=codimOnePartAlong_eq_empty_of_singular_cosupp W hW (barMarked Q)
    hN (fun x hx=>hSing (hCos ▸ hx))
  have hLevel : level Q (.refl : BlowupTower X X) a=0:=by
    simp only [level,origMembers,hE,List.length_nil,List.take_zero]
    rfl
  have hNot : ¬IsSpecial Q (.refl : BlowupTower X X) a:=by
    rintro (⟨_hL,hZ⟩ | ⟨hPos,_hMember⟩)
    · exact (hZero ▸ hZ : a∈(∅ : Set X)).elim
    · rw [hLevel] at hPos
      omega
  have haBar : a∈(geoTransformAlong (barMarked Q) (.refl : BlowupTower X X)).cosupp:=hCos.symm ▸ ha
  obtain ⟨hm,hDom⟩:=mem_lowerMask_and_isInvDomain_M Q hQ.isWellFormed hQ.one_le_d hn
    hMax hQ.dimLE (.refl : BlowupTower X X) trivial haBar (show stepRegime Q 0 .refl a from ⟨hLevel,hNot⟩)
  let V:=maskB Q (.refl : BlowupTower X X) a
  let L : MarkedIdeal n (CMfd.of (n:=n) V):=lowerMarkedB Q (.refl : BlowupTower X X) a
  let x : V:=⟨a,hm⟩
  change IsInvDomain (k-1) L at hDom
  have hEmpty : L.E=[]:=by
    change Q.E.map ((Subtype.val : V→X) ⁻¹' ·)=[]
    rw [hE,List.map_nil]
  have hLCos:=(StepOneCompare.isGeoTestTower_cosupp_lowerMarkedB Q hQ.isWellFormed
    hQ.one_le_d hMax (.refl : BlowupTower X X) (.refl : BlowupTower X X) trivial haBar).2
  have hx : x∈L.cosupp:=by
    change x∈(geoTransformAlong L (restrict V (.refl : BlowupTower X X))).cosupp
    rw [hLCos]
    exact haBar
  obtain ⟨hμ,hOrder⟩:=initial_order L hDom hEmpty x hx
  have hCoeff:=original_coefficient_history_order_along L hDom.isWellFormed.isClosedSubmanifold_N
    hDom.isWellFormed.isCoherent hDom.one_le_d (.refl : BlowupTower (CMfd.of (n:=n) V) (CMfd.of (n:=n) V))
    trivial x hx
  change GermIdealOrder.order n L.N (coeffMarkedAlong L).ideal x=
    ((sumExp (fun j=>L.d-j) L.d 0 : ℕ) : ℕ∞)*GermIdealOrder.order n L.N L.ideal x at hCoeff
  rw [hOrder] at hCoeff
  refine ⟨hm,hDom,hEmpty,rfl,hx,hμ,hOrder,hCoeff,?_⟩
  intro Y T hT
  exact ⟨fun r hr=>original_coefficient_history_threshold_along L hDom.isWellFormed.isClosedSubmanifold_N
      hDom.isWellFormed.isCoherent hDom.one_le_d T hT r hr,
    fun y hy=>original_coefficient_history_order_along L hDom.isWellFormed.isClosedSubmanifold_N
      hDom.isWellFormed.isCoherent hDom.one_le_d T hT y hy⟩

private theorem companion_point (hn : 0<n) (P : MarkedIdeal n X) {k q : ℕ}
    (hP : IsInvDomain k P)(hq : 1≤q)(hBound : ∀x∈P.cosupp,x∉ordGe P (q+1))
    {Y : CMfd.{0} n}(T : BlowupTower X Y)(hT : IsGeoTestTower (companionOf n P q) T)
    (y : Y)(hy : y∈(geoTransformAlong (companionOf n P q) T).cosupp) : OrdRegime P q T y := by
  obtain ⟨hPT,hUpper,hLower⟩:=companionOf_tower_facts hn hP hq hBound T hT
  obtain ⟨hGe,hCos⟩:=hLower hy
  have hCurrent:=isInvDomain_geoTransformAlong hP T hPT
  refine ⟨hCos,(nmOrd_le_of_notMem (hUpper y hCos)).antisymm ?_⟩
  exact (mem_ordGe_iff hCurrent.isWellFormed hCurrent.isNonzeroAlongAt
    ((geoTransformAlong P T).cosupp_subset_N hCos) q).mp hGe

private theorem companion_run (hn : 0<n) (P : MarkedIdeal n X) {k q : ℕ}
    (hP : IsInvDomain k P)(hq : 1≤q)(hBound : ∀x∈P.cosupp,x∉ordGe P (q+1)) :
    ∀{Y : CMfd.{0} n}(T : BlowupTower X Y),IsGeoTestTower (companionOf n P q) T →
      ∀y∈(geoTransformAlong (companionOf n P q) T).cosupp,
        regimeRun (OrdRegime P q) T y=T.length
  | _,.refl,_,_,_=>rfl
  | _,.step T C π hπ,hT,y,hy=>by
    have hJ:=isInvDomain_companionAlong hn hP hq
    have hp:=proj_mem_cosupp_step hJ.isWellFormed.isClosedSubmanifold_N
      hJ.isWellFormed.isCoherent T C π hπ hT hy
    rw [regimeRun_step_of (OrdRegime P q) T C π hπ
      (companion_point hn P hP hq hBound T hT.1 (π y) hp),
      companion_run hn P hP hq hBound T hT.1 (π y) hp]
    rfl

/-- The actual ORIGINAL lower record is normalized at its genuine initial μ,
with proper carrier saturation, and retains the SAME full companion-test clocks. -/
theorem original_lower_normalized_history (hn : 0<n) (Q : MarkedIdeal n X)
    {k : ℕ}(hQ : IsInvDomain k Q) (hN : Q.N=univ) (hE : Q.E=[])
    (hMax : IsMaximalOrderAlong Q.N Q.ideal Q.d)
    (W : Set X)(hW : IsComplexAnalyticSubset (n:=n) W)
    (hSing : Q.cosupp⊆singularSet (n:=n) W)(a : X)(ha : a∈Q.cosupp) :
    ∃hm : a∈maskB Q (.refl : BlowupTower X X) a,
      let L : MarkedIdeal n (CMfd.of (n:=n) (maskB Q (.refl : BlowupTower X X) a)):=
        lowerMarkedB Q (.refl : BlowupTower X X) a
      let x : maskB Q (.refl : BlowupTower X X) a:=⟨a,hm⟩
      let μ:=nmOrd L x
      let U:=ordMask L μ
      let P : MarkedIdeal n (CMfd.of (n:=n) U):=
        MarkedIdeal.pullback (Subtype.val : U→maskB Q (.refl : BlowupTower X X) a) L
      let J:=companionOf n (M:=CMfd.of (n:=n) U) P μ
      x∈U ∧ IsInvDomain (k-1) J ∧ IsMaximalOrderAlong J.N J.ideal J.d ∧
      J.N=P.N ∧ J.E=[] ∧ J.d=μ ∧ J.ideal=RestrictedIdealExtension.restrictOn n P.N P.ideal ∧
      HEq J (compAt L μ (.refl : BlowupTower (CMfd.of (n:=n) (maskB Q (.refl : BlowupTower X X) a))
        (CMfd.of (n:=n) (maskB Q (.refl : BlowupTower X X) a)))) ∧
      ∀{Y : CMfd.{0} n}(T : BlowupTower (CMfd.of (n:=n) U) Y),IsGeoTestTower J T →
        IsGeoTestTower P T ∧ ∀y∈(geoTransformAlong J T).cosupp,
          OrdRegime P μ T y ∧ regimeRun (OrdRegime P μ) T y=T.length := by
  obtain ⟨hm,hL,hEmpty,_hMark,hx,hμ,_hOrder,_hCoefficient,_hHistories⟩:=
    original_lower_coefficient_history_along hn Q hQ hN hE hMax W hW hSing a ha
  let V:=maskB Q (.refl : BlowupTower X X) a
  let L : MarkedIdeal n (CMfd.of (n:=n) V):=lowerMarkedB Q (.refl : BlowupTower X X) a
  let x : V:=⟨a,hm⟩
  let μ:=nmOrd L x
  let U:=ordMask L μ
  let P : MarkedIdeal n (CMfd.of (n:=n) U):=MarkedIdeal.pullback (Subtype.val : U→V) L
  change IsInvDomain (k-1) L at hL
  change L.E=[] at hEmpty
  change x∈L.cosupp at hx
  change L.d≤μ at hμ
  have hPos : 1≤μ:=hL.one_le_d.trans hμ
  have hP : IsInvDomain (k-1) P:=isInvDomain_pullback_val U hL
  have hNot : x∉ordGe L (μ+1):=by
    intro h
    have hBad:=(mem_ordGe_iff hL.isWellFormed hL.isNonzeroAlongAt (L.cosupp_subset_N hx) (μ+1)).mp h
    omega
  have hxU : x∈U:=(mem_ordMask_iff hn hL.isWellFormed hL.isNonzeroAlongAt μ x).mpr hNot
  have hBound : ∀z∈L.cosupp,z∈U → z∉ordGe L (μ+1):=fun _ _ hz=>notMem_ordGe_of_mem_ordMask hz
  have hBoundP : ∀z∈P.cosupp,z∉ordGe P (μ+1):=
    bound_pullback_val hn hL.isWellFormed hL.isNonzeroAlongAt U hBound
  have hJ:=isInvDomain_companionAlong (X:=CMfd.of (n:=n) U) (𝔪:=P) hn hP hPos
  have hMaxJ:=isMaximalOrderAlong_companionOf (X:=CMfd.of (n:=n) U) (𝔪:=P)
    hn hP.isWellFormed hP.isNonzeroAlongAt hBoundP
  have hPE : P.E=[]:=by
    change L.E.map ((Subtype.val : U→V) ⁻¹' ·)=[]
    rw [hEmpty,List.map_nil]
  have hμP : P.d≤μ:=hμ
  have hForm : companionOf n P μ=⟨P.N,[],RestrictedIdealExtension.restrictOn n P.N P.ideal,μ⟩:=by
    simp only [companionOf,companionAlong,if_neg (Nat.not_lt.mpr hμP),hPE]
    rw [nonmonomialPartAlong_nil_eq_restrictOn]
  have hJN : (companionOf n P μ).N=P.N:=companionAlong_N _ _ _ _ _ _
  have hMaxJ' : IsMaximalOrderAlong (companionOf n P μ).N (companionOf n P μ).ideal
      (companionOf n P μ).d:=by
    rw [hJN]
    exact hMaxJ
  refine ⟨hm,hxU,hJ,hMaxJ',hJN,?_,?_,?_,?_,?_⟩
  · change (companionOf n P μ).E=[]
    rw [hForm]
  · change (companionOf n P μ).d=μ
    rw [hForm]
  · change (companionOf n P μ).ideal=RestrictedIdealExtension.restrictOn n P.N P.ideal
    rw [hForm]
  · rfl
  · intro Y T hT
    exact ⟨(companionOf_tower_facts hn hP hPos hBoundP T hT).1,
      fun y hy=>⟨companion_point hn P hP hPos hBoundP T hT y hy,
        companion_run hn P hP hPos hBoundP T hT y hy⟩⟩

end
end Hironaka.HironakaActualOriginalCoefficientHistoryAlong
