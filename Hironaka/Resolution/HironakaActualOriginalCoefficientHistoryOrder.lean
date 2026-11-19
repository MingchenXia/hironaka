import Hironaka.Resolution.HironakaActualHistoricalOriginalBarOrder

/-! ALL genuine order thresholds and ordinary order of ORIGINAL coefficient
histories, without a current coefficient reset or maximal-order premise.
Blueprint FIRST: hironaka-actual-original-coefficient-history-order.tex. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualOriginalCoefficientHistoryOrder
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan GermIdealOrder IdealOrderArithmetic IdealWeightPowers
  GermIdealPullbackCalculus DerivativeIdeal DerivativeIdealTower MaximalContact
  CoefficientIdeal CoefficientIdealRestriction HomogenizedIdealAlong HomogenizedGlueing
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers
  HironakaActualHistoricalOriginalBarOrder

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

/-- EVERY threshold above the ORIGINAL mark on the SAME actual history.
Only original Q-tests are given; no current-reset coefficient or comparison. -/
theorem original_coefficient_history_threshold (Q : MarkedIdeal n X)
    (hN : Q.N=univ) (hI : Q.ideal.IsCoherent) (hd : 1≤Q.d)
    {Y : CMfd.{0} n}(T : BlowupTower X Y)(hT : IsGeoTestTower Q T)
    (r : ℕ)(hr : Q.d≤r) :
    let e:=sumExp (fun j=>Q.d-j) Q.d 0
    cosupport n univ (geoTransformAlong (coeffMarkedAlong Q) T).ideal (r*e)=
      cosupport n univ (geoTransformAlong Q T).ideal r := by
  let e:=sumExp (fun j=>Q.d-j) Q.d 0
  obtain ⟨he,hMark,_hCT,_hE,hPower⟩:=original_coefficient_history_power_le Q hN hI hd T hT
  have hA:= (inclusions_tower Q hN hI (show 0≤Q.d by omega) T hT).2.2.2.2.1
  have hEq : coeffMarkedAlong Q=coeffMarked Q:=coeffMarkedAlong_eq_coeffMarked hN (hol hI)
  have hAll : ∀i<Q.d,IsGeoTestTower (derivMarked Q i) T:=
    fun i hi=>(inclusions_tower Q hN hI hi.le T hT).1
  obtain ⟨hWhole,_hFam⟩:= (geoTransformAlong_msum (fun i=>derivMarked Q i) hd
    (isAmbientFamily_derivMarked hN hI) T).2 hAll
  change Q.d*e=(Finset.range Q.d).prod (fun j=>Q.d-j) at hMark
  ext y
  constructor
  · intro hy
    have hPow : y∈cosupport n univ (idealPow (geoTransformAlong Q T).ideal e) (r*e):=
      cosupport_subset_of_le hPower (r*e) hy
    rwa [OrderMultiplicativity.cosupport_idealPow_mul_eq (hol hA) he r] at hPow
  · intro hy
    rw [hEq]
    change y∈cosupport n univ
      (geoTransformAlong (msum (fun i=>derivMarked Q i) Q.d) T).ideal (r*e)
    rw [hWhole]
    change y∈cosupport n univ (finSumIdeal
      (fun i=>idealPow (geoTransformAlong (derivMarked Q i) T).ideal
        (sumExp (fun j=>(geoTransformAlong (derivMarked Q j) T).d) Q.d i)) Q.d) (r*e)
    apply (mem_cosupport_finSumIdeal (fun _ _ _ _ h=>holomorphicAt_of_mem_idealPow h)).mpr
    refine ⟨mem_univ y,?_⟩
    intro i hi
    obtain ⟨_hTest,_hNA,_hNJ,_hE,_hCA,_hCJ,hDeriv⟩:=inclusions_tower Q hN hI hi.le T hT
    have hCurrent : y∈cosupport n univ (iterDerivIdeal (geoTransformAlong Q T).ideal i) (r-i):=
      cosupport_add_subset_cosupport_iterDerivIdeal (geoTransformAlong Q T).ideal (r-i) i
        (by simpa only [Nat.sub_add_cancel (show i≤r by omega)] using hy)
    have hOriginal : y∈cosupport n univ (geoTransformAlong (derivMarked Q i) T).ideal (r-i):=
      cosupport_subset_of_le hDeriv (r-i) hCurrent
    let p:=sumExp (fun j=>Q.d-j) Q.d i
    have hP : y∈cosupport n univ
        (idealPow (geoTransformAlong (derivMarked Q i) T).ideal p) ((r-i)*p):=
      cosupport_subset_cosupport_idealPow (r-i) p hOriginal
    have hBalance : (Q.d-i)*p=Q.d*e:=
      (mul_sumExp (fun j=>Q.d-j) hi).trans hMark.symm
    have hBound : r*e≤(r-i)*p:=exponent_inequality (by omega) hr hi hBalance
    simpa only [d_geoTransformAlong,derivMarked_d] using cosupport_anti hBound hP

private theorem coefficient_history_coherent (Q : MarkedIdeal n X)
    (hN : Q.N=univ) (hI : Q.ideal.IsCoherent) (hd : 1≤Q.d)
    {Y : CMfd.{0} n}(T : BlowupTower X Y)(hT : IsGeoTestTower Q T) :
    (geoTransformAlong Q T).ideal.IsCoherent ∧
      (geoTransformAlong (coeffMarkedAlong Q) T).ideal.IsCoherent := by
  have hCeq : coeffMarkedAlong Q=coeffMarked Q:=coeffMarkedAlong_eq_coeffMarked hN (hol hI)
  have hCT : IsGeoTestTower (coeffMarkedAlong Q) T:=by
    rw [hCeq]
    exact (coeff_tower Q hN hI hd T).1.mpr hT
  have hCI : (coeffMarkedAlong Q).ideal.IsCoherent:=by
    rw [hCeq]
    exact isCoherent_coeffMarked hN hI
  exact ⟨(inclusions_tower Q hN hI (show 0≤Q.d by omega) T hT).2.2.2.2.1,
    (inclusions_tower (coeffMarkedAlong Q) hN hCI (show 0≤(coeffMarkedAlong Q).d by omega)
      T hCT).2.2.2.2.1⟩

/-- ENTIRE native ordinary order (including∞) of the ORIGINAL coefficient
transform. This is not raw nonmonomial order or a full suffix/CAN claim. -/
theorem original_coefficient_history_order (Q : MarkedIdeal n X)
    (hN : Q.N=univ) (hI : Q.ideal.IsCoherent) (hd : 1≤Q.d)
    {Y : CMfd.{0} n}(T : BlowupTower X Y)(hT : IsGeoTestTower Q T)
    (y : Y)(hy : y∈(geoTransformAlong Q T).cosupp) :
    let e:=sumExp (fun j=>Q.d-j) Q.d 0
    GermIdealOrder.order n univ (geoTransformAlong (coeffMarkedAlong Q) T).ideal y=
      (e : ℕ∞)*GermIdealOrder.order n univ (geoTransformAlong Q T).ideal y := by
  let A:=(geoTransformAlong Q T).ideal
  let B:=(geoTransformAlong (coeffMarkedAlong Q) T).ideal
  let e:=sumExp (fun j=>Q.d-j) Q.d 0
  obtain ⟨hA,hB⟩:=coefficient_history_coherent Q hN hI hd T hT
  obtain ⟨he,_hMark,_hCT,_hE,hPower⟩:=original_coefficient_history_power_le Q hN hI hd T hT
  have hNT : (geoTransformAlong Q T).N=univ:=
    (inclusions_tower Q hN hI (show 0≤Q.d by omega) T hT).2.1
  have hyM : y∈cosupport n univ A Q.d:=by
    simpa only [MarkedIdeal.cosupp,hNT,d_geoTransformAlong] using hy
  have hThresh (r : ℕ)(hr : Q.d≤r) :
      y∈cosupport n univ B (r*e) ↔ y∈cosupport n univ A r:=by
    rw [original_coefficient_history_threshold Q hN hI hd T hT r hr]
  by_cases hTop : GermIdealOrder.order n univ A y=⊤
  · have hBTop : GermIdealOrder.order n univ B y=⊤:=by
      apply ENat.eq_top_iff_forall_ge.mpr
      intro q
      have hSource : OrderGE n univ A y (q+Q.d):=
        (le_order_iff (hol hA y)).mp (by rw [hTop];exact le_top)
      have hTarget:=((hThresh (q+Q.d) (by omega)).mpr ⟨mem_univ y,hSource⟩).2
      have hLower : ((q+Q.d)*e : ℕ∞)≤GermIdealOrder.order n univ B y:=
        (le_order_iff (hol hB y)).mpr hTarget
      have hq : q≤(q+Q.d)*e:=by nlinarith
      exact (show (q : ℕ∞)≤((q+Q.d)*e : ℕ∞) by exact_mod_cast hq).trans hLower
    have he0 : (e : ℕ∞)≠0:=by exact_mod_cast (show e≠0 by omega)
    change GermIdealOrder.order n univ B y=(e : ℕ∞)*GermIdealOrder.order n univ A y
    rw [hBTop,hTop,ENat.mul_top he0]
  · obtain ⟨s,hs⟩:=ENat.ne_top_iff_exists.mp hTop
    have hM : Q.d≤s:=by
      have hLe:=(le_order_iff (hol hA y)).mpr hyM.2
      rw [←hs] at hLe
      exact_mod_cast hLe
    have hAtS : OrderGE n univ A y s:=
      (le_order_iff (hol hA y)).mp (by rw [←hs])
    have hCAtS:=((hThresh s hM).mpr ⟨mem_univ y,hAtS⟩).2
    have hNot : y∉cosupport n univ A (s+1):=by
      intro h
      have hLe:=(le_order_iff (hol hA y)).mpr h.2
      rw [←hs] at hLe
      exact Nat.not_succ_le_self s (by exact_mod_cast hLe)
    obtain ⟨f,hf,hNotf⟩:=CompanionReduction.exists_notMem_idealPow_of_notMem_cosupport hNot
    have hfh:=hol hA y f hf
    have hPowMem : B.mem y (fun z=>f z^e):=
      hPower y _ (OrderMultiplicativity.pow_mem_idealPow hf hfh e)
    have hNotC : ¬OrderGE n univ B y (e*s+1):=by
      intro h
      exact CompanionReduction.pow_notMem_idealPow hfh hNotf e
        (OrderTaylor.mem_idealPow_of_vanishesToOrderOn_univ (h _ hPowMem))
    have hUpper : GermIdealOrder.order n univ B y≤((e*s : ℕ) : ℕ∞):=by
      apply ENat.lt_natCast_add_one_iff.mp
      apply lt_of_not_ge
      intro h
      exact hNotC ((le_order_iff (hol hB y)).mp (by simpa only [Nat.cast_add,Nat.cast_one] using h))
    have hLower : ((s*e : ℕ) : ℕ∞)≤GermIdealOrder.order n univ B y:=
      (le_order_iff (hol hB y)).mpr hCAtS
    have hEq : GermIdealOrder.order n univ B y=((e*s : ℕ) : ℕ∞):=
      le_antisymm hUpper (by simpa only [Nat.mul_comm] using hLower)
    change GermIdealOrder.order n univ B y=(e : ℕ∞)*GermIdealOrder.order n univ A y
    rw [←hs,←Nat.cast_mul]
    exact hEq

end
end Hironaka.HironakaActualOriginalCoefficientHistoryOrder
