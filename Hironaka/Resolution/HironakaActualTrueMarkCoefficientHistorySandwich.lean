import Hironaka.Resolution.HironakaActualTrueMarkCommonContact
import Hironaka.Resolution.HironakaActualOriginalPowerTransform

/-! Whole ORIGINAL coefficient transforms at the actual true marks.
The two restricted inclusions retain the proper carrier and every boundary
position; no current coefficient reset or ambient power identity is asserted.
Blueprint FIRST: hironaka-actual-true-mark-coefficient-history-sandwich.tex. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualTrueMarkCoefficientHistorySandwich
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan IdealWeightPowers GermIdealOrder GermIdealPullbackCalculus
  InvertibleIdealQuotient RestrictedIdealWeight RestrictedIdealExtension RestrictedIdealQuotient
  RestrictLeCalculus MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealOperationsAlong
  MarkedIdealOperationsAlong.MarkedIdeal MarkedIdealEquivalence MarkedIdealEquivalence.MarkedIdeal
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold HomogenizedGlueing
  HomogenizedIdealAlongTower HomogenizedIdealAlong
  CoefficientIdeal CoefficientIdealRestriction DerivativeIdealAlong DerivativeIdealAlongCoherent TangentDirectionAlong
  ResolutionInvariantSpec InvDomainTowerAlong InvDomainCompanion
  HironakaActualOriginalPowerTransform HironakaActualPowerBoundaryExponents
  HironakaActualOriginalCoefficientHistoryAlong HironakaActualOriginalTrueMarkMaskCompanions
  HironakaActualInitialNonmonomialCoefficientBoundary
  NonmonomialOrderLocal NonmonomialOrderTail StepOneValue StepOneValueMasked
  StepOneRegime BoundaryCount CompanionRebase CompanionReductionAlong CompanionOpen
  GeneralValue MarkedIdealBiholomorphism MarkedIdealRestrictOpen HironakaEmbeddedAnalytic
  HironakaSharpOriginalProductTraceOrder

variable {n : ℕ} {X : CMfd.{u} n}

private theorem hol {Y : CMfd.{u} n} {I : GermIdeal n Y} (hI : I.IsCoherent) :
    ∀x f,I.mem x f→HolomorphicAt n f x :=
  fun _ _ hf=>GermIdeal.IsCoherent.holomorphicAt_mem hI hf

private theorem pullback_mono {Y : CMfd.{u} n} {A B : GermIdeal n X}
    (h : A.Le B) (f : Y→X) : (GermIdeal.pullback (m:=n) f A).Le (GermIdeal.pullback (m:=n) f B) := by
  intro x g hg
  exact GermIdeal.mem_pullback_iff.mpr ((GermIdeal.mem_pullback_iff.mp hg).mono
    (by rintro s ⟨a,ha,rfl⟩; exact ⟨a,h _ _ ha,rfl⟩))

private theorem restriction_mono {A B : GermIdeal n X} (h : A.Le B) (N : Set X) :
    (restrictOn n N A).Le (restrictOn n N B) := by
  intro x g hg
  exact ⟨hg.1,IsInSpanOnAt.mono (h x) hg.2⟩

private theorem lower_mark_step {Y : CMfd.{u} n} {A B : MarkedIdeal n X}
    (hN : A.N=B.N) (hI : A.ideal.Le B.ideal) (hd : A.d≤B.d)
    {C : Set X} {π : Y→X} (hπ : IsBlowupAlong n C π) :
    (A.geoTransform C π).ideal.Le (B.geoTransform C π).ideal := by
  rw [geoTransform_ideal,geoTransform_ideal,←hN]
  have hDen := idealPow_le_of_le
    (hol (isCoherent_pullback hπ.contMDiff (BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ))) hd
  have hNum:=restriction_mono (pullback_mono hI π) (geoStrictTransform π C A.N)
  intro x f hf
  exact ⟨hf.1,fun g hg=>hNum x _ (hf.2 g (hDen x g hg))⟩

private theorem lower_mark_data {A B : MarkedIdeal n X}
    (hN : A.N=B.N) (hE : A.E=B.E) (hI : A.ideal.Le B.ideal) (hd : A.d≤B.d) :
    ∀{Y : CMfd.{u} n}(T : BlowupTower X Y),
      (geoTransformAlong A T).N=(geoTransformAlong B T).N ∧
      (geoTransformAlong A T).E=(geoTransformAlong B T).E ∧
      (geoTransformAlong A T).ideal.Le (geoTransformAlong B T).ideal
  | _,.refl=>⟨hN,hE,hI⟩
  | _,.step T C π hπ=>by
    obtain ⟨hNT,hET,hIT⟩:=lower_mark_data hN hE hI hd T
    refine ⟨?_,?_,?_⟩
    · change geoStrictTransform π C (geoTransformAlong A T).N=geoStrictTransform π C (geoTransformAlong B T).N
      rw [hNT]
    · change (geoTransformAlong A T).E.map (geoStrictTransform π C)++[π ⁻¹' C]=
        (geoTransformAlong B T).E.map (geoStrictTransform π C)++[π ⁻¹' C]
      rw [hET]
    · exact lower_mark_step hNT hIT
        (by simpa only [d_geoTransformAlong] using hd) hπ

/-- Actual ambient ideal monotonicity for a lower controlled mark, with
every proper carrier/boundary and every literal test step retained. -/
theorem lower_mark_transform {A B : MarkedIdeal n X}
    (hN : A.N=B.N) (hE : A.E=B.E) (hI : A.ideal.Le B.ideal) (hd : A.d≤B.d)
    {Y : CMfd.{u} n}(T : BlowupTower X Y) :
    (geoTransformAlong A T).N=(geoTransformAlong B T).N ∧
    (geoTransformAlong A T).E=(geoTransformAlong B T).E ∧
    (geoTransformAlong A T).ideal.Le (geoTransformAlong B T).ideal ∧
    (IsGeoTestTower B T→IsGeoTestTower A T) := by
  obtain ⟨hNT,hET,hIT⟩:=lower_mark_data hN hE hI hd T
  refine ⟨hNT,hET,hIT,?_⟩
  clear hNT hET hIT
  induction T with
  | refl=>intro _; trivial
  | step T C π hπ ih=>
    intro hT
    obtain ⟨hBT,hC⟩:=hT
    obtain ⟨hN0,hE0,hI0⟩:=lower_mark_data hN hE hI hd T
    refine ⟨ih hBT, hC.1, ?_, ?_⟩
    · intro y hy
      have hz:=hC.2.1 hy
      change y∈cosupport n (geoTransformAlong A T).N (geoTransformAlong A T).ideal
        (geoTransformAlong A T).d
      rw [hN0]
      refine ⟨hz.1,fun g hg=>(hz.2 g (hI0 y g hg)).mono ?_⟩
      simpa only [d_geoTransformAlong] using hd
    · rw [hE0]
      exact hC.2.2

/-- Ordinary WHOLE finite sum at ONE unchanged common mark. -/
def uniformSum (F : ℕ→MarkedIdeal n X) (q : ℕ) : MarkedIdeal n X :=
  ⟨(F 0).N,(F 0).E,finSumIdeal (fun i=>(F i).ideal) q,(F 0).d⟩

private theorem uniform_sum_centre (F : ℕ→MarkedIdeal n X) {q : ℕ}
    (hq : 1≤q) (hF : IsSubmanifoldFamily F q)
    (hd : ∀i<q,(F i).d=(F 0).d) {C : Set X}
    (hC : ∀i<q,(F i).IsAdmissibleCentre C) : (uniformSum F q).IsAdmissibleCentre C := by
  refine ⟨(hC 0 hq).1,?_,(hC 0 hq).2.2⟩
  intro x hx
  apply (mem_cosupport_finSumIdeal (fun i hi=>hol (hF.coh i hi))).mpr
  refine ⟨((hC 0 hq).2.1 hx).1,?_⟩
  intro i hi
  have hz:=(hC i hi).2.1 hx
  change x∈cosupport n (F i).N (F i).ideal (F i).d at hz
  rwa [hF.N i hi,hd i hi] at hz

private theorem uniform_sum_step (F : ℕ→MarkedIdeal n X) {q : ℕ}
    (hq : 1≤q) (hF : IsSubmanifoldFamily F q)
    (hd : ∀i<q,(F i).d=(F 0).d) {Y : CMfd.{u} n} {C : Set X}
    {π : Y→X} (hπ : IsBlowupAlong n C π) (hC : ∀i<q,(F i).IsAdmissibleCentre C) :
    RestrictEquiv ((uniformSum F q).geoTransform C π)
      (uniformSum (fun i=>(F i).geoTransform C π) q) := by
  have hS:=isCoherent_finSumIdeal_of_lt hF.coh
  have hCS:=uniform_sum_centre F hq hF hd hC
  let L:=idealPow (GermIdeal.pullback (m:=n) π (vanishingIdeal (n:=n) C)) (F 0).d
  have hL : L.IsCoherent:=isCoherent_idealPow
    (isCoherent_pullback hπ.contMDiff (BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ)) _
  have hCurrent : ∀i<q,((F i).geoTransform C π).ideal.IsCoherent:=fun i hi=>
    HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre
      (hF.isClosedSubmanifold hi) (hF.coh i hi) (hC i hi) hπ
  have hCurrentSum:=isCoherent_finSumIdeal_of_lt hCurrent
  have hParts : ∀i<q,
      RestrictLe (geoStrictTransform π C (F 0).N) (GermIdeal.pullback (m:=n) π (F i).ideal)
        (L.mul ((F i).geoTransform C π).ideal) ∧
      RestrictLe (geoStrictTransform π C (F 0).N) (L.mul ((F i).geoTransform C π).ideal)
        (GermIdeal.pullback (m:=n) π (F i).ideal) := by
    intro i hi
    have h:=restrictLe_pullback_geoTransform (hF.isClosedSubmanifold hi) (hF.coh i hi) (hC i hi) hπ
    simpa only [geoTransform_N,hF.N i hi,hd i hi] using h
  have hPull : GermIdeal.pullback (m:=n) π (uniformSum F q).ideal=
      finSumIdeal (fun i=>GermIdeal.pullback (m:=n) π (F i).ideal) q :=
    pullback_finSumIdeal_of_lt hπ.contMDiff hq hF.coh
  have hMul : L.mul (finSumIdeal (fun i=>((F i).geoTransform C π).ideal) q)=
      finSumIdeal (fun i=>L.mul ((F i).geoTransform C π).ideal) q :=
    mul_finSumIdeal hL hq hCurrent
  have hEq:=restrictEquiv_geoTransform_of_pullback (𝔫:=uniformSum F q)
    hF.closed hS hCS hπ hCurrentSum (by
      change RestrictLe (geoStrictTransform π C (F 0).N) _ (L.mul _)
      rw [hPull,hMul]
      exact restrictLe_finSumIdeal (fun i hi=>hol (isCoherent_mul hL (hCurrent i hi)))
        (fun i hi=>(hParts i hi).1)) (by
      change RestrictLe (geoStrictTransform π C (F 0).N) (L.mul _) _
      rw [hPull,hMul]
      exact restrictLe_finSumIdeal (fun i hi=>hol (isCoherent_pullback hπ.contMDiff (hF.coh i hi)))
        (fun i hi=>(hParts i hi).2))
  exact hEq

/-- The WHOLE ordinary finite sum commutes with SAME actual tests on the
proper carrier, without raising the common mark by another marked sum. -/
theorem uniform_sum_transform (F : ℕ→MarkedIdeal n X) {q : ℕ}
    (hq : 1≤q) (hF : IsSubmanifoldFamily F q)
    (hd : ∀i<q,(F i).d=(F 0).d) :
    ∀{Y : CMfd.{u} n}(T : BlowupTower X Y),(∀i<q,IsGeoTestTower (F i) T)→
      IsGeoTestTower (uniformSum F q) T ∧
      RestrictEquiv (geoTransformAlong (uniformSum F q) T)
        (uniformSum (fun i=>geoTransformAlong (F i) T) q) ∧
      IsSubmanifoldFamily (fun i=>geoTransformAlong (F i) T) q
  | _,.refl,_=>⟨trivial,RestrictEquiv.refl (isCoherent_finSumIdeal_of_lt hF.coh),hF⟩
  | _,.step T C π hπ,hAll=>by
    have hPrefixes : ∀i<q,IsGeoTestTower (F i) T:=fun i hi=>(hAll i hi).1
    have hCentres : ∀i<q,(geoTransformAlong (F i) T).IsAdmissibleCentre C:=fun i hi=>(hAll i hi).2
    obtain ⟨hST,hEq,hFT⟩:=uniform_sum_transform F hq hF hd T hPrefixes
    have hdT : ∀i<q,(geoTransformAlong (F i) T).d=(geoTransformAlong (F 0) T).d:=by
      intro i hi
      simpa only [d_geoTransformAlong] using hd i hi
    have hCS:=uniform_sum_centre _ hq hFT hdT hCentres
    have hCurrentS : (geoTransformAlong (uniformSum F q) T).ideal.IsCoherent:=
      (inclusions_tower_along (uniformSum F q) hF.closed
        (isCoherent_finSumIdeal_of_lt hF.coh) (Nat.zero_le _) T hST).2.2.2.2.1
    have hCurrentN : IsClosedSubmanifold n (geoTransformAlong (uniformSum F q) T).N:=by
      rw [hEq.N_eq]
      exact hFT.closed
    refine ⟨⟨hST,hEq.isAdmissibleCentre_iff.mpr hCS⟩,?_,hFT.geoTransform hq hπ hCentres⟩
    change RestrictEquiv ((geoTransformAlong (uniformSum F q) T).geoTransform C π) _
    rw [hEq.geoTransform_eq hCurrentN.1 hCurrentS (isCoherent_finSumIdeal_of_lt hFT.coh) hπ.contMDiff]
    exact uniform_sum_step _ hq hFT hdT hπ hCentres

private theorem same_carrier {A B : MarkedIdeal n X} (hN : A.N=B.N)
    {Y : CMfd.{u} n}(T : BlowupTower X Y) :
    (geoTransformAlong A T).N=(geoTransformAlong B T).N := by
  rw [HomogenizedGlueingTower.N_geoTransformAlong,HomogenizedGlueingTower.N_geoTransformAlong,hN]

private theorem le_iter {N : Set X} {I : GermIdeal n X}
    (hN : IsClosedSubmanifold n N) (hI : I.IsCoherent) :
    ∀i : ℕ,I.Le (iterDerivIdealAlong N I i)
  | 0=>fun _ _ h=>h
  | i+1=>fun x g hg=>le_derivIdealAlong (hol (isCoherent_iterDerivIdealAlong hI hN i))
      x g (le_iter hN hI i x g hg)

private theorem derivative_domain {k : ℕ} (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) {i : ℕ} (hi : i<M.d) : IsInvDomain k (derivMarkedAlong M i) := by
  have hN:=hM.isWellFormed.isClosedSubmanifold_N
  have hI:=hM.isWellFormed.isCoherent
  refine ⟨⟨hN,isCoherent_iterDerivIdealAlong hI hN i,
    hM.isWellFormed.isSNCDivisor,hM.isWellFormed.isTransverse⟩,hM.dimLE,?_,?_⟩
  · change 1≤M.d-i
    omega
  · intro x hx
    obtain ⟨g,hg,hfreq⟩:=hM.isNonzeroAlongAt x hx
    exact ⟨g,le_iter hN hI i x g hg,hfreq⟩

private theorem exponent_bound {d m e p i : ℕ} (hd : 0<d) (hm : d≤m)
    (hi : i<d) (hBalance : (d-i)*p=d*e) : e*m≤(m-i)*p := by
  have hep : e≤p := by
    have hde : d*e≤d*p:=by rw [←hBalance]; exact Nat.mul_le_mul_right p (Nat.sub_le d i)
    exact Nat.le_of_mul_le_mul_left hde hd
  calc
    e*m=d*e+(m-d)*e:=by rw [←Nat.add_mul,Nat.add_sub_of_le hm,Nat.mul_comm]
    _=(d-i)*p+(m-d)*e:=by rw [hBalance]
    _≤(d-i)*p+(m-d)*p:=Nat.add_le_add_left (Nat.mul_le_mul_left (m-d) hep) _
    _=(m-i)*p:=by rw [←Nat.add_mul];congr 1;omega

/-- The ORIGINAL coefficient ideal formed at literal d, but controlled
at the genuine recoded mark e*M.d. All original geometric fields remain. -/
def recodedCoefficient (M : MarkedIdeal n X) (d : ℕ) : MarkedIdeal n X :=
  ⟨M.N,M.E,(coeffMarkedAlong {M with d:=d}).ideal,
    sumExp (fun j=>d-j) d 0*M.d⟩

/-- WHOLE ORIGINAL-history sandwich. Only ordinary source-domain data and
an actual original test are inputs; both restricted inclusions are produced. -/
theorem recoded_coefficient_history_sandwich {k : ℕ} (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) (d : ℕ) (hd : 1≤d) (hm : d≤M.d)
    {Y : CMfd.{u} n}(T : BlowupTower X Y)(hT : IsGeoTestTower M T) :
    let e:=sumExp (fun j=>d-j) d 0
    let B:=recodedCoefficient M d
    IsGeoTestTower B T ∧ (geoTransformAlong B T).N=(geoTransformAlong M T).N ∧
    (geoTransformAlong B T).E=(geoTransformAlong M T).E ∧ (geoTransformAlong B T).d=e*M.d ∧
    RestrictLe (geoTransformAlong M T).N (idealPow (geoTransformAlong M T).ideal e)
      (geoTransformAlong B T).ideal ∧
    RestrictLe (geoTransformAlong M T).N (geoTransformAlong B T).ideal
      (finSumIdeal (fun i=>idealPow
        (iterDerivIdealAlong (geoTransformAlong M T).N (geoTransformAlong M T).ideal i)
        (sumExp (fun j=>d-j) d i)) d) ∧
    (geoTransformAlong B T).E.length=M.E.length+T.length := by
  let e:=sumExp (fun j=>d-j) d 0
  let p:=fun i=>sumExp (fun j=>d-j) d i
  let F:=fun i=>{powerMarked (derivMarkedAlong M i) (p i) with d:=e*M.d}
  let B:=recodedCoefficient M d
  have hN:=hM.isWellFormed.isClosedSubmanifold_N
  have hI:=hM.isWellFormed.isCoherent
  have hp : ∀i,1≤p i:=fun i=>one_le_sumExp (fun j hj=>by omega) i
  have he : 1≤e:=hp 0
  have hBalance : ∀i<d,(d-i)*p i=d*e:=by
    intro i hi
    exact (mul_sumExp (fun j=>d-j) hi).trans
      (by simpa only [Nat.sub_zero] using (mul_sumExp (fun j=>d-j) (show 0<d from hd) (i:=0)).symm)
  have hBound : ∀i<d,e*M.d≤(M.d-i)*p i:=fun i hi=>
    exponent_bound (show 0<d from hd) hm hi (hBalance i hi)
  have hPower : ∀i<d,
      IsGeoTestTower (powerMarked (derivMarkedAlong M i) (p i)) T ∧
      RestrictEquiv (geoTransformAlong (powerMarked (derivMarkedAlong M i) (p i)) T)
        (powerMarked (geoTransformAlong (derivMarkedAlong M i) T) (p i)) := by
    intro i hi
    have hD:=derivative_domain M hM (lt_of_lt_of_le hi hm)
    have hDT:=(inclusions_tower_along M hN hI (show i≤M.d by omega) T hT).1
    exact original_power_transform _ hD (p i) (hp i) T hDT
  have hLow : ∀i<d,
      (geoTransformAlong (F i) T).ideal.Le
        (geoTransformAlong (powerMarked (derivMarkedAlong M i) (p i)) T).ideal ∧
      IsGeoTestTower (F i) T := by
    intro i hi
    have h:=lower_mark_transform (A:=F i) (B:=powerMarked (derivMarkedAlong M i) (p i))
      rfl rfl (fun _ _ h=>h) (hBound i hi) T
    exact ⟨h.2.2.1,h.2.2.2 (hPower i hi).1⟩
  have hFam : IsSubmanifoldFamily F d:=
    ⟨fun _ _=>rfl,fun _ _=>rfl,hN,
      fun i _=>isCoherent_idealPow (isCoherent_iterDerivIdealAlong hI hN i) _,
      fun _ _=>Nat.mul_pos he hM.one_le_d⟩
  have hSource : uniformSum F d=B:=rfl
  obtain ⟨hBT,hEq,hFT⟩:=uniform_sum_transform F hd hFam (fun _ _=>rfl) T
    (fun i hi=>(hLow i hi).2)
  rw [hSource] at hBT hEq
  have hBN : (geoTransformAlong B T).N=(geoTransformAlong M T).N:=same_carrier (A:=B) (B:=M) rfl T
  have hBE : (geoTransformAlong B T).E=(geoTransformAlong M T).E:=E_geoTransformAlong_eq (𝔪:=B) (𝔫:=M) rfl T
  have hCurrent:=isInvDomain_geoTransformAlong hM T hT
  have hBCoh : (geoTransformAlong B T).ideal.IsCoherent:=
    (inclusions_tower_along B hN (isCoherent_finSumIdeal_of_lt hFam.coh)
      (Nat.zero_le _) T hBT).2.2.2.2.1
  have hLowerSource : (powerMarked M e).ideal.Le B.ideal:=by
    rw [←hSource]
    intro x g hg
    change IsInSpanAt (n:=n) (fun s=>∃i,i<d ∧ (F i).ideal.mem x s) x g
    exact isInSpanAt_self ⟨0,hd,by simpa only [F,p,derivMarkedAlong_zero] using hg⟩
      (hol (isCoherent_idealPow hI e) x g hg)
  have hLowerHist:=lower_mark_transform (A:=powerMarked M e) (B:=B) rfl rfl
    hLowerSource (by change M.d*e≤e*M.d;exact le_of_eq (Nat.mul_comm _ _)) T
  have hPowerM:=(original_power_transform M hM e he T hT).2
  have hPowerMGe:=hPowerM.ge
  rw [same_carrier (A:=powerMarked M e) (B:=M) rfl T] at hPowerMGe
  have hLower : RestrictLe (geoTransformAlong M T).N (idealPow (geoTransformAlong M T).ideal e)
      (geoTransformAlong B T).ideal:=
    RestrictLe.trans hPowerMGe (restrictLe_of_le hBCoh hLowerHist.2.2.1)
  have hParts : ∀i<d,RestrictLe (geoTransformAlong M T).N (geoTransformAlong (F i) T).ideal
      (idealPow (iterDerivIdealAlong (geoTransformAlong M T).N (geoTransformAlong M T).ideal i) (p i)) := by
    intro i hi
    have hD:=derivative_domain M hM (lt_of_lt_of_le hi hm)
    have hPowDom:=powerMarked_isInvDomain _ hD (hp i)
    have hPowCurrent:=isInvDomain_geoTransformAlong hPowDom T (hPower i hi).1
    have hPowerLe:=(hPower i hi).2.le
    rw [same_carrier (A:=powerMarked (derivMarkedAlong M i) (p i)) (B:=M) rfl T] at hPowerLe
    have hDI:=(inclusions_tower_along M hN hI (show i≤M.d by omega) T hT).2.2.2.2.2.2
    exact RestrictLe.trans (restrictLe_of_le hPowCurrent.isWellFormed.isCoherent (hLow i hi).1)
      (RestrictLe.trans hPowerLe (restrictLe_idealPow
        (hol (isCoherent_iterDerivIdealAlong hCurrent.isWellFormed.isCoherent
          hCurrent.isWellFormed.isClosedSubmanifold_N i)) hDI (p i)))
  have hUpper:=hEq.le
  rw [hBN] at hUpper
  have hUpper' : RestrictLe (geoTransformAlong M T).N (geoTransformAlong B T).ideal
      (finSumIdeal (fun i=>idealPow
        (iterDerivIdealAlong (geoTransformAlong M T).N (geoTransformAlong M T).ideal i) (p i)) d):=
    RestrictLe.trans hUpper (restrictLe_finSumIdeal (fun i _=>hol (isCoherent_idealPow
      (isCoherent_iterDerivIdealAlong hCurrent.isWellFormed.isCoherent
        hCurrent.isWellFormed.isClosedSubmanifold_N i) _)) hParts)
  refine ⟨hBT,hBN,hBE,d_geoTransformAlong B T,hLower,hUpper',?_⟩
  exact length_E_geoTransformAlong B T

private theorem restricted_history {A B : MarkedIdeal n X} (h : RestrictEquiv A B)
    (hN : IsClosed A.N) (hA : A.ideal.IsCoherent) (hB : B.ideal.IsCoherent)
    {Y : CMfd.{u} n}(T : BlowupTower X Y) (hCurrent : (geoTransformAlong B T).ideal.IsCoherent) :
    RestrictEquiv (geoTransformAlong A T) (geoTransformAlong B T) := by
  cases T with
  | refl=>exact h
  | step T C π hπ=>
    rw [MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.geoTransformAlong_step_eq h hN hA hB T C π hπ]
    exact RestrictEquiv.refl hCurrent

private theorem iter_mono {N : Set X} {A B : GermIdeal n X} (h : A.Le B) :
    ∀i : ℕ,(iterDerivIdealAlong N A i).Le (iterDerivIdealAlong N B i)
  | 0=>h
  | i+1=>derivIdealAlong_mono (iter_mono h i)

/-- Ordinary ORIGINAL406 inputs derive the SAME lower/mask/true marks.
The actual companions' WHOLE original transforms satisfy both inclusions
at every shared actual history, with every old/born/empty clock retained. -/
theorem original_lower_companion_history_sandwich {A : CMfd.{0} n}
    (hn : 0<n) (Q : MarkedIdeal n A) {k : ℕ}(hQ : IsInvDomain k Q)
    (hN : Q.N=univ) (hE : Q.E=[]) (hMax : IsMaximalOrderAlong Q.N Q.ideal Q.d)
    (W : Set A)(hW : IsComplexAnalyticSubset (n:=n) W)
    (hSing : Q.cosupp⊆singularSet (n:=n) W)(a : A)(ha : a∈Q.cosupp) :
    ∃hm : a∈maskB Q (.refl : BlowupTower A A) a,
      let V:=maskB Q (.refl : BlowupTower A A) a
      let L : MarkedIdeal n (CMfd.of (n:=n) V):=lowerMarkedB Q (.refl : BlowupTower A A) a
      let x : V:=⟨a,hm⟩
      let μ:=nmOrd L x
      let e:=sumExp (fun j=>L.d-j) L.d 0
      let U:=ordMask L μ
      let P : MarkedIdeal n (CMfd.of (n:=n) U):=MarkedIdeal.pullback (Subtype.val : U→V) L
      let B : MarkedIdeal n (CMfd.of (n:=n) U):=MarkedIdeal.pullback (Subtype.val : U→V) (coeffMarkedAlong L)
      let J:=companionOf n P μ
      let K:=companionOf n B (e*μ)
      x∈U ∧ B=coeffMarkedAlong P ∧ IsInvDomain (k-1) J ∧ IsInvDomain (k-1) K ∧
      J.d=μ ∧ K.d=e*μ ∧
      ∀{Y : CMfd.{0} n}(T : BlowupTower (CMfd.of (n:=n) U) Y),IsGeoTestTower J T→
        IsGeoTestTower K T ∧ (geoTransformAlong J T).N=(geoTransformAlong K T).N ∧
        (geoTransformAlong J T).E=(geoTransformAlong K T).E ∧
        (geoTransformAlong J T).E.length=T.length ∧ (geoTransformAlong K T).E.length=T.length ∧
        RestrictLe (geoTransformAlong J T).N (idealPow (geoTransformAlong J T).ideal e)
          (geoTransformAlong K T).ideal ∧
        RestrictLe (geoTransformAlong J T).N (geoTransformAlong K T).ideal
          (finSumIdeal (fun i=>idealPow
            (iterDerivIdealAlong (geoTransformAlong J T).N (geoTransformAlong J T).ideal i)
            (sumExp (fun j=>L.d-j) L.d i)) L.d) := by
  obtain ⟨hm,hxU,_hMask,hNatural,hJ,hK,_hJMax,_hKMax,hJN,hKN,hJE,hKE,hJd,hKd,
    _hJHEq,_hKHEq,hWeak,_hHist⟩:=
    original_lower_true_mark_companions hn Q hQ hN hE hMax W hW hSing a ha
  obtain ⟨_hm0,hL,hEmpty,_hMark,_hx,hμ,_hOrd,_hCoeff,_hHistory⟩:=
    original_lower_coefficient_history_along hn Q hQ hN hE hMax W hW hSing a ha
  let V:=maskB Q (.refl : BlowupTower A A) a
  let L : MarkedIdeal n (CMfd.of (n:=n) V):=lowerMarkedB Q (.refl : BlowupTower A A) a
  let x : V:=⟨a,hm⟩
  let μ:=nmOrd L x
  let e:=sumExp (fun j=>L.d-j) L.d 0
  let U:=ordMask L μ
  let P : MarkedIdeal n (CMfd.of (n:=n) U):=MarkedIdeal.pullback (Subtype.val : U→V) L
  let B : MarkedIdeal n (CMfd.of (n:=n) U):=MarkedIdeal.pullback (Subtype.val : U→V) (coeffMarkedAlong L)
  let J:=companionOf n P μ
  let K:=companionOf n B (e*μ)
  let M : MarkedIdeal n (CMfd.of (n:=n) U):={P with d:=μ}
  let C:=recodedCoefficient M L.d
  change IsInvDomain (k-1) L at hL
  change L.E=[] at hEmpty
  change L.d≤μ at hμ
  change B=coeffMarkedAlong P at hNatural
  change IsInvDomain (k-1) J at hJ
  change IsInvDomain (k-1) K at hK
  change J.N=P.N at hJN
  change K.N=P.N at hKN
  change J.E=[] at hJE
  change K.E=[] at hKE
  change J.d=μ at hJd
  change K.d=e*μ at hKd
  have hP : IsInvDomain (k-1) P:=isInvDomain_pullback_val U hL
  have hPE : P.E=[]:=by
    change L.E.map ((Subtype.val : U→V) ⁻¹' ·)=[]
    rw [hEmpty,List.map_nil]
  have hM : IsInvDomain (k-1) M:=
    ⟨⟨hP.isWellFormed.isClosedSubmanifold_N,hP.isWellFormed.isCoherent,
      hP.isWellFormed.isSNCDivisor,hP.isWellFormed.isTransverse⟩,
      hP.dimLE,hL.one_le_d.trans hμ,hP.isNonzeroAlongAt⟩
  have hJI : J.ideal=restrictOn n P.N P.ideal:=by
    simp only [J,companionAlong,if_neg (Nat.not_lt.mpr (show P.d≤μ from hμ))]
    rw [hPE,nonmonomialPartAlong_nil_eq_restrictOn]
  have hJM : RestrictEquiv J M:=by
    refine ⟨hJN,?_,hJd,?_,?_⟩
    · change J.E=P.E
      rw [hJE,hPE]
    · change RestrictLe J.N J.ideal P.ideal
      rw [hJN,hJI]
      exact restrictLe_restrictOn
    · change RestrictLe J.N P.ideal J.ideal
      rw [hJN,hJI]
      exact restrictLe_self_restrictOn hP.isWellFormed.isCoherent
  have hBMark : B.d=P.d*e:=by
    rw [hNatural]
    change (Finset.range P.d).prod (fun j=>P.d-j)=P.d*e
    rw [show P.d=L.d from rfl]
    change (Finset.range L.d).prod (fun j=>L.d-j)=L.d*sumExp (fun j=>L.d-j) L.d 0
    simpa only [Nat.sub_zero] using (mul_sumExp (fun j=>L.d-j) (show 0<L.d from hL.one_le_d) (i:=0)).symm
  have hBμ : B.d≤e*μ:=by
    rw [hBMark,Nat.mul_comm P.d e]
    exact Nat.mul_le_mul_left e hμ
  have hBE : B.E=[]:=by rw [hNatural];exact hPE
  have hKI : K.ideal=restrictOn n P.N B.ideal:=by
    simp only [K,companionAlong,if_neg (Nat.not_lt.mpr hBμ)]
    change MonomialPartAlong.nonmonomialPartAlong n P.N B.ideal B.E=_
    rw [hBE,nonmonomialPartAlong_nil_eq_restrictOn]
  have hCI : C.ideal=B.ideal:=by rw [hNatural];rfl
  have hCCoh : C.ideal.IsCoherent:=by
    rw [hCI,hNatural]
    exact isCoherent_coeffMarkedAlong hP.isWellFormed.isCoherent hP.isWellFormed.isClosedSubmanifold_N
  have hKC : RestrictEquiv K C:=by
    refine ⟨hKN,?_,hKd,?_,?_⟩
    · change K.E=P.E
      rw [hKE,hPE]
    · rw [hKN,hKI,hCI]
      exact restrictLe_restrictOn
    · rw [hKN,hKI,hCI]
      exact restrictLe_self_restrictOn (hCI ▸ hCCoh)
  have hJMWeak:=MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.wEquiv hJM hJ.isWellFormed.isClosedSubmanifold_N.1
    hJ.isWellFormed.isCoherent hM.isWellFormed.isCoherent
  refine ⟨hm,hxU,hNatural,hJ,hK,hJd,hKd,?_⟩
  intro Y T hJT
  have hKT:=(hWeak.2 T).1.mp hJT
  have hMT:=(hJMWeak.2 T).1.mp hJT
  obtain ⟨hCT,_hCN,_hCE,_hCd,hLower,hUpper,_hLen⟩:=
    recoded_coefficient_history_sandwich M hM L.d hL.one_le_d hμ T hMT
  have hCurrentM:=isInvDomain_geoTransformAlong hM T hMT
  have hCurrentJ:=isInvDomain_geoTransformAlong hJ T hJT
  have hCurrentC : (geoTransformAlong C T).ideal.IsCoherent:=
    (inclusions_tower_along C hP.isWellFormed.isClosedSubmanifold_N hCCoh
      (Nat.zero_le _) T hCT).2.2.2.2.1
  have hJMT:=restricted_history hJM hJ.isWellFormed.isClosedSubmanifold_N.1
    hJ.isWellFormed.isCoherent hM.isWellFormed.isCoherent T hCurrentM.isWellFormed.isCoherent
  have hKCT:=restricted_history hKC hK.isWellFormed.isClosedSubmanifold_N.1
    hK.isWellFormed.isCoherent hCCoh T hCurrentC
  have hJK : (geoTransformAlong J T).N=(geoTransformAlong K T).N:=same_carrier (hJN.trans hKN.symm) T
  have hJKE : (geoTransformAlong J T).E=(geoTransformAlong K T).E:=E_geoTransformAlong_eq hWeak.1 T
  have hAmbientSource : M.ideal.Le J.ideal:=by
    change P.ideal.Le J.ideal
    rw [hJI]
    exact le_restrictOn hP.isWellFormed.isCoherent
  have hAmbient : (geoTransformAlong M T).ideal.Le (geoTransformAlong J T).ideal:=
    (lower_mark_transform (A:=M) (B:=J) hJN.symm hJM.E_eq.symm hAmbientSource
      (by change μ≤J.d;rw [hJd]) T).2.2.1
  rw [←hJMT.N_eq] at hLower hUpper
  have hKCLe:=hKCT.le
  have hKCGe:=hKCT.ge
  rw [←hJK] at hKCLe hKCGe
  have hLowerActual : RestrictLe (geoTransformAlong J T).N
      (idealPow (geoTransformAlong J T).ideal e) (geoTransformAlong K T).ideal:=
    RestrictLe.trans (restrictLe_idealPow (hol hCurrentM.isWellFormed.isCoherent) hJMT.le e)
      (RestrictLe.trans hLower hKCGe)
  have hCurrentN:=hCurrentJ.isWellFormed.isClosedSubmanifold_N
  have hCurrentI:=hCurrentJ.isWellFormed.isCoherent
  have hUpperParts : RestrictLe (geoTransformAlong J T).N
      (finSumIdeal (fun i=>idealPow
        (iterDerivIdealAlong (geoTransformAlong J T).N (geoTransformAlong M T).ideal i)
        (sumExp (fun j=>L.d-j) L.d i)) L.d)
      (finSumIdeal (fun i=>idealPow
        (iterDerivIdealAlong (geoTransformAlong J T).N (geoTransformAlong J T).ideal i)
        (sumExp (fun j=>L.d-j) L.d i)) L.d):=
    restrictLe_finSumIdeal (fun i _=>hol (isCoherent_idealPow
      (isCoherent_iterDerivIdealAlong hCurrentI hCurrentN i) _))
      (fun i _=>restrictLe_of_le (isCoherent_idealPow
        (isCoherent_iterDerivIdealAlong hCurrentI hCurrentN i) _)
        (MarkedIdealOperationsTransform.idealPow_mono (iter_mono hAmbient i) _))
  refine ⟨hKT,hJK,hJKE,?_,?_,hLowerActual,RestrictLe.trans hKCLe (RestrictLe.trans hUpper hUpperParts)⟩
  · rw [length_E_geoTransformAlong,hJE,List.length_nil,Nat.zero_add]
  · rw [length_E_geoTransformAlong,hKE,List.length_nil,Nat.zero_add]

end
end Hironaka.HironakaActualTrueMarkCoefficientHistorySandwich
