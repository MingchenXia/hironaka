import Hironaka.Resolution.HironakaG8MixedOrderInvariance
import Hironaka.Resolution.HironakaActualCoefficientNonmonomialHistoryOrder
import Hironaka.Resolution.HironakaActualPolymorphicBornExponent

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Boundary exponents on mixed-test equivalence classes along towers (G8 lane, run 0080, round 2; D01, entries E1–E3)

Blueprint: `hironaka-g8-resume-mixed-boundary-exponents.tex`.  Route note:
`work/hironaka-resume-20261111/G8/D01-ROUTE-r2.md`.

`HironakaG8MixedOrderInvariance` proved the first entry `nmOrd` of `CanonicalCentres.canonicalInvariant` constant on
same-mark mixed-test equivalence classes at the points OFF the exceptional boundary.  On the boundary the first entry is
`ord − Σ β_H` (`HironakaActualCoefficientNonmonomialHistoryOrder.whole_factor_order`), so it needs the boundary
exponents `β_H`.  Bierstone–Milman (BM97 Prop. 4.11) obtain their invariance in general through products with a line and
exceptional blowups.  Along a common multiple test blowup, however, every member of the boundary that was not there
initially is BORN at a step of the tower, and its exponents are computed from the history:

* the born exponent is `divExpAlong(𝔞_T, C) − d` (`HironakaActualPolymorphicBornExponent.original_history_born_exponent`),
  and the exponent along an admissible centre `C ⊆ cosupp` only sees cosupport points, where the orders are class
  invariants (BM97 Prop. 4.8 along histories, `mixedEquiv_normalizedOrder_record`): `mixedEquiv_divExpAlong_centre_eq`;
* an old member keeps its exponent on its strict transform
  (`HironakaActualOldDivisorExponentTransport.original_history_old_exponent`), and images of cosupport points are
  cosupport points.

This module proves, for `A ~ B` (`MixedEquiv`) in the native domain with the same carrier and the same mark, whose initial
boundary exponents agree on the initial cosupport (`ExpAgree A B`; vacuous for `E = []`, the case of the initial window
records):

* **exponents** (`mixedEquiv_expAgree_geoTransformAlong`, `mixedEquiv_expDataAlong_geoTransformAlong_eq`): along every
  common multiple test blowup `T`, at every cosupport point, all boundary exponents of `A_T` and `B_T` agree;
* **E1 on the whole cosupport** (`mixedEquiv_nmOrd_geoTransformAlong_eq`, `mixedEquiv_canonicalInvariant_fst_eq`,
  `_of_nil`): the first entries of `canonicalInvariant` agree at every point of the cosupport, boundary included;
* **E2** (`mixedEquiv_regimeRun_eq`): the regime runs (the split `T = T₀ T₁` of the general value) agree;
* **E3** (`mixedEquiv_genInv_eq_of_nmOrd_eq_zero`, `mixedEquiv_canonicalInvariant_eq_of_nmOrd_eq_zero`): at the points
  of order `0` (the monomial case) the FULL values of the general value (for every lower value function) and of
  `canonicalInvariant` agree.

Also: `divExpAlong_congr`, `divExpAlong_eq_zero_of_notMem`, `expDataAlong_eq_of_expAgree`,
`nmOrd_eq_of_expAgree` (`ord = Σ β + nmOrd` on both sides), `mixedEquiv_ordinaryTraceOrder_geoTransformAlong_eq`.

Not here: the companion value (E4) and the masked Step 1 value (E5) at points of positive order; boundary exponents of
initial members along general mixed histories (BM97 Prop. 4.11 proper).  Sorry-free.  Universe `0` (the old-member
transport is stated there).  Import discipline: no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8MixedBoundaryExponents

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals
  MarkedIdeals.MarkedIdeal GermIdealOrder RelativePrincipalizationSpan DivisorExponentAlong
open Hironaka.ResolutionInvariantSpec (IsInvDomain cosupp_eq_empty_of_dimLE_zero)
open Hironaka.BlowupStrictSubmanifold (geoStrictTransform geoStrictTransform_subset_preimage)
open Hironaka.NonmonomialOrderLocal (nmOrd)
open Hironaka.HironakaSharpOriginalProductTraceOrder (ordinaryTraceOrder
  ordinaryTraceOrder_cosupport_iff)
open Hironaka.HironakaActualMixedTestPowerNormalization
open Hironaka.HironakaG8MixedEquiv
open Hironaka.HironakaG8MixedOrderInvariance (fstEntry canonicalInvariant_fst
  mixedEquiv_normalizedOrder_record)
open Hironaka.MonomialCase (memberIdx)
open Hironaka.MonomialCaseAlong (expDataAlong gammaAlong)
open Hironaka.StepOneRegime (regimeRun regimeRun_step)
open Hironaka.NonmonomialOrderRegime (OrdRegime)
open Hironaka.CanonicalCentres (canonicalInvariant)

noncomputable section

/-! ### Exponents along a set -/

section Exponent

variable {m : ℕ} {Y : CMfd.{0} m}

/-- **The exponent along `H` is determined by the divisibility predicates.** -/
theorem divExpAlong_congr {N N' H H' : Set Y} {I J : GermIdeal m Y} {x : Y}
    (h : ∀ e, IsDivNearAlong m N I H e x ↔ IsDivNearAlong m N' J H' e x) :
    divExpAlong m N I H x = divExpAlong m N' J H' x := by
  classical
  have hex : (∃ e, ¬ IsDivNearAlong m N I H (e + 1) x) ↔ ∃ e, ¬ IsDivNearAlong m N' J H' (e + 1) x :=
    exists_congr fun e => not_congr (h (e + 1))
  by_cases hE : ∃ e, ¬ IsDivNearAlong m N I H (e + 1) x
  · have hE' := hex.mp hE
    simp only [divExpAlong, dif_pos hE, dif_pos hE']
    exact Nat.find_congr' fun {e} => not_congr (h (e + 1))
  · have hE' : ¬ ∃ e, ¬ IsDivNearAlong m N' J H' (e + 1) x := fun h' => hE (hex.mpr h')
    simp only [divExpAlong, dif_neg hE, dif_neg hE']

/-- Off the closed set `N ∩ H` the exponent is `0` (every divisibility holds). -/
theorem divExpAlong_eq_zero_of_notMem {N H : Set Y} {I : GermIdeal m Y} (hc : IsClosed (N ∩ H)) {x : Y}
    (hx : x ∉ N ∩ H) : divExpAlong m N I H x = 0 := by
  unfold divExpAlong
  rw [dif_neg]
  rintro ⟨e, he⟩
  exact he (isDivNearAlong_of_notMem hc hx (e + 1))

/-- **Exponent agreement**: at every point of the cosupport of `P`, the exponents of `P` and `Q` along the members of
the boundary of `P` through the point agree. -/
def ExpAgree (P Q : MarkedIdeal m Y) : Prop :=
  ∀ H ∈ P.E, ∀ y ∈ P.cosupp, y ∈ H → divExpAlong m P.N P.ideal H y = divExpAlong m Q.N Q.ideal H y

/-- With empty boundary, exponent agreement is vacuous. -/
theorem expAgree_of_nil {P Q : MarkedIdeal m Y} (hE : P.E = []) : ExpAgree P Q := by
  intro H hH
  rw [hE] at hH
  exact absurd hH List.not_mem_nil

/-- **The exponent data agree as functions** (same boundary, same closed carrier) at a cosupport point. -/
theorem expDataAlong_eq_of_expAgree {P Q : MarkedIdeal m Y} (hP : P.IsWellFormed) (hNQ : Q.N = P.N)
    (hE : Q.E = P.E) (hag : ExpAgree P Q) {y : Y} (hy : y ∈ P.cosupp) :
    expDataAlong m P.N P.ideal P.E y = expDataAlong m Q.N Q.ideal Q.E y := by
  funext i
  rw [hE]
  unfold expDataAlong
  split_ifs with hi
  · by_cases hyH : y ∈ P.E.get ⟨i, hi⟩
    · exact hag _ (List.get_mem _ _) y hy hyH
    · have hcl : IsClosed (P.N ∩ P.E.get ⟨i, hi⟩) :=
        hP.isClosedSubmanifold_N.1.inter (hP.isSNCDivisor.1 _ (List.get_mem _ _))
      rw [divExpAlong_eq_zero_of_notMem hcl (fun h => hyH h.2), hNQ,
        divExpAlong_eq_zero_of_notMem hcl (fun h => hyH h.2)]
  · rfl

/-- A marked ideal of the native domain with a cosupport point lives in positive dimension. -/
theorem pos_of_mem_cosupp {k : ℕ} {P : MarkedIdeal m Y} (hP : IsInvDomain k P) {y : Y} (hy : y ∈ P.cosupp) :
    0 < m := by
  by_contra hm
  have hm0 : m = 0 := by omega
  have h0 : IsInvDomain 0 P := {
    isWellFormed := hP.isWellFormed
    dimLE := by
      intro z hz
      obtain ⟨r, hr⟩ := hP.isWellFormed.isClosedSubmanifold_N.2 z hz
      exact ⟨r, by have := hr.1; omega, hr⟩
    one_le_d := hP.one_le_d
    isNonzeroAlongAt := hP.isNonzeroAlongAt }
  rw [cosupp_eq_empty_of_dimLE_zero h0] at hy
  exact hy

/-- **`ord = Σ β + nmOrd` on both sides**: equal ordinary orders and agreeing exponents at a cosupport point give equal
first entries (`whole_factor_order`). -/
theorem nmOrd_eq_of_expAgree {kP kQ : ℕ} {P Q : MarkedIdeal m Y} (hP : IsInvDomain kP P) (hQ : IsInvDomain kQ Q)
    (hNQ : Q.N = P.N) (hE : Q.E = P.E) (hag : ExpAgree P Q) {y : Y} (hy : y ∈ P.cosupp)
    (hord : ordinaryTraceOrder P.N P.ideal y = ordinaryTraceOrder Q.N Q.ideal y) : nmOrd P y = nmOrd Q y := by
  have hm := pos_of_mem_cosupp hP hy
  have hyN : y ∈ P.N := P.cosupp_subset_N hy
  have hyNQ : y ∈ Q.N := hNQ ▸ hyN
  obtain ⟨-, -, hoP, -⟩ := HironakaActualCoefficientNonmonomialHistoryOrder.whole_factor_order hm P
    hP.isWellFormed hP.isNonzeroAlongAt y hyN
  obtain ⟨-, -, hoQ, -⟩ := HironakaActualCoefficientNonmonomialHistoryOrder.whole_factor_order hm Q
    hQ.isWellFormed hQ.isNonzeroAlongAt y hyNQ
  have hexp := expDataAlong_eq_of_expAgree hP.isWellFormed hNQ hE hag hy
  have hs : (∑ i ∈ memberIdx Q.E y, expDataAlong m Q.N Q.ideal Q.E y i) =
      ∑ i ∈ memberIdx P.E y, expDataAlong m P.N P.ideal P.E y i := by
    rw [← hexp, hE]
  rw [hs] at hoQ
  omega

end Exponent

/-! ### Orders and centre exponents along common test towers -/

section Tower

variable {n : ℕ} {X : CMfd.{0} n}

/-- The carrier along a tower only depends on the initial carrier. -/
theorem carrier_geoTransformAlong_eq {P Q : MarkedIdeal n X} (hN : P.N = Q.N) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), (geoTransformAlong P T).N = (geoTransformAlong Q T).N
  | _, .refl => hN
  | _, .step T C π _ => congrArg (geoStrictTransform π C) (carrier_geoTransformAlong_eq hN T)

variable {kA kB : ℕ} {A B : MarkedIdeal n X}

/-- **Same-mark orders along common test towers** (BM97 Prop. 4.8 along histories): for `A ~ B` with the same carrier
and mark, the ordinary orders of `A_T` and `B_T` agree on the cosupport. -/
theorem mixedEquiv_ordinaryTraceOrder_geoTransformAlong_eq (h : MixedEquiv A B) (hA : IsInvDomain kA A)
    (hB : IsInvDomain kB B) (hN : B.N = A.N) (hd : B.d = A.d) {Y : CMfd.{0} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower A T) {y : Y} (hy : y ∈ (geoTransformAlong A T).cosupp) :
    ordinaryTraceOrder (geoTransformAlong A T).N (geoTransformAlong A T).ideal y =
      ordinaryTraceOrder (geoTransformAlong B T).N (geoTransformAlong B T).ideal y := by
  have rA := record_towerHistory_refl A T
  have rB : record (withBoundary B A.E) (towerHistory (.refl : History X A.E X A.E) T) = geoTransformAlong B T :=
    (record_towerHistory_refl (withBoundary B A.E) T).trans
      (congrArg (fun M => geoTransformAlong M T) (withBoundary_eq h.E_eq))
  have hH : IsTest A (towerHistory (.refl : History X A.E X A.E) T) := (isTest_towerHistory_refl_iff A T).mpr hT
  have hy' : y ∈ (record A (towerHistory (.refl : History X A.E X A.E) T)).cosupp := by
    rw [rA]
    exact hy
  have h1 := mixedEquiv_normalizedOrder_record h hA hB hN (towerHistory .refl T) hH hy'
  rw [rA, rB, hd] at h1
  exact Nat.eq_of_mul_eq_mul_left (Nat.lt_of_lt_of_le Nat.zero_lt_one hA.one_le_d) h1

/-- **Exponents along an admissible centre are class invariants** (same carrier, same mark): the divisibility
predicates along `C ⊆ cosupp` only test cosupport points, where the orders agree. -/
theorem mixedEquiv_divExpAlong_centre_eq (h : MixedEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hN : B.N = A.N) (hd : B.d = A.d) {Y : CMfd.{0} n} (T : BlowupTower X Y) (hT : IsGeoTestTower A T) {C : Set Y}
    (hC : (geoTransformAlong A T).IsAdmissibleCentre C) (x : Y) :
    divExpAlong n (geoTransformAlong A T).N (geoTransformAlong A T).ideal C x =
      divExpAlong n (geoTransformAlong B T).N (geoTransformAlong B T).ideal C x := by
  have hNT := carrier_geoTransformAlong_eq hN T
  have hTB : IsGeoTestTower B T := (h.wEquiv.2 T).1.mp hT
  have hcos : (geoTransformAlong A T).cosupp = (geoTransformAlong B T).cosupp := (h.wEquiv.2 T).2 hT
  have hdA := InvDomainTowerAlong.isInvDomain_geoTransformAlong hA T hT
  have hdB := InvDomainTowerAlong.isInvDomain_geoTransformAlong hB T hTB
  have iffA := fun {z : Y} (hz : z ∈ (geoTransformAlong A T).N) (e : ℕ) =>
    ordinaryTraceOrder_cosupport_iff hdA.isWellFormed.isClosedSubmanifold_N hdA.isWellFormed.isCoherent
      hdA.isNonzeroAlongAt hz e
  have iffB := fun {z : Y} (hz : z ∈ (geoTransformAlong B T).N) (e : ℕ) =>
    ordinaryTraceOrder_cosupport_iff hdB.isWellFormed.isClosedSubmanifold_N hdB.isWellFormed.isCoherent
      hdB.isNonzeroAlongAt hz e
  refine divExpAlong_congr fun e => ?_
  unfold IsDivNearAlong
  refine eventually_congr (Eventually.of_forall fun z => ?_)
  constructor
  · intro hz hzB hzC
    have hzA : z ∈ (geoTransformAlong A T).N := hNT ▸ hzB
    have ho := mixedEquiv_ordinaryTraceOrder_geoTransformAlong_eq h hA hB hN hd T hT (hC.2.1 hzC)
    exact (iffB hzB e).mpr (ho ▸ (iffA hzA e).mp (hz hzA hzC))
  · intro hz hzA hzC
    have hzB : z ∈ (geoTransformAlong B T).N := hNT.symm ▸ hzA
    have ho := mixedEquiv_ordinaryTraceOrder_geoTransformAlong_eq h hA hB hN hd T hT (hC.2.1 hzC)
    exact (iffA hzA e).mpr (ho.symm ▸ (iffB hzB e).mp (hz hzB hzC))

/-- **Boundary exponents along common test towers**: if the initial exponents agree on the initial cosupport (e.g.
`E = []`), the exponents of `A_T` and `B_T` agree at every cosupport point along every common multiple test blowup.
Born members: born exponent `= divExpAlong(C) − d` and `mixedEquiv_divExpAlong_centre_eq`; old members: exponent
transport on the strict transform, at the image point (a cosupport point). -/
theorem mixedEquiv_expAgree_geoTransformAlong (h : MixedEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hN : B.N = A.N) (hd : B.d = A.d) (h0 : ExpAgree A B) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), IsGeoTestTower A T →
      ExpAgree (geoTransformAlong A T) (geoTransformAlong B T)
  | _, .refl, _ => h0
  | _, .step T C π hπ, hT => by
    obtain ⟨hTT, hC⟩ := (isGeoTestTower_step_iff A T C π hπ).mp hT
    have hTB : IsGeoTestTower B T := (h.wEquiv.2 T).1.mp hTT
    have hcos : (geoTransformAlong A T).cosupp = (geoTransformAlong B T).cosupp := (h.wEquiv.2 T).2 hTT
    have hET : (geoTransformAlong B T).E = (geoTransformAlong A T).E :=
      MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq h.E_eq T
    have hCB : (geoTransformAlong B T).IsAdmissibleCentre C :=
      (isAdmissibleCentre_congr hET.symm hcos C).mp hC
    have hdA := InvDomainTowerAlong.isInvDomain_geoTransformAlong hA T hTT
    have hNT := carrier_geoTransformAlong_eq hN T
    have ih := mixedEquiv_expAgree_geoTransformAlong h hA hB hN hd h0 T hTT
    intro H hH z hz hzH
    have hzN : z ∈ ((geoTransformAlong A T).geoTransform C π).N := ((geoTransformAlong A T).geoTransform C π).cosupp_subset_N hz
    have hzNB : z ∈ ((geoTransformAlong B T).geoTransform C π).N := by
      show z ∈ geoStrictTransform π C (geoTransformAlong B T).N
      rw [hNT]
      exact hzN
    have hpz : π z ∈ (geoTransformAlong A T).cosupp :=
      CompanionReductionAlong.mem_cosupp_of_mem_cosupp_geoTransform_along hdA.isWellFormed.isClosedSubmanifold_N.1
        (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hdA.isWellFormed.isCoherent hg) hC hπ hz
    change H ∈ (geoTransformAlong A T).E.map (geoStrictTransform π C) ++ [π ⁻¹' C] at hH
    rcases List.mem_append.mp hH with hold | hborn
    · obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hold
      obtain ⟨i, hi⟩ := List.get_of_mem hH₀
      obtain ⟨j, hj⟩ := List.get_of_mem (hET.symm ▸ hH₀ : H₀ ∈ (geoTransformAlong B T).E)
      have hzi : z ∈ geoStrictTransform π C ((geoTransformAlong A T).E.get i) := by rw [hi]; exact hzH
      have hzj : z ∈ geoStrictTransform π C ((geoTransformAlong B T).E.get j) := by rw [hj]; exact hzH
      have eA := HironakaActualOldDivisorExponentTransport.original_history_old_exponent A hA T hTT hC hπ i hzN hzi
      have eB := HironakaActualOldDivisorExponentTransport.original_history_old_exponent B hB T hTB hCB hπ j hzNB hzj
      rw [hi] at eA
      rw [hj] at eB
      have hH₀c : IsClosed H₀ := hdA.isWellFormed.isSNCDivisor.1 H₀ hH₀
      have hpzH : π z ∈ H₀ := geoStrictTransform_subset_preimage hπ.contMDiff.continuous hH₀c hzH
      show divExpAlong n ((geoTransformAlong A T).geoTransform C π).N ((geoTransformAlong A T).geoTransform C π).ideal
          (geoStrictTransform π C H₀) z =
        divExpAlong n ((geoTransformAlong B T).geoTransform C π).N ((geoTransformAlong B T).geoTransform C π).ideal
          (geoStrictTransform π C H₀) z
      rw [eA, eB]
      exact ih H₀ hH₀ (π z) hpz hpzH
    · rw [List.mem_singleton] at hborn
      subst hborn
      have bA := (HironakaActualPolymorphicBornExponent.original_history_born_exponent A hA T hTT hC hπ hzN hzH).2
      have bB := (HironakaActualPolymorphicBornExponent.original_history_born_exponent B hB T hTB hCB hπ hzNB hzH).2
      show divExpAlong n ((geoTransformAlong A T).geoTransform C π).N ((geoTransformAlong A T).geoTransform C π).ideal
          (π ⁻¹' C) z =
        divExpAlong n ((geoTransformAlong B T).geoTransform C π).N ((geoTransformAlong B T).geoTransform C π).ideal
          (π ⁻¹' C) z
      rw [bA, bB, mixedEquiv_divExpAlong_centre_eq h hA hB hN hd T hTT hC (π z), hd]

/-- **The exponent data agree as functions** along common test towers, at every cosupport point. -/
theorem mixedEquiv_expDataAlong_geoTransformAlong_eq (h : MixedEquiv A B) (hA : IsInvDomain kA A)
    (hB : IsInvDomain kB B) (hN : B.N = A.N) (hd : B.d = A.d) (h0 : ExpAgree A B) {Y : CMfd.{0} n}
    (T : BlowupTower X Y) (hT : IsGeoTestTower A T) {y : Y} (hy : y ∈ (geoTransformAlong A T).cosupp) :
    expDataAlong n (geoTransformAlong A T).N (geoTransformAlong A T).ideal (geoTransformAlong A T).E y =
      expDataAlong n (geoTransformAlong B T).N (geoTransformAlong B T).ideal (geoTransformAlong B T).E y :=
  expDataAlong_eq_of_expAgree (InvDomainTowerAlong.isInvDomain_geoTransformAlong hA T hT).isWellFormed
    (carrier_geoTransformAlong_eq hN T) (MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq h.E_eq T)
    (mixedEquiv_expAgree_geoTransformAlong h hA hB hN hd h0 T hT) hy

/-- **E1 on the whole cosupport**: for `A ~ B` in the native domain with the same carrier and mark and agreeing initial
exponents, the first entries `nmOrd` of `A_T`, `B_T` agree at every cosupport point, boundary included. -/
theorem mixedEquiv_nmOrd_geoTransformAlong_eq (h : MixedEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hN : B.N = A.N) (hd : B.d = A.d) (h0 : ExpAgree A B) {Y : CMfd.{0} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower A T) {y : Y} (hy : y ∈ (geoTransformAlong A T).cosupp) :
    nmOrd (geoTransformAlong A T) y = nmOrd (geoTransformAlong B T) y := by
  have hTB : IsGeoTestTower B T := (h.wEquiv.2 T).1.mp hT
  exact nmOrd_eq_of_expAgree (InvDomainTowerAlong.isInvDomain_geoTransformAlong hA T hT)
    (InvDomainTowerAlong.isInvDomain_geoTransformAlong hB T hTB) (carrier_geoTransformAlong_eq hN T)
    (MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq h.E_eq T)
    (mixedEquiv_expAgree_geoTransformAlong h hA hB hN hd h0 T hT) hy
    (mixedEquiv_ordinaryTraceOrder_geoTransformAlong_eq h hA hB hN hd T hT hy)

/-- **E2: the regime runs agree** (hence the split `T = T₀ T₁` of the general value at every point): along every common
multiple test blowup, for every order `o`. -/
theorem mixedEquiv_regimeRun_eq (h : MixedEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hN : B.N = A.N) (hd : B.d = A.d) (h0 : ExpAgree A B) (o : ℕ) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), IsGeoTestTower A T → ∀ y : Y,
      regimeRun (OrdRegime A o) T y = regimeRun (OrdRegime B o) T y
  | _, .refl, _, _ => rfl
  | _, .step T C π hπ, hT, z => by
    have hTT := ((isGeoTestTower_step_iff A T C π hπ).mp hT).1
    have hcos : (geoTransformAlong A T).cosupp = (geoTransformAlong B T).cosupp := (h.wEquiv.2 T).2 hTT
    have hiff : OrdRegime A o T (π z) ↔ OrdRegime B o T (π z) := by
      show (π z ∈ (geoTransformAlong A T).cosupp ∧ nmOrd (geoTransformAlong A T) (π z) = o) ↔
        (π z ∈ (geoTransformAlong B T).cosupp ∧ nmOrd (geoTransformAlong B T) (π z) = o)
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨hcos ▸ h1, (mixedEquiv_nmOrd_geoTransformAlong_eq h hA hB hN hd h0 T hTT h1).symm.trans h2⟩
      · rintro ⟨h1, h2⟩
        have h1' : π z ∈ (geoTransformAlong A T).cosupp := hcos.symm ▸ h1
        exact ⟨h1', (mixedEquiv_nmOrd_geoTransformAlong_eq h hA hB hN hd h0 T hTT h1').trans h2⟩
    rw [regimeRun_step, regimeRun_step, mixedEquiv_regimeRun_eq h hA hB hN hd h0 o T hTT (π z)]
    by_cases hP : OrdRegime A o T (π z)
    · rw [if_pos hP, if_pos (hiff.mp hP)]
    · rw [if_neg hP, if_neg (fun h' => hP (hiff.mpr h'))]

/-- **E3: at the points of order `0` the full general values agree** (for every lower value function `M`): the second
entry is `γ` of the transform, which only depends on the boundary, the exponent data and the mark. -/
theorem mixedEquiv_genInv_eq_of_nmOrd_eq_zero {Λ : Type} [LinearOrder Λ]
    (M : ∀ {X : CMfd.{0} n}, MarkedIdeal n X → ∀ {Y : CMfd.{0} n}, BlowupTower X Y → Y → Λ)
    (h : MixedEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B) (hN : B.N = A.N) (hd : B.d = A.d)
    (h0 : ExpAgree A B) {Y : CMfd.{0} n} (T : BlowupTower X Y) (hT : IsGeoTestTower A T) {y : Y}
    (hy : y ∈ (geoTransformAlong A T).cosupp) (hzero : nmOrd (geoTransformAlong A T) y = 0) :
    GeneralValue.genInv M A T y = GeneralValue.genInv M B T y := by
  have hnm := mixedEquiv_nmOrd_geoTransformAlong_eq h hA hB hN hd h0 T hT hy
  rw [GeneralValue.genInv_of_nmOrd_eq_zero M A T hzero,
    GeneralValue.genInv_of_nmOrd_eq_zero M B T (hnm.symm.trans hzero)]
  have hexp := mixedEquiv_expDataAlong_geoTransformAlong_eq h hA hB hN hd h0 T hT hy
  have hET : (geoTransformAlong B T).E = (geoTransformAlong A T).E :=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq h.E_eq T
  have hγ : gammaAlong n (geoTransformAlong A T).N (geoTransformAlong A T).ideal (geoTransformAlong A T).E
      (geoTransformAlong A T).d y =
      gammaAlong n (geoTransformAlong B T).N (geoTransformAlong B T).ideal (geoTransformAlong B T).E
        (geoTransformAlong B T).d y := by
    unfold gammaAlong
    rw [hexp, hET, d_geoTransformAlong, d_geoTransformAlong, hd]
  rw [hγ]

/-- **E1 for `canonicalInvariant`, boundary included.** -/
theorem mixedEquiv_canonicalInvariant_fst_eq {k : ℕ} {X : CMfd.{0} (k + 1)} {A B : MarkedIdeal (k + 1) X}
    (h : MixedEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B) (hN : B.N = A.N) (hd : B.d = A.d)
    (h0 : ExpAgree A B) {Y : CMfd.{0} (k + 1)} (T : BlowupTower X Y) (hT : IsGeoTestTower A T) {y : Y}
    (hy : y ∈ (geoTransformAlong A T).cosupp) :
    fstEntry ((canonicalInvariant.{0} (k + 1)).inv A T y) = fstEntry ((canonicalInvariant.{0} (k + 1)).inv B T y) :=
  mixedEquiv_nmOrd_geoTransformAlong_eq h hA hB hN hd h0 T hT hy

/-- **E1 for `canonicalInvariant` from an empty initial boundary** (the initial window records): on the whole
cosupport along every common multiple test blowup. -/
theorem mixedEquiv_canonicalInvariant_fst_eq_of_nil {k : ℕ} {X : CMfd.{0} (k + 1)} {A B : MarkedIdeal (k + 1) X}
    (h : MixedEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B) (hN : B.N = A.N) (hd : B.d = A.d)
    (hE : A.E = []) {Y : CMfd.{0} (k + 1)} (T : BlowupTower X Y) (hT : IsGeoTestTower A T) {y : Y}
    (hy : y ∈ (geoTransformAlong A T).cosupp) :
    fstEntry ((canonicalInvariant.{0} (k + 1)).inv A T y) = fstEntry ((canonicalInvariant.{0} (k + 1)).inv B T y) :=
  mixedEquiv_canonicalInvariant_fst_eq h hA hB hN hd (expAgree_of_nil hE) T hT hy

/-- **E3 for `canonicalInvariant`**: at the points of order `0` the full values agree. -/
theorem mixedEquiv_canonicalInvariant_eq_of_nmOrd_eq_zero {k : ℕ} {X : CMfd.{0} (k + 1)}
    {A B : MarkedIdeal (k + 1) X} (h : MixedEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hN : B.N = A.N) (hd : B.d = A.d) (h0 : ExpAgree A B) {Y : CMfd.{0} (k + 1)} (T : BlowupTower X Y)
    (hT : IsGeoTestTower A T) {y : Y} (hy : y ∈ (geoTransformAlong A T).cosupp)
    (hzero : nmOrd (geoTransformAlong A T) y = 0) :
    (canonicalInvariant.{0} (k + 1)).inv A T y = (canonicalInvariant.{0} (k + 1)).inv B T y :=
  mixedEquiv_genInv_eq_of_nmOrd_eq_zero _ h hA hB hN hd h0 T hT hy hzero

end Tower

end

end Hironaka.HironakaG8MixedBoundaryExponents
