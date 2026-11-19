import Hironaka.Resolution.HironakaG8P1NormalizedOrder

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Entries E1–E3 for carriers that differ (G8B lane, run 0080; port P1, second half)

Blueprint: `hironaka-g8-p1-entries.tex`.  Plan: lane G11B's `BPRIME-PLAN.md` §2, port P1 ("Then E1–E3 with different
carriers"); lane G8's `HironakaG8ProjEquiv` §Entries proves E1–E3 from `TowerOrdAgree` for `B.N = A.N`.

Lane G8's generic entries (`divExpAlong_centre_eq_of_ordAgree`, `expAgree_geoTransformAlong_of_ordAgree`,
`nmOrd_geoTransformAlong_eq_of_ordAgree`, `regimeRun_eq_of_ordAgree`, `genInv_eq_of_ordAgree_of_nmOrd_eq_zero`) use the
carrier equality only to move points between the two carriers; every such point lies on an admissible centre or in the
cosupport, which is common to both records and contained in both carriers.  This module re-proves them for carriers that
differ (`_of_ordAgree'` names), and with `HironakaG8P1NormalizedOrder.towerOrdAgree_of_projEquiv` (BM08 Thm 6.1 for
different carriers of equal dimension) obtains the `s(i,ii)` and `LocWPEquiv` forms:

* E1 `projEquiv_nmOrd_geoTransformAlong_eq'`, `locWPEquiv_nmOrd_geoTransformAlong_eq`, and for `canonicalInvariant`
  `projEquiv_canonicalInvariant_fst_eq'`;
* E2 `projEquiv_regimeRun_eq'`, `locWPEquiv_regimeRun_eq`;
* E3 `projEquiv_genInv_eq_of_nmOrd_eq_zero'` (any lower value), `projEquiv_canonicalInvariant_eq_of_nmOrd_eq_zero'`;

all under: same mark, `SameCarrierDim`, agreeing initial boundary exponents (`ExpAgree`, vacuous for `E = []`).

Sorry-free.  Import discipline: no import of `Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8P1Entries

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals
  MarkedIdeals.MarkedIdeal GermIdealOrder RelativePrincipalizationSpan DivisorExponentAlong
open Hironaka.ResolutionInvariantSpec (IsInvDomain)
open Hironaka.BlowupStrictSubmanifold (geoStrictTransform geoStrictTransform_subset_preimage)
open Hironaka.NonmonomialOrderLocal (nmOrd)
open Hironaka.HironakaSharpOriginalProductTraceOrder (ordinaryTraceOrder
  ordinaryTraceOrder_cosupport_iff)
open Hironaka.HironakaActualMixedTestPowerNormalization
open Hironaka.HironakaG8MixedEquiv
open Hironaka.HironakaG8MixedOrderInvariance (fstEntry)
open Hironaka.HironakaG8MixedBoundaryExponents
open Hironaka.HironakaG8ProjEquiv
open Hironaka.MonomialCase (memberIdx)
open Hironaka.MonomialCaseAlong (expDataAlong gammaAlong)
open Hironaka.StepOneRegime (regimeRun regimeRun_step)
open Hironaka.NonmonomialOrderRegime (OrdRegime)
open Hironaka.CanonicalCentres (canonicalInvariant)
open Hironaka.MarkedIdealEquivalence.MarkedIdeal (WEquiv)
open Hironaka.HironakaG11InvBMClass (SameCarrierDim)
open Hironaka.HironakaG8LocalHistory (LocWPEquiv LocEquiv)

noncomputable section

/-! ### One stage -/

section Exponent

variable {m : ℕ} {Y : CMfd.{0} m}

/-- The exponent data at a cosupport point agree if the exponents along the members through it agree (carriers may
differ). -/
theorem expDataAlong_eq_of_expAgree' {P Q : MarkedIdeal m Y} (hP : P.IsWellFormed) (hQ : Q.IsWellFormed)
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
      have hclQ : IsClosed (Q.N ∩ P.E.get ⟨i, hi⟩) :=
        hQ.isClosedSubmanifold_N.1.inter (hP.isSNCDivisor.1 _ (List.get_mem _ _))
      rw [divExpAlong_eq_zero_of_notMem hcl (fun h => hyH h.2),
        divExpAlong_eq_zero_of_notMem hclQ (fun h => hyH h.2)]
  · rfl

/-- **`ord = Σ β + nmOrd` on both carriers**: equal ordinary orders and agreeing exponents at a common cosupport point
give equal first entries (carriers may differ). -/
theorem nmOrd_eq_of_expAgree' {kP kQ : ℕ} {P Q : MarkedIdeal m Y} (hP : IsInvDomain kP P) (hQ : IsInvDomain kQ Q)
    (hE : Q.E = P.E) (hag : ExpAgree P Q) {y : Y} (hy : y ∈ P.cosupp) (hyQ : y ∈ Q.N)
    (hord : ordinaryTraceOrder P.N P.ideal y = ordinaryTraceOrder Q.N Q.ideal y) : nmOrd P y = nmOrd Q y := by
  have hm := pos_of_mem_cosupp hP hy
  have hyN : y ∈ P.N := P.cosupp_subset_N hy
  obtain ⟨-, -, hoP, -⟩ := HironakaActualCoefficientNonmonomialHistoryOrder.whole_factor_order hm P
    hP.isWellFormed hP.isNonzeroAlongAt y hyN
  obtain ⟨-, -, hoQ, -⟩ := HironakaActualCoefficientNonmonomialHistoryOrder.whole_factor_order hm Q
    hQ.isWellFormed hQ.isNonzeroAlongAt y hyQ
  have hexp := expDataAlong_eq_of_expAgree' hP.isWellFormed hQ.isWellFormed hE hag hy
  have hs : (∑ i ∈ memberIdx Q.E y, expDataAlong m Q.N Q.ideal Q.E y i) =
      ∑ i ∈ memberIdx P.E y, expDataAlong m P.N P.ideal P.E y i := by
    rw [← hexp, hE]
  rw [hs] at hoQ
  omega

end Exponent

/-! ### Along common test towers -/

section Tower

variable {n : ℕ} {X : CMfd.{0} n} {kA kB : ℕ} {A B : MarkedIdeal n X}

/-- Exponents along an admissible centre, from equal orders (carriers may differ). -/
theorem divExpAlong_centre_eq_of_ordAgree' (hW : WEquiv A B) (hOrd : TowerOrdAgree A B) (hA : IsInvDomain kA A)
    (hB : IsInvDomain kB B) {Y : CMfd.{0} n} (T : BlowupTower X Y) (hT : IsGeoTestTower A T)
    {C : Set Y} (hC : (geoTransformAlong A T).IsAdmissibleCentre C) (x : Y) :
    divExpAlong n (geoTransformAlong A T).N (geoTransformAlong A T).ideal C x =
      divExpAlong n (geoTransformAlong B T).N (geoTransformAlong B T).ideal C x := by
  have hTB : IsGeoTestTower B T := (hW.2 T).1.mp hT
  have hcos : (geoTransformAlong A T).cosupp = (geoTransformAlong B T).cosupp := (hW.2 T).2 hT
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
    have hzc : z ∈ (geoTransformAlong A T).cosupp := hC.2.1 hzC
    have hzA : z ∈ (geoTransformAlong A T).N := (geoTransformAlong A T).cosupp_subset_N hzc
    have ho := hOrd T hT z hzc
    exact (iffB hzB e).mpr (ho ▸ (iffA hzA e).mp (hz hzA hzC))
  · intro hz hzA hzC
    have hzc : z ∈ (geoTransformAlong A T).cosupp := hC.2.1 hzC
    have hzB : z ∈ (geoTransformAlong B T).N := (geoTransformAlong B T).cosupp_subset_N (hcos ▸ hzc)
    have ho := hOrd T hT z hzc
    exact (iffA hzA e).mpr (ho.symm ▸ (iffB hzB e).mp (hz hzB hzC))

/-- **Boundary exponents along common test towers, from equal orders** (initial exponents agreeing; carriers may
differ). -/
theorem expAgree_geoTransformAlong_of_ordAgree' (hW : WEquiv A B) (hOrd : TowerOrdAgree A B) (hA : IsInvDomain kA A)
    (hB : IsInvDomain kB B) (hd : B.d = A.d) (h0 : ExpAgree A B) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), IsGeoTestTower A T →
      ExpAgree (geoTransformAlong A T) (geoTransformAlong B T)
  | _, .refl, _ => h0
  | _, .step T C π hπ, hT => by
    obtain ⟨hTT, hC⟩ := (isGeoTestTower_step_iff A T C π hπ).mp hT
    have hTB : IsGeoTestTower B T := (hW.2 T).1.mp hTT
    have hcos : (geoTransformAlong A T).cosupp = (geoTransformAlong B T).cosupp := (hW.2 T).2 hTT
    have hcos' : ((geoTransformAlong A T).geoTransform C π).cosupp =
        ((geoTransformAlong B T).geoTransform C π).cosupp := (hW.2 (.step T C π hπ)).2 hT
    have hET : (geoTransformAlong B T).E = (geoTransformAlong A T).E :=
      MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq hW.1.symm T
    have hCB : (geoTransformAlong B T).IsAdmissibleCentre C :=
      (isAdmissibleCentre_congr hET.symm hcos C).mp hC
    have hdA := InvDomainTowerAlong.isInvDomain_geoTransformAlong hA T hTT
    have ih := expAgree_geoTransformAlong_of_ordAgree' hW hOrd hA hB hd h0 T hTT
    intro H hH z hz hzH
    have hzN : z ∈ ((geoTransformAlong A T).geoTransform C π).N :=
      ((geoTransformAlong A T).geoTransform C π).cosupp_subset_N hz
    have hzNB : z ∈ ((geoTransformAlong B T).geoTransform C π).N :=
      ((geoTransformAlong B T).geoTransform C π).cosupp_subset_N (hcos' ▸ hz)
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
      rw [bA, bB, divExpAlong_centre_eq_of_ordAgree' hW hOrd hA hB T hTT hC (π z), hd]

/-- **E1 from equal orders** (carriers may differ): the orders of the nonmonomial parts agree on the cosupport. -/
theorem nmOrd_geoTransformAlong_eq_of_ordAgree' (hW : WEquiv A B) (hOrd : TowerOrdAgree A B) (hA : IsInvDomain kA A)
    (hB : IsInvDomain kB B) (hd : B.d = A.d) (h0 : ExpAgree A B) {Y : CMfd.{0} n}
    (T : BlowupTower X Y) (hT : IsGeoTestTower A T) {y : Y} (hy : y ∈ (geoTransformAlong A T).cosupp) :
    nmOrd (geoTransformAlong A T) y = nmOrd (geoTransformAlong B T) y := by
  have hTB : IsGeoTestTower B T := (hW.2 T).1.mp hT
  have hcos : (geoTransformAlong A T).cosupp = (geoTransformAlong B T).cosupp := (hW.2 T).2 hT
  exact nmOrd_eq_of_expAgree' (InvDomainTowerAlong.isInvDomain_geoTransformAlong hA T hT)
    (InvDomainTowerAlong.isInvDomain_geoTransformAlong hB T hTB)
    (MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq hW.1.symm T)
    (expAgree_geoTransformAlong_of_ordAgree' hW hOrd hA hB hd h0 T hT) hy
    ((geoTransformAlong B T).cosupp_subset_N (hcos ▸ hy)) (hOrd T hT y hy)

/-- **E2 from equal orders** (carriers may differ): the regime runs agree. -/
theorem regimeRun_eq_of_ordAgree' (hW : WEquiv A B) (hOrd : TowerOrdAgree A B) (hA : IsInvDomain kA A)
    (hB : IsInvDomain kB B) (hd : B.d = A.d) (h0 : ExpAgree A B) (o : ℕ) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), IsGeoTestTower A T → ∀ y : Y,
      regimeRun (OrdRegime A o) T y = regimeRun (OrdRegime B o) T y
  | _, .refl, _, _ => rfl
  | _, .step T C π hπ, hT, z => by
    have hTT := ((isGeoTestTower_step_iff A T C π hπ).mp hT).1
    have hcos : (geoTransformAlong A T).cosupp = (geoTransformAlong B T).cosupp := (hW.2 T).2 hTT
    have hiff : OrdRegime A o T (π z) ↔ OrdRegime B o T (π z) := by
      show (π z ∈ (geoTransformAlong A T).cosupp ∧ nmOrd (geoTransformAlong A T) (π z) = o) ↔
        (π z ∈ (geoTransformAlong B T).cosupp ∧ nmOrd (geoTransformAlong B T) (π z) = o)
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨hcos ▸ h1, (nmOrd_geoTransformAlong_eq_of_ordAgree' hW hOrd hA hB hd h0 T hTT h1).symm.trans h2⟩
      · rintro ⟨h1, h2⟩
        have h1' : π z ∈ (geoTransformAlong A T).cosupp := hcos.symm ▸ h1
        exact ⟨h1', (nmOrd_geoTransformAlong_eq_of_ordAgree' hW hOrd hA hB hd h0 T hTT h1').trans h2⟩
    rw [regimeRun_step, regimeRun_step, regimeRun_eq_of_ordAgree' hW hOrd hA hB hd h0 o T hTT (π z)]
    by_cases hP : OrdRegime A o T (π z)
    · rw [if_pos hP, if_pos (hiff.mp hP)]
    · rw [if_neg hP, if_neg (fun h' => hP (hiff.mpr h'))]

/-- **E3 from equal orders** (carriers may differ): at the points of order `0` the full general values agree. -/
theorem genInv_eq_of_ordAgree_of_nmOrd_eq_zero' {Λ : Type} [LinearOrder Λ]
    (M : ∀ {X : CMfd.{0} n}, MarkedIdeal n X → ∀ {Y : CMfd.{0} n}, BlowupTower X Y → Y → Λ)
    (hW : WEquiv A B) (hOrd : TowerOrdAgree A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hd : B.d = A.d) (h0 : ExpAgree A B) {Y : CMfd.{0} n} (T : BlowupTower X Y) (hT : IsGeoTestTower A T) {y : Y}
    (hy : y ∈ (geoTransformAlong A T).cosupp) (hzero : nmOrd (geoTransformAlong A T) y = 0) :
    GeneralValue.genInv M A T y = GeneralValue.genInv M B T y := by
  have hnm := nmOrd_geoTransformAlong_eq_of_ordAgree' hW hOrd hA hB hd h0 T hT hy
  rw [GeneralValue.genInv_of_nmOrd_eq_zero M A T hzero,
    GeneralValue.genInv_of_nmOrd_eq_zero M B T (hnm.symm.trans hzero)]
  have hTB : IsGeoTestTower B T := (hW.2 T).1.mp hT
  have hexp := expDataAlong_eq_of_expAgree' (InvDomainTowerAlong.isInvDomain_geoTransformAlong hA T hT).isWellFormed
    (InvDomainTowerAlong.isInvDomain_geoTransformAlong hB T hTB).isWellFormed
    (MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq hW.1.symm T)
    (expAgree_geoTransformAlong_of_ordAgree' hW hOrd hA hB hd h0 T hT) hy
  have hET : (geoTransformAlong B T).E = (geoTransformAlong A T).E :=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq hW.1.symm T
  have hγ : gammaAlong n (geoTransformAlong A T).N (geoTransformAlong A T).ideal (geoTransformAlong A T).E
      (geoTransformAlong A T).d y =
      gammaAlong n (geoTransformAlong B T).N (geoTransformAlong B T).ideal (geoTransformAlong B T).E
        (geoTransformAlong B T).d y := by
    unfold gammaAlong
    rw [hexp, hET, d_geoTransformAlong, d_geoTransformAlong, hd]
  rw [hγ]

/-! ### The `s(i,ii)` and `LocWPEquiv` forms -/

/-- **E1 for `s(i,ii)`, carriers of equal dimension**: same mark, agreeing initial exponents. -/
theorem projEquiv_nmOrd_geoTransformAlong_eq' (h : ProjEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hdim : SameCarrierDim A B) (hd : B.d = A.d) (h0 : ExpAgree A B) {Y : CMfd.{0} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower A T) {y : Y} (hy : y ∈ (geoTransformAlong A T).cosupp) :
    nmOrd (geoTransformAlong A T) y = nmOrd (geoTransformAlong B T) y :=
  nmOrd_geoTransformAlong_eq_of_ordAgree' h.wEquiv
    (HironakaG8P1NormalizedOrder.towerOrdAgree_of_projEquiv h hA hB hdim hd) hA hB hd h0 T hT hy

/-- **E1 for `LocWPEquiv`, carriers of equal dimension.** -/
theorem locWPEquiv_nmOrd_geoTransformAlong_eq (h : LocWPEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hdim : SameCarrierDim A B) (hd : B.d = A.d) (h0 : ExpAgree A B) {Y : CMfd.{0} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower A T) {y : Y} (hy : y ∈ (geoTransformAlong A T).cosupp) :
    nmOrd (geoTransformAlong A T) y = nmOrd (geoTransformAlong B T) y :=
  projEquiv_nmOrd_geoTransformAlong_eq' (LocEquiv.projEquiv h) hA hB hdim hd h0 T hT hy

/-- **E2 for `s(i,ii)`, carriers of equal dimension.** -/
theorem projEquiv_regimeRun_eq' (h : ProjEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hdim : SameCarrierDim A B) (hd : B.d = A.d) (h0 : ExpAgree A B) (o : ℕ) {Y : CMfd.{0} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower A T) (y : Y) : regimeRun (OrdRegime A o) T y = regimeRun (OrdRegime B o) T y :=
  regimeRun_eq_of_ordAgree' h.wEquiv (HironakaG8P1NormalizedOrder.towerOrdAgree_of_projEquiv h hA hB hdim hd)
    hA hB hd h0 o T hT y

/-- **E2 for `LocWPEquiv`, carriers of equal dimension.** -/
theorem locWPEquiv_regimeRun_eq (h : LocWPEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hdim : SameCarrierDim A B) (hd : B.d = A.d) (h0 : ExpAgree A B) (o : ℕ) {Y : CMfd.{0} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower A T) (y : Y) : regimeRun (OrdRegime A o) T y = regimeRun (OrdRegime B o) T y :=
  projEquiv_regimeRun_eq' (LocEquiv.projEquiv h) hA hB hdim hd h0 o T hT y

/-- **E3 for `s(i,ii)`, carriers of equal dimension**: at the points of order `0` the full general values agree, for any
lower value function. -/
theorem projEquiv_genInv_eq_of_nmOrd_eq_zero' {Λ : Type} [LinearOrder Λ]
    (M : ∀ {X : CMfd.{0} n}, MarkedIdeal n X → ∀ {Y : CMfd.{0} n}, BlowupTower X Y → Y → Λ)
    (h : ProjEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B) (hdim : SameCarrierDim A B)
    (hd : B.d = A.d) (h0 : ExpAgree A B) {Y : CMfd.{0} n} (T : BlowupTower X Y) (hT : IsGeoTestTower A T) {y : Y}
    (hy : y ∈ (geoTransformAlong A T).cosupp) (hzero : nmOrd (geoTransformAlong A T) y = 0) :
    GeneralValue.genInv M A T y = GeneralValue.genInv M B T y :=
  genInv_eq_of_ordAgree_of_nmOrd_eq_zero' M h.wEquiv
    (HironakaG8P1NormalizedOrder.towerOrdAgree_of_projEquiv h hA hB hdim hd) hA hB hd h0 T hT hy hzero

/-- **E1 for `canonicalInvariant` and `s(i,ii)`, carriers of equal dimension**, boundary included. -/
theorem projEquiv_canonicalInvariant_fst_eq' {k : ℕ} {X : CMfd.{0} (k + 1)} {A B : MarkedIdeal (k + 1) X}
    (h : ProjEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B) (hdim : SameCarrierDim A B)
    (hd : B.d = A.d) (h0 : ExpAgree A B) {Y : CMfd.{0} (k + 1)} (T : BlowupTower X Y) (hT : IsGeoTestTower A T)
    {y : Y} (hy : y ∈ (geoTransformAlong A T).cosupp) :
    fstEntry ((canonicalInvariant.{0} (k + 1)).inv A T y) = fstEntry ((canonicalInvariant.{0} (k + 1)).inv B T y) :=
  projEquiv_nmOrd_geoTransformAlong_eq' h hA hB hdim hd h0 T hT hy

/-- **E3 for `canonicalInvariant` and `s(i,ii)`, carriers of equal dimension.** -/
theorem projEquiv_canonicalInvariant_eq_of_nmOrd_eq_zero' {k : ℕ} {X : CMfd.{0} (k + 1)}
    {A B : MarkedIdeal (k + 1) X} (h : ProjEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hdim : SameCarrierDim A B) (hd : B.d = A.d) (h0 : ExpAgree A B) {Y : CMfd.{0} (k + 1)} (T : BlowupTower X Y)
    (hT : IsGeoTestTower A T) {y : Y} (hy : y ∈ (geoTransformAlong A T).cosupp)
    (hzero : nmOrd (geoTransformAlong A T) y = 0) :
    (canonicalInvariant.{0} (k + 1)).inv A T y = (canonicalInvariant.{0} (k + 1)).inv B T y :=
  projEquiv_genInv_eq_of_nmOrd_eq_zero' _ h hA hB hdim hd h0 T hT hy hzero

end Tower

end

end Hironaka.HironakaG8P1Entries
