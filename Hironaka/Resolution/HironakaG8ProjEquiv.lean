import Hironaka.Resolution.HironakaG8MixedBoundaryExponents

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Equivalence for admissible blowups and products with a line; entries E1–E3 from it (G8 lane, run 0080, round 2; D01)

Blueprint: `hironaka-g8-resume-proj-equivalence.tex`.  Route note: `work/hironaka-resume-20261111/G8/D01-ROUTE-r2.md`.

`HironakaG8MixedBoundaryExponents` proved the entries E1–E3 of `CanonicalCentres.canonicalInvariant` constant on
same-mark `MixedEquiv` classes (all three test transformations of BM97 §1, exceptional blowups included).  Those proofs
only use (a) the same multiple test blowups and cosupports, and (b) Bierstone–Milman's Prop. 4.8 along towers, which
only needs products with a line.  Exceptional blowups are needed by BM only to detect the exponents of INITIAL boundary
members (BM97 Prop. 4.11), which is unnecessary when the initial exponents agree (e.g. `E = []`).  The weaker relation
matters for the induction behind D01: BM97 Prop. 4.24 shows that the companion construction respects their relation
`s*` (only special exceptional blowups), not the full one, so the deeper entries can only be compared through a relation
without arbitrary exceptional blowups.  This module

* defines `NoExc` (mixed histories without exceptional actions; closed under `append`, `towerHistory`) and
  **`ProjEquiv`** (BM's equivalence `s(i,ii)`: the same tests and cosupports along every such history), with
  `MixedEquiv.projEquiv`, `ProjEquiv.refl`, `.symm`, `.trans`, **`ProjEquiv.record`**, `ProjEquiv.wEquiv`,
  `ProjEquiv.projectionTest_wEquiv`, `projEquiv_powerMarked`, `ProjEquiv.commonMark`;
* proves Prop. 4.8 for it along histories (`projEquiv_normalizedOrder`, `projEquiv_normalizedOrder_record`) and along
  towers with equal marks (`projEquiv_towerOrdAgree`);
* proves E1–E3 from the two facts (a), (b) only (`TowerOrdAgree`; `expAgree_geoTransformAlong_of_ordAgree`,
  `nmOrd_geoTransformAlong_eq_of_ordAgree`, `regimeRun_eq_of_ordAgree`, `genInv_eq_of_ordAgree_of_nmOrd_eq_zero`), and
  the `ProjEquiv` forms for `canonicalInvariant` (`projEquiv_canonicalInvariant_fst_eq`,
  `projEquiv_canonicalInvariant_eq_of_nmOrd_eq_zero`, `projEquiv_regimeRun_eq`).

Sorry-free.  Import discipline: no import of `Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8ProjEquiv

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals
  MarkedIdeals.MarkedIdeal GermIdealOrder RelativePrincipalizationSpan DivisorExponentAlong
open Hironaka.ResolutionInvariantSpec (IsInvDomain)
open Hironaka.BlowupStrictSubmanifold (geoStrictTransform geoStrictTransform_subset_preimage)
open Hironaka.NonmonomialOrderLocal (nmOrd)
open Hironaka.HironakaSharpOriginalProductTraceOrder (ordinaryTraceOrder
  ordinaryTraceOrder_cosupport_iff)
open Hironaka.HironakaActualMixedTestPowerNormalization
open Hironaka.HironakaActualProjectionTestRecord (projectionTest)
open Hironaka.HironakaActualPowerBoundaryExponents (powerMarked powerMarked_cosupp)
open Hironaka.MarkedIdealEquivalence.MarkedIdeal (WEquiv)
open Hironaka.HironakaG8MixedEquiv
open Hironaka.HironakaG8MixedOrderInvariance (fstEntry)
open Hironaka.HironakaG8MixedBoundaryExponents
open Hironaka.MonomialCaseAlong (expDataAlong gammaAlong)
open Hironaka.StepOneRegime (regimeRun regimeRun_step)
open Hironaka.NonmonomialOrderRegime (OrdRegime)
open Hironaka.CanonicalCentres (canonicalInvariant)

noncomputable section

/-! ### Histories without exceptional actions -/

section NoExc

variable {n : ℕ} {X : CMfd.{u} n} {E : List (Set X)}

/-- **A mixed history without exceptional actions** (only admissible blowups and products with a line). -/
def NoExc : {m : ℕ} → {Y : CMfd.{u} m} → {F : List (Set Y)} → History X E Y F → Prop
  | _, _, _, .refl => True
  | _, _, _, .controlled H _ _ _ => NoExc H
  | _, _, _, .projection H => NoExc H
  | _, _, _, .exceptional _ _ _ _ _ _ => False

theorem noExc_refl : NoExc (.refl : History X E X E) := trivial

theorem noExc_projection {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)} (H : History X E Y F) (hH : NoExc H) :
    NoExc (.projection H) := hH

theorem noExc_append {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)} (H₀ : History X E Y F) :
    ∀ {p : ℕ} {Z : CMfd.{u} p} {G : List (Set Z)} (H₁ : History Y F Z G),
      NoExc (append H₀ H₁) ↔ NoExc H₀ ∧ NoExc H₁
  | _, _, _, .refl => ⟨fun h => ⟨h, trivial⟩, And.left⟩
  | _, _, _, .controlled H _ _ _ => noExc_append H₀ H
  | _, _, _, .projection H => noExc_append H₀ H
  | _, _, _, .exceptional _ _ _ _ _ _ => ⟨fun h => h.elim, fun h => h.2.elim⟩

theorem noExc_towerHistory {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)} (H : History X E Y F) (hH : NoExc H) :
    ∀ {Z : CMfd.{u} m} (T : BlowupTower Y Z), NoExc (towerHistory H T)
  | _, .refl => hH
  | _, .step T _ _ _ => noExc_towerHistory H hH T

end NoExc

/-! ### The equivalence `s(i,ii)` -/

section Equiv

variable {n : ℕ} {X : CMfd.{u} n} {M M' M'' : MarkedIdeal n X}

/-- **Equivalence for admissible blowups and products with a line** (BM97's `s(i,ii)`): the same boundary, the same
test histories without exceptional actions, and the same cosupports along them. -/
def ProjEquiv (M M' : MarkedIdeal n X) : Prop :=
  M'.E = M.E ∧ ∀ {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)} (H : History X M.E Y F), NoExc H →
    (IsTest M H ↔ IsTest (withBoundary M' M.E) H) ∧
      (IsTest M H → (record M H).cosupp = (record (withBoundary M' M.E) H).cosupp)

/-- Mixed-test equivalence implies `s(i,ii)`-equivalence. -/
theorem MixedEquiv.projEquiv (h : MixedEquiv M M') : ProjEquiv M M' :=
  ⟨h.1, fun H _ => h.2 H⟩

theorem ProjEquiv.E_eq (h : ProjEquiv M M') : M'.E = M.E := h.1

theorem ProjEquiv.refl (M : MarkedIdeal n X) : ProjEquiv M M :=
  ⟨rfl, fun _ _ => ⟨Iff.rfl, fun _ => rfl⟩⟩

theorem ProjEquiv.symm (h : ProjEquiv M M') : ProjEquiv M' M := by
  obtain ⟨N, E, I, d⟩ := M
  obtain ⟨N', E', I', d'⟩ := M'
  obtain ⟨hE, h⟩ := h
  change E' = E at hE
  subst hE
  exact ⟨rfl, fun H hn => ⟨(h H hn).1.symm, fun hH => ((h H hn).2 ((h H hn).1.mpr hH)).symm⟩⟩

theorem ProjEquiv.trans (h : ProjEquiv M M') (h' : ProjEquiv M' M'') : ProjEquiv M M'' := by
  obtain ⟨N, E, I, d⟩ := M
  obtain ⟨N', E', I', d'⟩ := M'
  obtain ⟨N'', E'', I'', d''⟩ := M''
  obtain ⟨hE, h⟩ := h
  obtain ⟨hE', h'⟩ := h'
  change E' = E at hE
  change E'' = E' at hE'
  subst hE hE'
  exact ⟨rfl, fun H hn => ⟨(h H hn).1.trans (h' H hn).1,
    fun hH => ((h H hn).2 hH).trans ((h' H hn).2 ((h H hn).1.mp hH))⟩⟩

/-- **Stability under transforms** along a common test history without exceptional actions. -/
theorem ProjEquiv.record (h : ProjEquiv M M') {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)}
    (H₀ : History X M.E Y F) (hH₀ : IsTest M H₀) (hn₀ : NoExc H₀) :
    ProjEquiv (record M H₀) (record (withBoundary M' M.E) H₀) := by
  obtain ⟨N, E, I, d⟩ := M
  obtain ⟨N', E', I', d'⟩ := M'
  obtain ⟨hE, h⟩ := h
  change E' = E at hE
  subst hE
  have hH₀' : IsTest (⟨N', E', I', d'⟩ : MarkedIdeal n X) H₀ := (h H₀ hn₀).1.mp hH₀
  refine ⟨rfl, fun H₁ hn₁ => ?_⟩
  have hn : NoExc (append H₀ H₁) := (noExc_append H₀ H₁).mpr ⟨hn₀, hn₁⟩
  have hA := isTest_append (⟨N, E', I, d⟩ : MarkedIdeal n X) H₀ H₁
  have hB := isTest_append (⟨N', E', I', d'⟩ : MarkedIdeal n X) H₀ H₁
  have hiff : IsTest (HironakaActualMixedTestPowerNormalization.record (⟨N, E', I, d⟩ : MarkedIdeal n X) H₀) H₁ ↔
      IsTest (HironakaActualMixedTestPowerNormalization.record (⟨N', E', I', d'⟩ : MarkedIdeal n X) H₀) H₁ := by
    constructor
    · intro h1
      exact (hB.mp ((h (append H₀ H₁) hn).1.mp (hA.mpr ⟨hH₀, h1⟩))).2
    · intro h1
      exact (hA.mp ((h (append H₀ H₁) hn).1.mpr (hB.mpr ⟨hH₀', h1⟩))).2
  refine ⟨hiff, fun h1 => ?_⟩
  have hc := (h (append H₀ H₁) hn).2 (hA.mpr ⟨hH₀, h1⟩)
  have e1 := record_append (⟨N, E', I, d⟩ : MarkedIdeal n X) H₀ H₁
  have e2 := record_append (⟨N', E', I', d'⟩ : MarkedIdeal n X) H₀ H₁
  show (HironakaActualMixedTestPowerNormalization.record
      (HironakaActualMixedTestPowerNormalization.record (⟨N, E', I, d⟩ : MarkedIdeal n X) H₀) H₁).cosupp =
    (HironakaActualMixedTestPowerNormalization.record
      (HironakaActualMixedTestPowerNormalization.record (⟨N', E', I', d'⟩ : MarkedIdeal n X) H₀) H₁).cosupp
  exact (congrArg MarkedIdeal.cosupp e1).symm.trans (hc.trans (congrArg MarkedIdeal.cosupp e2))

/-- `s(i,ii)`-equivalence implies Włodarczyk's equivalence. -/
theorem ProjEquiv.wEquiv (h : ProjEquiv M M') : WEquiv M M' := by
  obtain ⟨N, E, I, d⟩ := M
  obtain ⟨N', E', I', d'⟩ := M'
  obtain ⟨hE, h⟩ := h
  change E' = E at hE
  subst hE
  refine ⟨rfl, fun T => ?_⟩
  have hA := isTest_towerHistory_refl_iff (⟨N, E', I, d⟩ : MarkedIdeal n X) T
  have hB := isTest_towerHistory_refl_iff (⟨N', E', I', d'⟩ : MarkedIdeal n X) T
  have rA := record_towerHistory_refl (⟨N, E', I, d⟩ : MarkedIdeal n X) T
  have rB := record_towerHistory_refl (⟨N', E', I', d'⟩ : MarkedIdeal n X) T
  obtain ⟨h1, h2⟩ := h (towerHistory (.refl : History X E' X E') T) (noExc_towerHistory .refl noExc_refl T)
  refine ⟨hA.symm.trans (h1.trans hB), fun hT => ?_⟩
  exact (congrArg MarkedIdeal.cosupp rA).symm.trans ((h2 (hA.mpr hT)).trans (congrArg MarkedIdeal.cosupp rB))

/-- `s(i,ii)`-equivalence gives Włodarczyk's equivalence after one product with a line. -/
theorem ProjEquiv.projectionTest_wEquiv (h : ProjEquiv M M') : WEquiv (projectionTest M) (projectionTest M') := by
  obtain ⟨N, E, I, d⟩ := M
  obtain ⟨N', E', I', d'⟩ := M'
  obtain ⟨hE, h⟩ := h
  change E' = E at hE
  subst hE
  refine ⟨rfl, fun T => ?_⟩
  have hA : IsTest (⟨N, E', I, d⟩ : MarkedIdeal n X) (towerHistory (.projection (.refl : History X E' X E')) T) ↔
      IsGeoTestTower (projectionTest (⟨N, E', I, d⟩ : MarkedIdeal n X)) T :=
    (isTest_towerHistory_iff (⟨N, E', I, d⟩ : MarkedIdeal n X) (.projection .refl) T).trans
      ⟨And.right, fun h => ⟨trivial, h⟩⟩
  have hB : IsTest (⟨N', E', I', d'⟩ : MarkedIdeal n X) (towerHistory (.projection (.refl : History X E' X E')) T) ↔
      IsGeoTestTower (projectionTest (⟨N', E', I', d'⟩ : MarkedIdeal n X)) T :=
    (isTest_towerHistory_iff (⟨N', E', I', d'⟩ : MarkedIdeal n X) (.projection .refl) T).trans
      ⟨And.right, fun h => ⟨trivial, h⟩⟩
  have rA : HironakaActualMixedTestPowerNormalization.record (⟨N, E', I, d⟩ : MarkedIdeal n X)
      (towerHistory (.projection (.refl : History X E' X E')) T) =
        geoTransformAlong (projectionTest (⟨N, E', I, d⟩ : MarkedIdeal n X)) T :=
    record_towerHistory (⟨N, E', I, d⟩ : MarkedIdeal n X) (.projection .refl) T
  have rB : HironakaActualMixedTestPowerNormalization.record (⟨N', E', I', d'⟩ : MarkedIdeal n X)
      (towerHistory (.projection (.refl : History X E' X E')) T) =
        geoTransformAlong (projectionTest (⟨N', E', I', d'⟩ : MarkedIdeal n X)) T :=
    record_towerHistory (⟨N', E', I', d'⟩ : MarkedIdeal n X) (.projection .refl) T
  obtain ⟨h1, h2⟩ := h (towerHistory (.projection (.refl : History X E' X E')) T)
    (noExc_towerHistory (.projection .refl) (noExc_projection .refl noExc_refl) T)
  refine ⟨hA.symm.trans (h1.trans hB), fun hT => ?_⟩
  exact (congrArg MarkedIdeal.cosupp rA).symm.trans ((h2 (hA.mpr hT)).trans (congrArg MarkedIdeal.cosupp rB))

/-- `M ~ M^e` for `s(i,ii)` (`e ≥ 1`, native domain). -/
theorem projEquiv_powerMarked {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M) {e : ℕ} (he : 1 ≤ e) :
    ProjEquiv M (powerMarked M e) :=
  MixedEquiv.projEquiv (mixedEquiv_powerMarked M hM he)

/-- **Common-mark normalization** for `s(i,ii)`: `M ~ M'` gives `M^{d'} ~ M'^{d}`, both of mark `d d'`. -/
theorem ProjEquiv.commonMark {k k' : ℕ} (h : ProjEquiv M M') (hM : IsInvDomain k M) (hM' : IsInvDomain k' M') :
    ProjEquiv (powerMarked M M'.d) (powerMarked M' M.d) ∧ (powerMarked M M'.d).d = (powerMarked M' M.d).d :=
  ⟨((projEquiv_powerMarked M hM hM'.one_le_d).symm.trans h).trans (projEquiv_powerMarked M' hM' hM.one_le_d),
    Nat.mul_comm _ _⟩

/-- **BM97 Prop. 4.8 for `s(i,ii)`**: `d' ord_x(𝔞|_N) = d ord_x(𝔞'|_N)` on the common cosupport (same carrier). -/
theorem projEquiv_normalizedOrder {kA kB : ℕ} {A B : MarkedIdeal n X} (h : ProjEquiv A B) (hA : IsInvDomain kA A)
    (hB : IsInvDomain kB B) (hN : B.N = A.N) {x : X} (hx : x ∈ A.cosupp) :
    B.d * ordinaryTraceOrder A.N A.ideal x = A.d * ordinaryTraceOrder B.N B.ideal x := by
  have hxB : x ∈ B.cosupp := h.wEquiv.cosupp_eq ▸ hx
  exact (HironakaActualProjectedNormalizedOrderDetection.normalized_ordinary_order_of_projected_wEquiv A B hA hB x hx
    hxB hN h.E_eq h.projectionTest_wEquiv).2.2

/-- **BM97 Prop. 4.8 for `s(i,ii)` along every common test history without exceptional actions.** -/
theorem projEquiv_normalizedOrder_record {kA kB : ℕ} {A B : MarkedIdeal n X} (h : ProjEquiv A B)
    (hA : IsInvDomain kA A) (hB : IsInvDomain kB B) (hN : B.N = A.N) {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)}
    (H : History X A.E Y F) (hH : IsTest A H) (hn : NoExc H) {y : Y} (hy : y ∈ (record A H).cosupp) :
    B.d * ordinaryTraceOrder (record A H).N (record A H).ideal y =
      A.d * ordinaryTraceOrder (record (withBoundary B A.E) H).N (record (withBoundary B A.E) H).ideal y := by
  have hB' : IsInvDomain kB (withBoundary B A.E) := (withBoundary_eq h.E_eq).symm ▸ hB
  have hHB : IsTest (withBoundary B A.E) H := ((h.2 H hn).1).mp hH
  have hRA := record_isInvDomain A hA H hH
  have hRB := record_isInvDomain (withBoundary B A.E) hB' H hHB
  have hNr : (record (withBoundary B A.E) H).N = (record A H).N := by
    show carrier B.N H = carrier A.N H
    rw [hN]
  exact projEquiv_normalizedOrder (h.record H hH hn) hRA hRB hNr hy

end Equiv

/-! ### Entries E1–E3 from equal orders along towers -/

section Entries

variable {n : ℕ} {X : CMfd.{0} n} {kA kB : ℕ} {A B : MarkedIdeal n X}

/-- **Equal ordinary orders on the cosupport along every common multiple test blowup.** -/
def TowerOrdAgree (A B : MarkedIdeal n X) : Prop :=
  ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), IsGeoTestTower A T → ∀ y ∈ (geoTransformAlong A T).cosupp,
    ordinaryTraceOrder (geoTransformAlong A T).N (geoTransformAlong A T).ideal y =
      ordinaryTraceOrder (geoTransformAlong B T).N (geoTransformAlong B T).ideal y

/-- **Same-mark `s(i,ii)`-equivalent marked ideals have equal orders along towers** (Prop. 4.8, marks cancelled). -/
theorem projEquiv_towerOrdAgree (h : ProjEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hN : B.N = A.N) (hd : B.d = A.d) : TowerOrdAgree A B := by
  intro Y T hT y hy
  have rA := record_towerHistory_refl A T
  have rB : record (withBoundary B A.E) (towerHistory (.refl : History X A.E X A.E) T) = geoTransformAlong B T :=
    (record_towerHistory_refl (withBoundary B A.E) T).trans
      (congrArg (fun M => geoTransformAlong M T) (withBoundary_eq h.E_eq))
  have hH : IsTest A (towerHistory (.refl : History X A.E X A.E) T) := (isTest_towerHistory_refl_iff A T).mpr hT
  have hy' : y ∈ (record A (towerHistory (.refl : History X A.E X A.E) T)).cosupp := by
    rw [rA]
    exact hy
  have h1 := projEquiv_normalizedOrder_record h hA hB hN (towerHistory .refl T) hH
    (noExc_towerHistory .refl noExc_refl T) hy'
  rw [rA, rB, hd] at h1
  exact Nat.eq_of_mul_eq_mul_left (Nat.lt_of_lt_of_le Nat.zero_lt_one hA.one_le_d) h1

/-- Exponents along an admissible centre, from equal orders. -/
theorem divExpAlong_centre_eq_of_ordAgree (hW : WEquiv A B) (hOrd : TowerOrdAgree A B) (hA : IsInvDomain kA A)
    (hB : IsInvDomain kB B) (hN : B.N = A.N) {Y : CMfd.{0} n} (T : BlowupTower X Y) (hT : IsGeoTestTower A T)
    {C : Set Y} (hC : (geoTransformAlong A T).IsAdmissibleCentre C) (x : Y) :
    divExpAlong n (geoTransformAlong A T).N (geoTransformAlong A T).ideal C x =
      divExpAlong n (geoTransformAlong B T).N (geoTransformAlong B T).ideal C x := by
  have hNT := carrier_geoTransformAlong_eq hN T
  have hTB : IsGeoTestTower B T := (hW.2 T).1.mp hT
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
    have ho := hOrd T hT z (hC.2.1 hzC)
    exact (iffB hzB e).mpr (ho ▸ (iffA hzA e).mp (hz hzA hzC))
  · intro hz hzA hzC
    have hzB : z ∈ (geoTransformAlong B T).N := hNT.symm ▸ hzA
    have ho := hOrd T hT z (hC.2.1 hzC)
    exact (iffA hzA e).mpr (ho.symm ▸ (iffB hzB e).mp (hz hzB hzC))

/-- **Boundary exponents along common test towers, from equal orders** (initial exponents agreeing). -/
theorem expAgree_geoTransformAlong_of_ordAgree (hW : WEquiv A B) (hOrd : TowerOrdAgree A B) (hA : IsInvDomain kA A)
    (hB : IsInvDomain kB B) (hN : B.N = A.N) (hd : B.d = A.d) (h0 : ExpAgree A B) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), IsGeoTestTower A T →
      ExpAgree (geoTransformAlong A T) (geoTransformAlong B T)
  | _, .refl, _ => h0
  | _, .step T C π hπ, hT => by
    obtain ⟨hTT, hC⟩ := (isGeoTestTower_step_iff A T C π hπ).mp hT
    have hTB : IsGeoTestTower B T := (hW.2 T).1.mp hTT
    have hcos : (geoTransformAlong A T).cosupp = (geoTransformAlong B T).cosupp := (hW.2 T).2 hTT
    have hET : (geoTransformAlong B T).E = (geoTransformAlong A T).E :=
      MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq hW.1.symm T
    have hCB : (geoTransformAlong B T).IsAdmissibleCentre C :=
      (isAdmissibleCentre_congr hET.symm hcos C).mp hC
    have hdA := InvDomainTowerAlong.isInvDomain_geoTransformAlong hA T hTT
    have hNT := carrier_geoTransformAlong_eq hN T
    have ih := expAgree_geoTransformAlong_of_ordAgree hW hOrd hA hB hN hd h0 T hTT
    intro H hH z hz hzH
    have hzN : z ∈ ((geoTransformAlong A T).geoTransform C π).N :=
      ((geoTransformAlong A T).geoTransform C π).cosupp_subset_N hz
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
      rw [bA, bB, divExpAlong_centre_eq_of_ordAgree hW hOrd hA hB hN T hTT hC (π z), hd]

/-- **E1 from equal orders**: the orders of the nonmonomial parts agree on the cosupport, boundary included. -/
theorem nmOrd_geoTransformAlong_eq_of_ordAgree (hW : WEquiv A B) (hOrd : TowerOrdAgree A B) (hA : IsInvDomain kA A)
    (hB : IsInvDomain kB B) (hN : B.N = A.N) (hd : B.d = A.d) (h0 : ExpAgree A B) {Y : CMfd.{0} n}
    (T : BlowupTower X Y) (hT : IsGeoTestTower A T) {y : Y} (hy : y ∈ (geoTransformAlong A T).cosupp) :
    nmOrd (geoTransformAlong A T) y = nmOrd (geoTransformAlong B T) y := by
  have hTB : IsGeoTestTower B T := (hW.2 T).1.mp hT
  exact nmOrd_eq_of_expAgree (InvDomainTowerAlong.isInvDomain_geoTransformAlong hA T hT)
    (InvDomainTowerAlong.isInvDomain_geoTransformAlong hB T hTB) (carrier_geoTransformAlong_eq hN T)
    (MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq hW.1.symm T)
    (expAgree_geoTransformAlong_of_ordAgree hW hOrd hA hB hN hd h0 T hT) hy (hOrd T hT y hy)

/-- **E2 from equal orders**: the regime runs agree. -/
theorem regimeRun_eq_of_ordAgree (hW : WEquiv A B) (hOrd : TowerOrdAgree A B) (hA : IsInvDomain kA A)
    (hB : IsInvDomain kB B) (hN : B.N = A.N) (hd : B.d = A.d) (h0 : ExpAgree A B) (o : ℕ) :
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
        exact ⟨hcos ▸ h1, (nmOrd_geoTransformAlong_eq_of_ordAgree hW hOrd hA hB hN hd h0 T hTT h1).symm.trans h2⟩
      · rintro ⟨h1, h2⟩
        have h1' : π z ∈ (geoTransformAlong A T).cosupp := hcos.symm ▸ h1
        exact ⟨h1', (nmOrd_geoTransformAlong_eq_of_ordAgree hW hOrd hA hB hN hd h0 T hTT h1').trans h2⟩
    rw [regimeRun_step, regimeRun_step, regimeRun_eq_of_ordAgree hW hOrd hA hB hN hd h0 o T hTT (π z)]
    by_cases hP : OrdRegime A o T (π z)
    · rw [if_pos hP, if_pos (hiff.mp hP)]
    · rw [if_neg hP, if_neg (fun h' => hP (hiff.mpr h'))]

/-- **E3 from equal orders**: at the points of order `0` the full general values agree. -/
theorem genInv_eq_of_ordAgree_of_nmOrd_eq_zero {Λ : Type} [LinearOrder Λ]
    (M : ∀ {X : CMfd.{0} n}, MarkedIdeal n X → ∀ {Y : CMfd.{0} n}, BlowupTower X Y → Y → Λ)
    (hW : WEquiv A B) (hOrd : TowerOrdAgree A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B) (hN : B.N = A.N)
    (hd : B.d = A.d) (h0 : ExpAgree A B) {Y : CMfd.{0} n} (T : BlowupTower X Y) (hT : IsGeoTestTower A T) {y : Y}
    (hy : y ∈ (geoTransformAlong A T).cosupp) (hzero : nmOrd (geoTransformAlong A T) y = 0) :
    GeneralValue.genInv M A T y = GeneralValue.genInv M B T y := by
  have hnm := nmOrd_geoTransformAlong_eq_of_ordAgree hW hOrd hA hB hN hd h0 T hT hy
  rw [GeneralValue.genInv_of_nmOrd_eq_zero M A T hzero,
    GeneralValue.genInv_of_nmOrd_eq_zero M B T (hnm.symm.trans hzero)]
  have hexp := expDataAlong_eq_of_expAgree (InvDomainTowerAlong.isInvDomain_geoTransformAlong hA T hT).isWellFormed
    (carrier_geoTransformAlong_eq hN T) (MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq hW.1.symm T)
    (expAgree_geoTransformAlong_of_ordAgree hW hOrd hA hB hN hd h0 T hT) hy
  have hET : (geoTransformAlong B T).E = (geoTransformAlong A T).E :=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq hW.1.symm T
  have hγ : gammaAlong n (geoTransformAlong A T).N (geoTransformAlong A T).ideal (geoTransformAlong A T).E
      (geoTransformAlong A T).d y =
      gammaAlong n (geoTransformAlong B T).N (geoTransformAlong B T).ideal (geoTransformAlong B T).E
        (geoTransformAlong B T).d y := by
    unfold gammaAlong
    rw [hexp, hET, d_geoTransformAlong, d_geoTransformAlong, hd]
  rw [hγ]

/-! ### The `s(i,ii)` forms -/

/-- **E1 for `s(i,ii)`**: same carrier, same mark, agreeing initial exponents. -/
theorem projEquiv_nmOrd_geoTransformAlong_eq (h : ProjEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hN : B.N = A.N) (hd : B.d = A.d) (h0 : ExpAgree A B) {Y : CMfd.{0} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower A T) {y : Y} (hy : y ∈ (geoTransformAlong A T).cosupp) :
    nmOrd (geoTransformAlong A T) y = nmOrd (geoTransformAlong B T) y :=
  nmOrd_geoTransformAlong_eq_of_ordAgree h.wEquiv (projEquiv_towerOrdAgree h hA hB hN hd) hA hB hN hd h0 T hT hy

/-- **E2 for `s(i,ii)`.** -/
theorem projEquiv_regimeRun_eq (h : ProjEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hN : B.N = A.N) (hd : B.d = A.d) (h0 : ExpAgree A B) (o : ℕ) {Y : CMfd.{0} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower A T) (y : Y) : regimeRun (OrdRegime A o) T y = regimeRun (OrdRegime B o) T y :=
  regimeRun_eq_of_ordAgree h.wEquiv (projEquiv_towerOrdAgree h hA hB hN hd) hA hB hN hd h0 o T hT y

/-- **E1 for `canonicalInvariant` and `s(i,ii)`**, boundary included. -/
theorem projEquiv_canonicalInvariant_fst_eq {k : ℕ} {X : CMfd.{0} (k + 1)} {A B : MarkedIdeal (k + 1) X}
    (h : ProjEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B) (hN : B.N = A.N) (hd : B.d = A.d)
    (h0 : ExpAgree A B) {Y : CMfd.{0} (k + 1)} (T : BlowupTower X Y) (hT : IsGeoTestTower A T) {y : Y}
    (hy : y ∈ (geoTransformAlong A T).cosupp) :
    fstEntry ((canonicalInvariant.{0} (k + 1)).inv A T y) = fstEntry ((canonicalInvariant.{0} (k + 1)).inv B T y) :=
  projEquiv_nmOrd_geoTransformAlong_eq h hA hB hN hd h0 T hT hy

/-- **E3 for `canonicalInvariant` and `s(i,ii)`**: at the points of order `0` the full values agree. -/
theorem projEquiv_canonicalInvariant_eq_of_nmOrd_eq_zero {k : ℕ} {X : CMfd.{0} (k + 1)}
    {A B : MarkedIdeal (k + 1) X} (h : ProjEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hN : B.N = A.N) (hd : B.d = A.d) (h0 : ExpAgree A B) {Y : CMfd.{0} (k + 1)} (T : BlowupTower X Y)
    (hT : IsGeoTestTower A T) {y : Y} (hy : y ∈ (geoTransformAlong A T).cosupp)
    (hzero : nmOrd (geoTransformAlong A T) y = 0) :
    (canonicalInvariant.{0} (k + 1)).inv A T y = (canonicalInvariant.{0} (k + 1)).inv B T y :=
  genInv_eq_of_ordAgree_of_nmOrd_eq_zero _ h.wEquiv (projEquiv_towerOrdAgree h hA hB hN hd) hA hB hN hd h0 T hT hy
    hzero

end Entries

end

end Hironaka.HironakaG8ProjEquiv
