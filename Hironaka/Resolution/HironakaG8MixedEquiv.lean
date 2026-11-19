import Hironaka.Resolution.HironakaActualMixedTestPowerNormalization
import Hironaka.MarkedIdeal.MarkedIdealEquivalence
import Hironaka.Resolution.HironakaG8LogClosureHistory

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Mixed-test equivalence of marked ideals (G8 lane, run 0080, round 2; toward D01–D03)

Blueprint: `hironaka-g8-resume-mixed-equivalence.tex`.

Bierstone–Milman's equivalence of marked ideals (BM08 §1, §3; BM97 §1 conditions (1)–(3)) quantifies over sequences of
three kinds of test transformations: admissible blowups, products with a line, and exceptional blowups (of the
intersection of two boundary members).  These are exactly the actions of the existing mixed histories
`HironakaActualMixedTestPowerNormalization.History` (controlled / projection / exceptional).  This module defines

* `MixedEquiv M M'`: the same boundary `E`, the same mixed test histories, and the same cosupports along them;

and proves its calculus:

* histories: concatenation `append` (`carrier_append`, `wholeIdeal_append`, `record_append`, `isTest_append`) and
  blowup towers as histories (`towerHistory`, `record_towerHistory`, `isTest_towerHistory_iff`);
* `MixedEquiv.refl`, `.symm`, `.trans`, and the constructor `MixedEquiv.of_cosupp` (equal cosupports along common
  tests already force the same tests);
* **stability under transforms**: `MixedEquiv.record` (the records along a common test history are equivalent);
* comparison with the blowup-only equivalence: `MixedEquiv.wEquiv` (Włodarczyk's `WEquiv`) and
  **`MixedEquiv.projectionTest_wEquiv`** (`WEquiv` after one product with a line), the input of the existing normalized
  order detection `HironakaActualProjectedNormalizedOrderDetection.normalized_ordinary_order_of_projected_wEquiv`;
* instances: `mixedEquiv_powerMarked` (`M ~ M^e`), `MixedEquiv.pow`, **`MixedEquiv.commonMark`** (common-mark
  normalization `M^{d'} ~ M'^{d}`), and `mixedEquiv_logClosure` (`M ~ 𝓒^k(M)`, BM08 Theorem 3.10 / Corollary 3.11 in the
  log form of `HironakaG8LogClosureHistory`).

Sorry-free.  Import discipline: no import of `Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8MixedEquiv

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals
  MarkedIdeals.MarkedIdeal
open Hironaka.ResolutionInvariantSpec (IsInvDomain)
open Hironaka.BlowupStrictSubmanifold (geoStrictTransform)
open Hironaka.HironakaActualMixedTestPowerNormalization
open Hironaka.HironakaActualProjectionTestRecord (projectionTest projectionAmbient)
open Hironaka.HironakaActualPowerBoundaryExponents (powerMarked powerMarked_cosupp
  powerMarked_isInvDomain)
open Hironaka.MarkedIdealEquivalence.MarkedIdeal (WEquiv)
open scoped ProductComplexManifold

noncomputable section

/-! ### Concatenation of mixed histories -/

section Append

variable {n : ℕ} {X : CMfd.{u} n} {E : List (Set X)}

/-- **Concatenation of mixed histories**: `H₀` followed by the actions of `H₁`. -/
def append {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)} (H₀ : History X E Y F) :
    {p : ℕ} → {Z : CMfd.{u} p} → {G : List (Set Z)} → History Y F Z G → History X E Z G
  | _, _, _, .refl => H₀
  | _, _, _, .controlled H C π hπ => .controlled (append H₀ H) C π hπ
  | _, _, _, .projection H => .projection (append H₀ H)
  | _, _, _, .exceptional H i j hij π hπ => .exceptional (append H₀ H) i j hij π hπ

/-- The proper carrier along a concatenation is the carrier along the second history of the carrier along the first. -/
theorem carrier_append (N : Set X) {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)} (H₀ : History X E Y F) :
    ∀ {p : ℕ} {Z : CMfd.{u} p} {G : List (Set Z)} (H₁ : History Y F Z G),
      carrier N (append H₀ H₁) = carrier (carrier N H₀) H₁
  | _, _, _, .refl => rfl
  | _, _, _, .controlled H C π hπ => by
    simp only [append, carrier, carrier_append N H₀ H]
  | _, _, _, .projection H => by
    simp only [append, carrier, carrier_append N H₀ H]
  | _, _, _, .exceptional H i j hij π hπ => by
    simp only [append, carrier, carrier_append N H₀ H]
    rfl

/-- The whole ideal along a concatenation is the whole ideal along the second history of the whole ideal along the
first (same mark). -/
theorem wholeIdeal_append (N : Set X) (I : GermIdeal n X) (d : ℕ) {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)}
    (H₀ : History X E Y F) :
    ∀ {p : ℕ} {Z : CMfd.{u} p} {G : List (Set Z)} (H₁ : History Y F Z G),
      wholeIdeal N I d (append H₀ H₁) = wholeIdeal (carrier N H₀) (wholeIdeal N I d H₀) d H₁
  | _, _, _, .refl => rfl
  | _, _, _, .controlled H C π hπ => by
    simp only [append, wholeIdeal, carrier_append N H₀ H, wholeIdeal_append N I d H₀ H]
  | _, _, _, .projection H => by
    simp only [append, wholeIdeal, wholeIdeal_append N I d H₀ H]
  | _, _, _, .exceptional H i j hij π hπ => by
    simp only [append, wholeIdeal, wholeIdeal_append N I d H₀ H]

/-- **The record along a concatenation is the record of the record.** -/
theorem record_append (M : MarkedIdeal n X) {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)} (H₀ : History X M.E Y F)
    {p : ℕ} {Z : CMfd.{u} p} {G : List (Set Z)} (H₁ : History Y F Z G) :
    record M (append H₀ H₁) = record (record M H₀) H₁ := by
  show (⟨carrier M.N (append H₀ H₁), G, wholeIdeal M.N M.ideal M.d (append H₀ H₁), M.d⟩ : MarkedIdeal p Z) =
    ⟨carrier (carrier M.N H₀) H₁, G, wholeIdeal (carrier M.N H₀) (wholeIdeal M.N M.ideal M.d H₀) M.d H₁, M.d⟩
  rw [carrier_append, wholeIdeal_append]

/-- **Tests along a concatenation**: `H₀ H₁` is a test history of `M` iff `H₀` is one and `H₁` is a test history of
the record `M_{H₀}`. -/
theorem isTest_append (M : MarkedIdeal n X) {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)} (H₀ : History X M.E Y F) :
    ∀ {p : ℕ} {Z : CMfd.{u} p} {G : List (Set Z)} (H₁ : History Y F Z G),
      IsTest M (append H₀ H₁) ↔ IsTest M H₀ ∧ IsTest (record M H₀) H₁
  | _, _, _, .refl => ⟨fun h => ⟨h, trivial⟩, And.left⟩
  | _, _, _, .controlled H C π hπ => by
    show IsTest M (append H₀ H) ∧ (record M (append H₀ H)).IsAdmissibleCentre C ↔
      IsTest M H₀ ∧ (IsTest (record M H₀) H ∧ (record (record M H₀) H).IsAdmissibleCentre C)
    rw [isTest_append M H₀ H, record_append, and_assoc]
  | _, _, _, .projection H => isTest_append M H₀ H
  | _, _, _, .exceptional H _ _ _ _ _ => isTest_append M H₀ H

end Append

/-! ### Blowup towers as mixed histories -/

section Tower

variable {n : ℕ} {X : CMfd.{u} n} {E : List (Set X)}

/-- The boundary after a blowup tower: the strict transforms of the old members, the new exceptional divisor last. -/
def towerBoundary {m : ℕ} {Y : CMfd.{u} m} (F : List (Set Y)) :
    {Z : CMfd.{u} m} → BlowupTower Y Z → List (Set Z)
  | _, .refl => F
  | _, .step T C π _ => (towerBoundary F T).map (geoStrictTransform π C) ++ [π ⁻¹' C]

/-- **A blowup tower as a mixed history**: `H` followed by the controlled actions of `T`. -/
def towerHistory {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)} (H : History X E Y F) :
    {Z : CMfd.{u} m} → (T : BlowupTower Y Z) → History X E Z (towerBoundary F T)
  | _, .refl => H
  | _, .step T C π hπ => .controlled (towerHistory H T) C π hπ

/-- **The record along `H` followed by a tower is the transform of the record along the tower.** -/
theorem record_towerHistory (M : MarkedIdeal n X) {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)}
    (H : History X M.E Y F) {Z : CMfd.{u} m} (T : BlowupTower Y Z) :
    record M (towerHistory H T) = geoTransformAlong (record M H) T := by
  induction T with
  | refl => rfl
  | step T C π hπ ih =>
    show (record M (towerHistory H T)).geoTransform C π = (geoTransformAlong (record M H) T).geoTransform C π
    rw [ih]

/-- **Tests along `H` followed by a tower.** -/
theorem isTest_towerHistory_iff (M : MarkedIdeal n X) {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)}
    (H : History X M.E Y F) {Z : CMfd.{u} m} (T : BlowupTower Y Z) :
    IsTest M (towerHistory H T) ↔ IsTest M H ∧ IsGeoTestTower (record M H) T := by
  induction T with
  | refl => exact ⟨fun h => ⟨h, trivial⟩, And.left⟩
  | step T C π hπ ih =>
    show IsTest M (towerHistory H T) ∧ (record M (towerHistory H T)).IsAdmissibleCentre C ↔
      IsTest M H ∧ (IsGeoTestTower (record M H) T ∧ (geoTransformAlong (record M H) T).IsAdmissibleCentre C)
    rw [ih, record_towerHistory, and_assoc]

/-- A blowup tower over the base is a mixed history from `refl`; the record is the transform. -/
theorem record_towerHistory_refl (M : MarkedIdeal n X) {Z : CMfd.{u} n} (T : BlowupTower X Z) :
    record M (towerHistory (.refl : History X M.E X M.E) T) = geoTransformAlong M T :=
  record_towerHistory M .refl T

theorem isTest_towerHistory_refl_iff (M : MarkedIdeal n X) {Z : CMfd.{u} n} (T : BlowupTower X Z) :
    IsTest M (towerHistory (.refl : History X M.E X M.E) T) ↔ IsGeoTestTower M T :=
  (isTest_towerHistory_iff M .refl T).trans ⟨And.right, fun h => ⟨trivial, h⟩⟩

end Tower

/-! ### Mixed-test equivalence -/

section Equiv

variable {n : ℕ} {X : CMfd.{u} n}

/-- `M` with its boundary replaced by `E` (to read `M` along the histories of another marked ideal with the same
boundary). -/
def withBoundary (M : MarkedIdeal n X) (E : List (Set X)) : MarkedIdeal n X :=
  ⟨M.N, E, M.ideal, M.d⟩

theorem withBoundary_eq {M : MarkedIdeal n X} {E : List (Set X)} (h : M.E = E) : withBoundary M E = M := by
  obtain ⟨N, E', I, d⟩ := M
  change E' = E at h
  subst h
  rfl

@[simp] theorem withBoundary_self (M : MarkedIdeal n X) : withBoundary M M.E = M :=
  withBoundary_eq rfl

/-- **Mixed-test equivalence** (Bierstone–Milman's equivalence for the test transformations admissible blowup,
product with a line, exceptional blowup): the same boundary, the same mixed test histories, and the same cosupports
along them. -/
def MixedEquiv (M M' : MarkedIdeal n X) : Prop :=
  M'.E = M.E ∧ ∀ {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)} (H : History X M.E Y F),
    (IsTest M H ↔ IsTest (withBoundary M' M.E) H) ∧
      (IsTest M H → (record M H).cosupp = (record (withBoundary M' M.E) H).cosupp)

variable {M M' M'' : MarkedIdeal n X}

/-- The same boundary. -/
theorem MixedEquiv.E_eq (h : MixedEquiv M M') : M'.E = M.E := h.1

/-- The same tests. -/
theorem MixedEquiv.isTest_iff (h : MixedEquiv M M') {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)}
    (H : History X M.E Y F) : IsTest M H ↔ IsTest (withBoundary M' M.E) H :=
  (h.2 H).1

/-- The same cosupports along the tests. -/
theorem MixedEquiv.cosupp_eq (h : MixedEquiv M M') {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)}
    (H : History X M.E Y F) (hH : IsTest M H) : (record M H).cosupp = (record (withBoundary M' M.E) H).cosupp :=
  (h.2 H).2 hH

/-- In particular the same cosupport. -/
theorem MixedEquiv.cosupp_eq_base (h : MixedEquiv M M') : M.cosupp = M'.cosupp :=
  h.cosupp_eq .refl trivial

/-- **Admissibility depends only on the cosupport and the boundary.** -/
theorem isAdmissibleCentre_congr {p : ℕ} {Z : CMfd.{u} p} {𝔪 𝔫 : MarkedIdeal p Z} (hE : 𝔪.E = 𝔫.E)
    (hc : 𝔪.cosupp = 𝔫.cosupp) (C : Set Z) : 𝔪.IsAdmissibleCentre C ↔ 𝔫.IsAdmissibleCentre C := by
  unfold IsAdmissibleCentre
  rw [hc, hE]

/-- **Equal cosupports along common tests force the same tests** (by induction on the history: admissibility of the
next centre depends only on the current cosupport and boundary). -/
theorem isTest_iff_of_cosupp {M₁ M₂ : MarkedIdeal n X} (hE : M₂.E = M₁.E)
    (hc : ∀ {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)} (H : History X M₁.E Y F), IsTest M₁ H →
      IsTest (withBoundary M₂ M₁.E) H → (record M₁ H).cosupp = (record (withBoundary M₂ M₁.E) H).cosupp) :
    ∀ {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)} (H : History X M₁.E Y F),
      IsTest M₁ H ↔ IsTest (withBoundary M₂ M₁.E) H
  | _, _, _, .refl => Iff.rfl
  | _, _, _, .controlled H C π hπ => by
    have ih := isTest_iff_of_cosupp hE hc H
    show IsTest M₁ H ∧ (record M₁ H).IsAdmissibleCentre C ↔
      IsTest (withBoundary M₂ M₁.E) H ∧ (record (withBoundary M₂ M₁.E) H).IsAdmissibleCentre C
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨ih.mp h1, (isAdmissibleCentre_congr (𝔪 := record M₁ H) (𝔫 := record (withBoundary M₂ M₁.E) H)
        rfl (hc H h1 (ih.mp h1)) C).mp h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨ih.mpr h1, (isAdmissibleCentre_congr (𝔪 := record M₁ H) (𝔫 := record (withBoundary M₂ M₁.E) H)
        rfl (hc H (ih.mpr h1) h1) C).mpr h2⟩
  | _, _, _, .projection H => isTest_iff_of_cosupp hE hc H
  | _, _, _, .exceptional H _ _ _ _ _ => isTest_iff_of_cosupp hE hc H

/-- **Constructor**: the same boundary and equal cosupports along the common tests. -/
theorem MixedEquiv.of_cosupp (hE : M'.E = M.E)
    (hc : ∀ {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)} (H : History X M.E Y F), IsTest M H →
      IsTest (withBoundary M' M.E) H → (record M H).cosupp = (record (withBoundary M' M.E) H).cosupp) :
    MixedEquiv M M' :=
  ⟨hE, fun H => ⟨isTest_iff_of_cosupp hE hc H, fun hH => hc H hH ((isTest_iff_of_cosupp hE hc H).mp hH)⟩⟩

theorem MixedEquiv.refl (M : MarkedIdeal n X) : MixedEquiv M M :=
  ⟨rfl, fun _ => ⟨Iff.rfl, fun _ => rfl⟩⟩

theorem MixedEquiv.symm (h : MixedEquiv M M') : MixedEquiv M' M := by
  obtain ⟨N, E, I, d⟩ := M
  obtain ⟨N', E', I', d'⟩ := M'
  obtain ⟨hE, h⟩ := h
  change E' = E at hE
  subst hE
  exact ⟨rfl, fun H => ⟨(h H).1.symm, fun hH => ((h H).2 ((h H).1.mpr hH)).symm⟩⟩

theorem MixedEquiv.trans (h : MixedEquiv M M') (h' : MixedEquiv M' M'') : MixedEquiv M M'' := by
  obtain ⟨N, E, I, d⟩ := M
  obtain ⟨N', E', I', d'⟩ := M'
  obtain ⟨N'', E'', I'', d''⟩ := M''
  obtain ⟨hE, h⟩ := h
  obtain ⟨hE', h'⟩ := h'
  change E' = E at hE
  change E'' = E' at hE'
  subst hE hE'
  exact ⟨rfl, fun H => ⟨(h H).1.trans (h' H).1, fun hH => ((h H).2 hH).trans ((h' H).2 ((h H).1.mp hH))⟩⟩

/-- **Stability under transforms**: along a common test history the records are again mixed-test equivalent (every
history of the record is the tail of a concatenation). -/
theorem MixedEquiv.record (h : MixedEquiv M M') {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)}
    (H₀ : History X M.E Y F) (hH₀ : IsTest M H₀) :
    MixedEquiv (record M H₀) (record (withBoundary M' M.E) H₀) := by
  obtain ⟨N, E, I, d⟩ := M
  obtain ⟨N', E', I', d'⟩ := M'
  obtain ⟨hE, h⟩ := h
  change E' = E at hE
  subst hE
  have hH₀' : IsTest (⟨N', E', I', d'⟩ : MarkedIdeal n X) H₀ := (h H₀).1.mp hH₀
  refine ⟨rfl, fun H₁ => ?_⟩
  have hA := isTest_append (⟨N, E', I, d⟩ : MarkedIdeal n X) H₀ H₁
  have hB := isTest_append (⟨N', E', I', d'⟩ : MarkedIdeal n X) H₀ H₁
  have hiff : IsTest (HironakaActualMixedTestPowerNormalization.record (⟨N, E', I, d⟩ : MarkedIdeal n X) H₀) H₁ ↔
      IsTest (HironakaActualMixedTestPowerNormalization.record (⟨N', E', I', d'⟩ : MarkedIdeal n X) H₀) H₁ := by
    constructor
    · intro h1
      exact (hB.mp ((h (append H₀ H₁)).1.mp (hA.mpr ⟨hH₀, h1⟩))).2
    · intro h1
      exact (hA.mp ((h (append H₀ H₁)).1.mpr (hB.mpr ⟨hH₀', h1⟩))).2
  refine ⟨hiff, fun h1 => ?_⟩
  have hc := (h (append H₀ H₁)).2 (hA.mpr ⟨hH₀, h1⟩)
  have e1 := record_append (⟨N, E', I, d⟩ : MarkedIdeal n X) H₀ H₁
  have e2 := record_append (⟨N', E', I', d'⟩ : MarkedIdeal n X) H₀ H₁
  show (HironakaActualMixedTestPowerNormalization.record
      (HironakaActualMixedTestPowerNormalization.record (⟨N, E', I, d⟩ : MarkedIdeal n X) H₀) H₁).cosupp =
    (HironakaActualMixedTestPowerNormalization.record
      (HironakaActualMixedTestPowerNormalization.record (⟨N', E', I', d'⟩ : MarkedIdeal n X) H₀) H₁).cosupp
  exact (congrArg MarkedIdeal.cosupp e1).symm.trans (hc.trans (congrArg MarkedIdeal.cosupp e2))

/-- **Mixed-test equivalence implies Włodarczyk's equivalence** (blowup towers are mixed histories). -/
theorem MixedEquiv.wEquiv (h : MixedEquiv M M') : WEquiv M M' := by
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
  obtain ⟨h1, h2⟩ := h (towerHistory (.refl : History X E' X E') T)
  refine ⟨hA.symm.trans (h1.trans hB), fun hT => ?_⟩
  exact (congrArg MarkedIdeal.cosupp rA).symm.trans ((h2 (hA.mpr hT)).trans (congrArg MarkedIdeal.cosupp rB))

/-- **Mixed-test equivalence implies Włodarczyk's equivalence after one product with a line**: the input of
`HironakaActualProjectedNormalizedOrderDetection.normalized_ordinary_order_of_projected_wEquiv`. -/
theorem MixedEquiv.projectionTest_wEquiv (h : MixedEquiv M M') : WEquiv (projectionTest M) (projectionTest M') := by
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
  refine ⟨hA.symm.trans (h1.trans hB), fun hT => ?_⟩
  exact (congrArg MarkedIdeal.cosupp rA).symm.trans ((h2 (hA.mpr hT)).trans (congrArg MarkedIdeal.cosupp rB))

/-- **`M ~ M^e`** (`e ≥ 1`, native domain): the original power has the same mixed tests and cuts
(`original_power_test_iff`, `original_power_normalization`). -/
theorem mixedEquiv_powerMarked {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M) {e : ℕ} (he : 1 ≤ e) :
    MixedEquiv M (powerMarked M e) := by
  refine ⟨rfl, fun H => ⟨(original_power_test_iff M hM he H).symm, fun hH => ?_⟩⟩
  have hr := (original_power_normalization M hM e he H hH).2
  have hd := record_isInvDomain M hM H hH
  exact (hr.cosupp_eq.trans (powerMarked_cosupp (record M H) hd he)).symm

/-- **Powers of equivalent marked ideals are equivalent.** -/
theorem MixedEquiv.pow {k k' : ℕ} (h : MixedEquiv M M') (hM : IsInvDomain k M) (hM' : IsInvDomain k' M')
    {e : ℕ} (he : 1 ≤ e) : MixedEquiv (powerMarked M e) (powerMarked M' e) :=
  ((mixedEquiv_powerMarked M hM he).symm.trans h).trans (mixedEquiv_powerMarked M' hM' he)

/-- **Common-mark normalization**: if `M ~ M'` then `M^{d'} ~ M'^{d}`, both of mark `d d'`. -/
theorem MixedEquiv.commonMark {k k' : ℕ} (h : MixedEquiv M M') (hM : IsInvDomain k M) (hM' : IsInvDomain k' M') :
    MixedEquiv (powerMarked M M'.d) (powerMarked M' M.d) ∧ (powerMarked M M'.d).d = (powerMarked M' M.d).d :=
  ⟨((mixedEquiv_powerMarked M hM hM'.one_le_d).symm.trans h).trans (mixedEquiv_powerMarked M' hM' hM.one_le_d),
    Nat.mul_comm _ _⟩

end Equiv

/-! ### The logarithmic closure (universe 0, as in `HironakaG8LogClosureHistory`) -/

section LogClosure

open Hironaka.HironakaActualIteratedLogMarkedFamily (bmFiniteSum rawLogMarked)
open Hironaka.HironakaG8LogClosureHistory (mixed_logClosure_isTest_iff mixed_logClosure_cosupp)

variable {n : ℕ} {X : CMfd.{0} n}

/-- **`M ~ 𝓒^k(M)`** (`k < d`, native domain): BM08 Theorem 3.10 / Corollary 3.11 along the mixed histories, as a
mixed-test equivalence. -/
theorem mixedEquiv_logClosure (M : MarkedIdeal n X) {r : ℕ} (hM : IsInvDomain r M) {k : ℕ} (hk : k < M.d) :
    MixedEquiv M (bmFiniteSum (rawLogMarked M) (k + 1)) :=
  ⟨rfl, fun H => ⟨(mixed_logClosure_isTest_iff M hM hk H).symm,
    fun hH => (mixed_logClosure_cosupp M hM hk H hH).1.symm⟩⟩

end LogClosure

end

end Hironaka.HironakaG8MixedEquiv
