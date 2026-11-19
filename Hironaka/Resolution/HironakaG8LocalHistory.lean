import Hironaka.Resolution.HironakaG8ProjEquiv

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Local mixed histories and the local equivalences (G8 lane, run 0080, round 3; repair (B'), port P0 and locality)

Blueprint: `hironaka-g8-resume-local-histories.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §2 (P0),
G8 `REPORT-r2.md` finding (L).

Bierstone–Milman's equivalence of marked ideals is LOCAL: in the analytic category the test transformations are local
blowings-up (BM97 §1, Remark 1.8: "local blowings-up", a composite of the inclusion of an open subset and a blowing-up;
BM08 §5 Step I.A compares coefficient ideals "in overlapping charts", i.e. on open subsets).  The library's relations
(`WEquiv`, G8's `MixedEquiv`, `ProjEquiv`) quantify over towers/histories over the WHOLE base, and they do not formally
pass to open subsets: a test tower over an open `W` may have centres that are not closed in the base, and an open subset
of a later stage is not the preimage of an open subset of the base.  The companion ideal of the general value is formed on
an open mask (`GeneralValue.compAt`), the lower ideals on tangent opens, and the window records are compared on overlaps,
so the class-functoriality induction of (B') needs relations that restrict to opens of every stage.

This module adds the restriction as a fourth kind of test action:

* `LHist X E Y F`: **local mixed histories** — the actions of `HironakaActualMixedTestPowerNormalization.History`
  (admissible blowup, product with a line, exceptional blowup) plus `restrict H U` (restriction to an open subset `U` of the
  current stage, `CMfd.of U`, members `F.map (val⁻¹ ·)`); `carrier`, `wholeIdeal`, `record`, `IsTest` exactly as for
  `History`, the restriction acting by `MarkedIdeal.pullback Subtype.val` (`record_restrict`, `rfl`);
* `Kinds`, `InKinds`: which actions besides blowups and restrictions a history may use (`Kinds.w` none, `Kinds.wp`
  products with a line, `Kinds.bm` products and exceptional blowups);
* concatenation (`append`, `record_append`, `isTest_append`, `inKinds_append`), towers (`towerL`, `record_towerL`,
  `isTest_towerL_iff`), and the embedding of the global histories (`ofHist`, `record_ofHist`, `isTest_ofHist`);
* **`LocEquiv κ M M'`**: the same boundary, the same local test histories of kinds `κ`, the same cosupports along them;
  `LocWPEquiv = LocEquiv Kinds.wp` is the local form of BM's `s(i,ii)` (the relation `WPEquiv` of the (B') plan),
  `LocMixedEquiv = LocEquiv Kinds.bm` the local form of BM's equivalence (BM08 Defn 2.5), `LocWEquiv = LocEquiv Kinds.w` the
  local form of Włodarczyk's;
* calculus: `refl`, `symm`, `trans`, `mono` (fewer kinds), **`LocEquiv.record`** (stable along common local test histories,
  in particular at every node), **`LocEquiv.restrict`** (restriction to an open subset), `LocEquiv.geoTransformAlong`;
* comparison with the global relations at every node: `LocEquiv.wEquiv`, **`LocEquiv.projEquiv`** (from `Kinds.wp`),
  `LocEquiv.mixedEquiv` (from `Kinds.bm`), hence every result proved for `ProjEquiv`/`MixedEquiv` (E1–E3 of G8 r2) applies
  at every node of a local history, in particular to every restriction of every stage.

Sorry-free.  Import discipline: no import of `Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8LocalHistory

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec RelativePrincipalizationSpan InvertibleIdealQuotient
  IdealWeightPowers GermIdealPullbackCalculus RestrictedIdealExtension RestrictedIdealWeight RestrictedIdealQuotient
  RestrictLeCalculus MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal BlowupStrictSubmanifold
  HironakaActualProjectionTestRecord HironakaActualExceptionalTestRecord MarkedIdealBiholomorphism
open Hironaka.HironakaActualMixedTestPowerNormalization (History)
open Hironaka.HironakaG8MixedEquiv (withBoundary withBoundary_eq MixedEquiv towerBoundary
  towerHistory isAdmissibleCentre_congr)
open Hironaka.HironakaG8ProjEquiv (NoExc ProjEquiv)
open Hironaka.MarkedIdealEquivalence.MarkedIdeal (WEquiv)
open scoped ProductComplexManifold

noncomputable section

/-! ### Local mixed histories -/

/-- **Local mixed histories**: admissible blowups, products with a line, exceptional blowups, and restrictions to open
subsets of the current stage (geometry only: admissibility is imposed by `IsTest`). -/
inductive LHist {n : ℕ} (X : CMfd.{u} n) (E : List (Set X)) :
    {m : ℕ} → (Y : CMfd.{u} m) → List (Set Y) → Type (u+1)
  | refl : LHist X E X E
  | controlled {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)}
      (H : LHist X E Y F) (C : Set Y) {Z : CMfd.{u} m} (π : Z → Y)
      (hπ : IsBlowupAlong m C π) :
      LHist X E Z (F.map (geoStrictTransform π C) ++ [π ⁻¹' C])
  | projection {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)}
      (H : LHist X E Y F) : LHist X E (projectionAmbient Y)
        (F.map ((Prod.fst : projectionAmbient Y → Y) ⁻¹' ·) ++ [horizontal Y])
  | exceptional {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)}
      (H : LHist X E Y F) (i j : Fin F.length) (hij : i ≠ j)
      {Z : CMfd.{u} m} (π : Z → Y)
      (hπ : IsBlowupAlong m (F.get i ∩ F.get j) π) :
      LHist X E Z (F.map (geoStrictTransform π (F.get i ∩ F.get j)) ++
        [π ⁻¹' (F.get i ∩ F.get j)])
  | restrict {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)}
      (H : LHist X E Y F) (U : Opens Y) :
      LHist X E (CMfd.of (n := m) U) (F.map ((Subtype.val : U → Y) ⁻¹' ·))

namespace LHist

variable {n : ℕ} {X : CMfd.{u} n} {E : List (Set X)}

/-- The proper carrier along a local history. -/
def carrier (N : Set X) :
    {m : ℕ} → {Y : CMfd.{u} m} → {F : List (Set Y)} → LHist X E Y F → Set Y
  | _, _, _, .refl => N
  | _, _, _, .controlled H C π _ => geoStrictTransform π C (carrier N H)
  | _, _, _, .projection H => Prod.fst ⁻¹' carrier N H
  | _, _, _, @exceptional _ _ _ _ _ F H i j _ _ π _ => geoStrictTransform π (F.get i ∩ F.get j) (carrier N H)
  | _, _, _, .restrict H U => (Subtype.val : U → _) ⁻¹' carrier N H

/-- The whole ideal along a local history (only controlled actions have a denominator). -/
def wholeIdeal (N : Set X) (I : GermIdeal n X) (d : ℕ) :
    {m : ℕ} → {Y : CMfd.{u} m} → {F : List (Set Y)} → LHist X E Y F → GermIdeal m Y
  | _, _, _, .refl => I
  | m, _, _, .controlled H C π _ =>
    colonAlong m (geoStrictTransform π C (carrier N H))
      (GermIdeal.pullback (m := m) π (wholeIdeal N I d H))
      (idealPow (GermIdeal.pullback (m := m) π (vanishingIdeal (n := m) C)) d)
  | _, _, _, .projection H => GermIdeal.pullback Prod.fst (wholeIdeal N I d H)
  | _, _, _, .exceptional H _ _ _ π _ => GermIdeal.pullback π (wholeIdeal N I d H)
  | m, _, _, .restrict H U => GermIdeal.pullback (m := m) (Subtype.val : U → _) (wholeIdeal N I d H)

/-- The record of `M` along a local history: carrier, full boundary, whole ideal, original mark. -/
def record (M : MarkedIdeal n X) {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)}
    (H : LHist X M.E Y F) : MarkedIdeal m Y :=
  ⟨carrier M.N H, F, wholeIdeal M.N M.ideal M.d H, M.d⟩

theorem record_refl (M : MarkedIdeal n X) : record M (.refl : LHist X M.E X M.E) = M := rfl

theorem record_controlled (M : MarkedIdeal n X) {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)}
    (H : LHist X M.E Y F) (C : Set Y) {Z : CMfd.{u} m} (π : Z → Y) (hπ : IsBlowupAlong m C π) :
    record M (.controlled H C π hπ) = (record M H).geoTransform C π := rfl

theorem record_projection (M : MarkedIdeal n X) {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)}
    (H : LHist X M.E Y F) : record M (.projection H) = projectionTest (record M H) := rfl

theorem record_exceptional (M : MarkedIdeal n X) {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)}
    (H : LHist X M.E Y F) (i j : Fin F.length) (hij : i ≠ j) {Z : CMfd.{u} m} (π : Z → Y)
    (hπ : IsBlowupAlong m (F.get i ∩ F.get j) π) :
    record M (.exceptional H i j hij π hπ) = exceptionalTest (record M H) i j π := rfl

/-- **The record after a restriction is the restriction of the record.** -/
theorem record_restrict (M : MarkedIdeal n X) {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)}
    (H : LHist X M.E Y F) (U : Opens Y) :
    record M (.restrict H U) = MarkedIdeal.pullback (Subtype.val : U → Y) (record M H) := rfl

/-- Admissibility only at controlled actions. -/
def IsTest (M : MarkedIdeal n X) :
    {m : ℕ} → {Y : CMfd.{u} m} → {F : List (Set Y)} → LHist X M.E Y F → Prop
  | _, _, _, .refl => True
  | _, _, _, .controlled H C _ _ => IsTest M H ∧ (record M H).IsAdmissibleCentre C
  | _, _, _, .projection H => IsTest M H
  | _, _, _, .exceptional H _ _ _ _ _ => IsTest M H
  | _, _, _, .restrict H _ => IsTest M H

end LHist

/-! ### Kinds of actions -/

/-- Which test transformations a local history may use besides admissible blowups and restrictions to open subsets. -/
structure Kinds where
  /-- products with a line -/
  proj : Bool
  /-- exceptional blowups -/
  exc : Bool

/-- Blowups and restrictions only (Włodarczyk's equivalence, localized). -/
def Kinds.w : Kinds := ⟨false, false⟩
/-- Blowups, products with a line and restrictions (BM's `s(i,ii)`, localized). -/
def Kinds.wp : Kinds := ⟨true, false⟩
/-- All test transformations (BM08 Defn 2.5, localized). -/
def Kinds.bm : Kinds := ⟨true, true⟩

/-- `κ` allows at most the actions `κ'` allows. -/
def Kinds.Le (κ κ' : Kinds) : Prop := (κ.proj = true → κ'.proj = true) ∧ (κ.exc = true → κ'.exc = true)

theorem Kinds.le_refl (κ : Kinds) : κ.Le κ := ⟨id, id⟩

theorem Kinds.w_le (κ : Kinds) : Kinds.w.Le κ := ⟨fun h => absurd h Bool.false_ne_true, fun h => absurd h Bool.false_ne_true⟩

theorem Kinds.le_bm (κ : Kinds) : κ.Le Kinds.bm := ⟨fun _ => rfl, fun _ => rfl⟩

theorem Kinds.wp_le_bm : Kinds.wp.Le Kinds.bm := Kinds.le_bm _

namespace LHist

variable {n : ℕ} {X : CMfd.{u} n} {E : List (Set X)}

/-- The local history uses only actions of the kinds `κ` (blowups and restrictions are always allowed). -/
def InKinds (κ : Kinds) : {m : ℕ} → {Y : CMfd.{u} m} → {F : List (Set Y)} → LHist X E Y F → Prop
  | _, _, _, .refl => True
  | _, _, _, .controlled H _ _ _ => InKinds κ H
  | _, _, _, .projection H => κ.proj = true ∧ InKinds κ H
  | _, _, _, .exceptional H _ _ _ _ _ => κ.exc = true ∧ InKinds κ H
  | _, _, _, .restrict H _ => InKinds κ H

theorem InKinds.mono {κ κ' : Kinds} (hκ : κ.Le κ') :
    ∀ {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)} (H : LHist X E Y F), InKinds κ H → InKinds κ' H
  | _, _, _, .refl, _ => trivial
  | _, _, _, .controlled H _ _ _, h => InKinds.mono hκ H h
  | _, _, _, .projection H, h => ⟨hκ.1 h.1, InKinds.mono hκ H h.2⟩
  | _, _, _, .exceptional H _ _ _ _ _, h => ⟨hκ.2 h.1, InKinds.mono hκ H h.2⟩
  | _, _, _, .restrict H _, h => InKinds.mono hκ H h

theorem inKinds_bm : ∀ {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)} (H : LHist X E Y F), InKinds Kinds.bm H
  | _, _, _, .refl => trivial
  | _, _, _, .controlled H _ _ _ => inKinds_bm H
  | _, _, _, .projection H => ⟨rfl, inKinds_bm H⟩
  | _, _, _, .exceptional H _ _ _ _ _ => ⟨rfl, inKinds_bm H⟩
  | _, _, _, .restrict H _ => inKinds_bm H

theorem inKinds_refl (κ : Kinds) : InKinds κ (.refl : LHist X E X E) := trivial

/-! ### Concatenation -/

/-- **Concatenation**: `H₀` followed by the actions of `H₁`. -/
def append {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)} (H₀ : LHist X E Y F) :
    {p : ℕ} → {Z : CMfd.{u} p} → {G : List (Set Z)} → LHist Y F Z G → LHist X E Z G
  | _, _, _, .refl => H₀
  | _, _, _, .controlled H C π hπ => .controlled (append H₀ H) C π hπ
  | _, _, _, .projection H => .projection (append H₀ H)
  | _, _, _, .exceptional H i j hij π hπ => .exceptional (append H₀ H) i j hij π hπ
  | _, _, _, .restrict H U => .restrict (append H₀ H) U

theorem carrier_append (N : Set X) {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)} (H₀ : LHist X E Y F) :
    ∀ {p : ℕ} {Z : CMfd.{u} p} {G : List (Set Z)} (H₁ : LHist Y F Z G),
      carrier N (append H₀ H₁) = carrier (carrier N H₀) H₁
  | _, _, _, .refl => rfl
  | _, _, _, .controlled H C π hπ => by
    simp only [append, carrier, carrier_append N H₀ H]
  | _, _, _, .projection H => by
    simp only [append, carrier, carrier_append N H₀ H]
  | _, _, _, .exceptional H i j hij π hπ => by
    simp only [append, carrier, carrier_append N H₀ H]
  | _, _, _, .restrict H U => by
    simp only [append, carrier, carrier_append N H₀ H]

theorem wholeIdeal_append (N : Set X) (I : GermIdeal n X) (d : ℕ) {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)}
    (H₀ : LHist X E Y F) :
    ∀ {p : ℕ} {Z : CMfd.{u} p} {G : List (Set Z)} (H₁ : LHist Y F Z G),
      wholeIdeal N I d (append H₀ H₁) = wholeIdeal (carrier N H₀) (wholeIdeal N I d H₀) d H₁
  | _, _, _, .refl => rfl
  | _, _, _, .controlled H C π hπ => by
    simp only [append, wholeIdeal, carrier_append N H₀ H, wholeIdeal_append N I d H₀ H]
  | _, _, _, .projection H => by
    simp only [append, wholeIdeal, wholeIdeal_append N I d H₀ H]
  | _, _, _, .exceptional H i j hij π hπ => by
    simp only [append, wholeIdeal, wholeIdeal_append N I d H₀ H]
  | _, _, _, .restrict H U => by
    simp only [append, wholeIdeal, wholeIdeal_append N I d H₀ H]

/-- **The record along a concatenation is the record of the record.** -/
theorem record_append (M : MarkedIdeal n X) {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)} (H₀ : LHist X M.E Y F)
    {p : ℕ} {Z : CMfd.{u} p} {G : List (Set Z)} (H₁ : LHist Y F Z G) :
    record M (append H₀ H₁) = record (record M H₀) H₁ := by
  show (⟨carrier M.N (append H₀ H₁), G, wholeIdeal M.N M.ideal M.d (append H₀ H₁), M.d⟩ : MarkedIdeal p Z) =
    ⟨carrier (carrier M.N H₀) H₁, G, wholeIdeal (carrier M.N H₀) (wholeIdeal M.N M.ideal M.d H₀) M.d H₁, M.d⟩
  rw [carrier_append, wholeIdeal_append]

/-- **Tests along a concatenation.** -/
theorem isTest_append (M : MarkedIdeal n X) {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)} (H₀ : LHist X M.E Y F) :
    ∀ {p : ℕ} {Z : CMfd.{u} p} {G : List (Set Z)} (H₁ : LHist Y F Z G),
      IsTest M (append H₀ H₁) ↔ IsTest M H₀ ∧ IsTest (record M H₀) H₁
  | _, _, _, .refl => ⟨fun h => ⟨h, trivial⟩, And.left⟩
  | _, _, _, .controlled H C π hπ => by
    show IsTest M (append H₀ H) ∧ (record M (append H₀ H)).IsAdmissibleCentre C ↔
      IsTest M H₀ ∧ (IsTest (record M H₀) H ∧ (record (record M H₀) H).IsAdmissibleCentre C)
    rw [isTest_append M H₀ H, record_append, and_assoc]
  | _, _, _, .projection H => isTest_append M H₀ H
  | _, _, _, .exceptional H _ _ _ _ _ => isTest_append M H₀ H
  | _, _, _, .restrict H _ => isTest_append M H₀ H

theorem inKinds_append (κ : Kinds) {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)} (H₀ : LHist X E Y F) :
    ∀ {p : ℕ} {Z : CMfd.{u} p} {G : List (Set Z)} (H₁ : LHist Y F Z G),
      InKinds κ (append H₀ H₁) ↔ InKinds κ H₀ ∧ InKinds κ H₁
  | _, _, _, .refl => ⟨fun h => ⟨h, trivial⟩, And.left⟩
  | _, _, _, .controlled H _ _ _ => inKinds_append κ H₀ H
  | _, _, _, .projection H => by
    show κ.proj = true ∧ InKinds κ (append H₀ H) ↔ InKinds κ H₀ ∧ (κ.proj = true ∧ InKinds κ H)
    rw [inKinds_append κ H₀ H]
    tauto
  | _, _, _, .exceptional H _ _ _ _ _ => by
    show κ.exc = true ∧ InKinds κ (append H₀ H) ↔ InKinds κ H₀ ∧ (κ.exc = true ∧ InKinds κ H)
    rw [inKinds_append κ H₀ H]
    tauto
  | _, _, _, .restrict H _ => inKinds_append κ H₀ H

/-! ### Towers -/

/-- **A blowup tower after a local history.** -/
def towerL {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)} (H : LHist X E Y F) :
    {Z : CMfd.{u} m} → (T : BlowupTower Y Z) → LHist X E Z (towerBoundary F T)
  | _, .refl => H
  | _, .step T C π hπ => .controlled (towerL H T) C π hπ

theorem record_towerL (M : MarkedIdeal n X) {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)}
    (H : LHist X M.E Y F) {Z : CMfd.{u} m} (T : BlowupTower Y Z) :
    record M (towerL H T) = geoTransformAlong (record M H) T := by
  induction T with
  | refl => rfl
  | step T C π hπ ih =>
    show (record M (towerL H T)).geoTransform C π = (geoTransformAlong (record M H) T).geoTransform C π
    rw [ih]

theorem isTest_towerL_iff (M : MarkedIdeal n X) {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)}
    (H : LHist X M.E Y F) {Z : CMfd.{u} m} (T : BlowupTower Y Z) :
    IsTest M (towerL H T) ↔ IsTest M H ∧ IsGeoTestTower (record M H) T := by
  induction T with
  | refl => exact ⟨fun h => ⟨h, trivial⟩, And.left⟩
  | step T C π hπ ih =>
    show IsTest M (towerL H T) ∧ (record M (towerL H T)).IsAdmissibleCentre C ↔
      IsTest M H ∧ (IsGeoTestTower (record M H) T ∧ (geoTransformAlong (record M H) T).IsAdmissibleCentre C)
    rw [ih, record_towerL, and_assoc]

theorem inKinds_towerL (κ : Kinds) {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)} (H : LHist X E Y F)
    (hH : InKinds κ H) : ∀ {Z : CMfd.{u} m} (T : BlowupTower Y Z), InKinds κ (towerL H T)
  | _, .refl => hH
  | _, .step T _ _ _ => inKinds_towerL κ H hH T

/-! ### Global histories as local histories -/

/-- **A global mixed history is a local one** (no restriction). -/
def ofHist : {m : ℕ} → {Y : CMfd.{u} m} → {F : List (Set Y)} → History X E Y F → LHist X E Y F
  | _, _, _, .refl => .refl
  | _, _, _, .controlled H C π hπ => .controlled (ofHist H) C π hπ
  | _, _, _, .projection H => .projection (ofHist H)
  | _, _, _, .exceptional H i j hij π hπ => .exceptional (ofHist H) i j hij π hπ

theorem carrier_ofHist (N : Set X) :
    ∀ {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)} (H : History X E Y F),
      carrier N (ofHist H) = HironakaActualMixedTestPowerNormalization.carrier N H
  | _, _, _, .refl => rfl
  | _, _, _, .controlled H C π hπ => by
    simp only [ofHist, carrier, HironakaActualMixedTestPowerNormalization.carrier, carrier_ofHist N H]
  | _, _, _, .projection H => by
    simp only [ofHist, carrier, HironakaActualMixedTestPowerNormalization.carrier, carrier_ofHist N H]
  | _, _, _, .exceptional H i j hij π hπ => by
    simp only [ofHist, carrier, HironakaActualMixedTestPowerNormalization.carrier, carrier_ofHist N H]
    rfl

theorem wholeIdeal_ofHist (N : Set X) (I : GermIdeal n X) (d : ℕ) :
    ∀ {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)} (H : History X E Y F),
      wholeIdeal N I d (ofHist H) = HironakaActualMixedTestPowerNormalization.wholeIdeal N I d H
  | _, _, _, .refl => rfl
  | _, _, _, .controlled H C π hπ => by
    simp only [ofHist, wholeIdeal, HironakaActualMixedTestPowerNormalization.wholeIdeal, carrier_ofHist N H,
      wholeIdeal_ofHist N I d H]
  | _, _, _, .projection H => by
    simp only [ofHist, wholeIdeal, HironakaActualMixedTestPowerNormalization.wholeIdeal, wholeIdeal_ofHist N I d H]
  | _, _, _, .exceptional H i j hij π hπ => by
    simp only [ofHist, wholeIdeal, HironakaActualMixedTestPowerNormalization.wholeIdeal, wholeIdeal_ofHist N I d H]

theorem record_ofHist (M : MarkedIdeal n X) {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)} (H : History X M.E Y F) :
    record M (ofHist H) = HironakaActualMixedTestPowerNormalization.record M H := by
  show (⟨carrier M.N (ofHist H), F, wholeIdeal M.N M.ideal M.d (ofHist H), M.d⟩ : MarkedIdeal m Y) =
    ⟨HironakaActualMixedTestPowerNormalization.carrier M.N H, F,
      HironakaActualMixedTestPowerNormalization.wholeIdeal M.N M.ideal M.d H, M.d⟩
  rw [carrier_ofHist, wholeIdeal_ofHist]

theorem isTest_ofHist (M : MarkedIdeal n X) :
    ∀ {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)} (H : History X M.E Y F),
      IsTest M (ofHist H) ↔ HironakaActualMixedTestPowerNormalization.IsTest M H
  | _, _, _, .refl => Iff.rfl
  | _, _, _, .controlled H C π hπ => by
    show IsTest M (ofHist H) ∧ (record M (ofHist H)).IsAdmissibleCentre C ↔
      HironakaActualMixedTestPowerNormalization.IsTest M H ∧
        (HironakaActualMixedTestPowerNormalization.record M H).IsAdmissibleCentre C
    rw [isTest_ofHist M H, record_ofHist]
  | _, _, _, .projection H => isTest_ofHist M H
  | _, _, _, .exceptional H _ _ _ _ _ => isTest_ofHist M H

theorem inKinds_ofHist_of_noExc :
    ∀ {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)} (H : History X E Y F), NoExc H → InKinds Kinds.wp (ofHist H)
  | _, _, _, .refl, _ => trivial
  | _, _, _, .controlled H _ _ _, h => inKinds_ofHist_of_noExc H h
  | _, _, _, .projection H, h => ⟨rfl, inKinds_ofHist_of_noExc H h⟩
  | _, _, _, .exceptional _ _ _ _ _ _, h => h.elim

end LHist

/-! ### The local equivalences -/

section Equiv

open LHist

variable {n : ℕ} {X : CMfd.{u} n} {M M' M'' : MarkedIdeal n X} {κ : Kinds}

/-- **Local equivalence for the kinds `κ`**: the same boundary, the same local test histories of kinds `κ` (admissible
blowups and restrictions to open subsets of every stage, plus the actions `κ` allows), and the same cosupports along
them. -/
def LocEquiv (κ : Kinds) (M M' : MarkedIdeal n X) : Prop :=
  M'.E = M.E ∧ ∀ {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)} (H : LHist X M.E Y F), InKinds κ H →
    (IsTest M H ↔ IsTest (withBoundary M' M.E) H) ∧
      (IsTest M H → (record M H).cosupp = (record (withBoundary M' M.E) H).cosupp)

/-- **The local form of BM's `s(i,ii)`** (the relation `WPEquiv` of the (B') plan, localized): admissible blowups,
products with a line and restrictions to open subsets. -/
abbrev LocWPEquiv (M M' : MarkedIdeal n X) : Prop := LocEquiv Kinds.wp M M'

/-- **The local form of BM's equivalence** (BM08 Defn 2.5, with local blowings-up). -/
abbrev LocMixedEquiv (M M' : MarkedIdeal n X) : Prop := LocEquiv Kinds.bm M M'

/-- **The local form of Włodarczyk's equivalence.** -/
abbrev LocWEquiv (M M' : MarkedIdeal n X) : Prop := LocEquiv Kinds.w M M'

theorem LocEquiv.E_eq (h : LocEquiv κ M M') : M'.E = M.E := h.1

theorem LocEquiv.refl (κ : Kinds) (M : MarkedIdeal n X) : LocEquiv κ M M := by
  obtain ⟨N, E, I, d⟩ := M
  exact ⟨rfl, fun _ _ => ⟨Iff.rfl, fun _ => rfl⟩⟩

theorem LocEquiv.symm (h : LocEquiv κ M M') : LocEquiv κ M' M := by
  obtain ⟨N, E, I, d⟩ := M
  obtain ⟨N', E', I', d'⟩ := M'
  obtain ⟨hE, h⟩ := h
  change E' = E at hE
  subst hE
  exact ⟨rfl, fun H hk => ⟨(h H hk).1.symm, fun hH => ((h H hk).2 ((h H hk).1.mpr hH)).symm⟩⟩

theorem LocEquiv.trans (h : LocEquiv κ M M') (h' : LocEquiv κ M' M'') : LocEquiv κ M M'' := by
  obtain ⟨N, E, I, d⟩ := M
  obtain ⟨N', E', I', d'⟩ := M'
  obtain ⟨N'', E'', I'', d''⟩ := M''
  obtain ⟨hE, h⟩ := h
  obtain ⟨hE', h'⟩ := h'
  change E' = E at hE
  change E'' = E' at hE'
  subst hE hE'
  exact ⟨rfl, fun H hk => ⟨(h H hk).1.trans (h' H hk).1,
    fun hH => ((h H hk).2 hH).trans ((h' H hk).2 ((h H hk).1.mp hH))⟩⟩

/-- **Fewer kinds**: a local equivalence for more test transformations is one for fewer. -/
theorem LocEquiv.mono {κ' : Kinds} (hκ : κ.Le κ') (h : LocEquiv κ' M M') : LocEquiv κ M M' :=
  ⟨h.1, fun H hk => h.2 H (InKinds.mono hκ H hk)⟩

/-- The local BM equivalence implies the local `s(i,ii)`-equivalence, which implies the local Włodarczyk equivalence. -/
theorem LocEquiv.locWPEquiv (h : LocMixedEquiv M M') : LocWPEquiv M M' := h.mono Kinds.wp_le_bm

theorem LocEquiv.locWEquiv (h : LocEquiv κ M M') : LocWEquiv M M' := h.mono (Kinds.w_le κ)

theorem LocEquiv.isTest_iff (h : LocEquiv κ M M') {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)}
    (H : LHist X M.E Y F) (hk : InKinds κ H) : IsTest M H ↔ IsTest (withBoundary M' M.E) H := (h.2 H hk).1

theorem LocEquiv.cosupp_eq (h : LocEquiv κ M M') {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)}
    (H : LHist X M.E Y F) (hk : InKinds κ H) (hH : IsTest M H) :
    (record M H).cosupp = (record (withBoundary M' M.E) H).cosupp := (h.2 H hk).2 hH

theorem LocEquiv.cosupp_eq_base (h : LocEquiv κ M M') : M.cosupp = M'.cosupp := by
  have h1 := h.cosupp_eq (.refl : LHist X M.E X M.E) trivial trivial
  rw [record_refl] at h1
  rw [h1]
  exact congrArg MarkedIdeal.cosupp (withBoundary_eq h.1)

/-- **Stability along common local test histories**: the records at every node are again locally equivalent. -/
theorem LocEquiv.record (h : LocEquiv κ M M') {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)}
    (H₀ : LHist X M.E Y F) (hk₀ : InKinds κ H₀) (hH₀ : IsTest M H₀) :
    LocEquiv κ (LHist.record M H₀) (LHist.record (withBoundary M' M.E) H₀) := by
  obtain ⟨N, E, I, d⟩ := M
  obtain ⟨N', E', I', d'⟩ := M'
  obtain ⟨hE, h⟩ := h
  change E' = E at hE
  subst hE
  have hH₀' : IsTest (⟨N', E', I', d'⟩ : MarkedIdeal n X) H₀ := (h H₀ hk₀).1.mp hH₀
  refine ⟨rfl, fun H₁ hk₁ => ?_⟩
  have hk : InKinds κ (append H₀ H₁) := (inKinds_append κ H₀ H₁).mpr ⟨hk₀, hk₁⟩
  have hA := isTest_append (⟨N, E', I, d⟩ : MarkedIdeal n X) H₀ H₁
  have hB := isTest_append (⟨N', E', I', d'⟩ : MarkedIdeal n X) H₀ H₁
  have hiff : IsTest (LHist.record (⟨N, E', I, d⟩ : MarkedIdeal n X) H₀) H₁ ↔
      IsTest (LHist.record (⟨N', E', I', d'⟩ : MarkedIdeal n X) H₀) H₁ := by
    constructor
    · intro h1
      exact (hB.mp ((h (append H₀ H₁) hk).1.mp (hA.mpr ⟨hH₀, h1⟩))).2
    · intro h1
      exact (hA.mp ((h (append H₀ H₁) hk).1.mpr (hB.mpr ⟨hH₀', h1⟩))).2
  refine ⟨hiff, fun h1 => ?_⟩
  have hc := (h (append H₀ H₁) hk).2 (hA.mpr ⟨hH₀, h1⟩)
  have e1 := record_append (⟨N, E', I, d⟩ : MarkedIdeal n X) H₀ H₁
  have e2 := record_append (⟨N', E', I', d'⟩ : MarkedIdeal n X) H₀ H₁
  show (LHist.record (LHist.record (⟨N, E', I, d⟩ : MarkedIdeal n X) H₀) H₁).cosupp =
    (LHist.record (LHist.record (⟨N', E', I', d'⟩ : MarkedIdeal n X) H₀) H₁).cosupp
  exact (congrArg MarkedIdeal.cosupp e1).symm.trans (hc.trans (congrArg MarkedIdeal.cosupp e2))

/-- **Restriction to an open subset**: locally equivalent marked ideals have locally equivalent restrictions. -/
theorem LocEquiv.restrict (h : LocEquiv κ M M') (U : Opens X) :
    LocEquiv (X := CMfd.of (n := n) U) κ (MarkedIdeal.pullback (Subtype.val : U → X) M)
      (MarkedIdeal.pullback (Subtype.val : U → X) M') := by
  obtain ⟨N, E, I, d⟩ := M
  obtain ⟨N', E', I', d'⟩ := M'
  have hE : E' = E := h.1
  subst hE
  exact h.record (.restrict .refl U) trivial trivial

/-- **Stability along a common test tower.** -/
theorem LocEquiv.geoTransformAlong (h : LocEquiv κ M M') {Z : CMfd.{u} n} (T : BlowupTower X Z)
    (hT : IsGeoTestTower M T) : LocEquiv κ (geoTransformAlong M T) (geoTransformAlong M' T) := by
  obtain ⟨N, E, I, d⟩ := M
  obtain ⟨N', E', I', d'⟩ := M'
  have hE : E' = E := h.1
  subst hE
  have hk : InKinds κ (towerL (.refl : LHist X E' X E') T) := inKinds_towerL κ .refl (inKinds_refl κ) T
  have hH : IsTest (⟨N, E', I, d⟩ : MarkedIdeal n X) (towerL (.refl : LHist X E' X E') T) :=
    (isTest_towerL_iff _ .refl T).mpr ⟨trivial, hT⟩
  have h1 := h.record _ hk hH
  have e1 := record_towerL (⟨N, E', I, d⟩ : MarkedIdeal n X) .refl T
  have e2 := record_towerL (⟨N', E', I', d'⟩ : MarkedIdeal n X) .refl T
  change LocEquiv κ (LHist.record (⟨N, E', I, d⟩ : MarkedIdeal n X) (towerL .refl T))
    (LHist.record (⟨N', E', I', d'⟩ : MarkedIdeal n X) (towerL .refl T)) at h1
  rw [e1, e2] at h1
  exact h1

/-- **Comparison with the global relations**: a local equivalence (any kinds) is Włodarczyk's equivalence. -/
theorem LocEquiv.wEquiv (h : LocEquiv κ M M') : WEquiv M M' := by
  obtain ⟨N, E, I, d⟩ := M
  obtain ⟨N', E', I', d'⟩ := M'
  obtain ⟨hE, h⟩ := h
  change E' = E at hE
  subst hE
  refine ⟨rfl, fun T => ?_⟩
  have hk : InKinds κ (towerL (.refl : LHist X E' X E') T) := inKinds_towerL κ .refl (inKinds_refl κ) T
  have hA := isTest_towerL_iff (⟨N, E', I, d⟩ : MarkedIdeal n X) .refl T
  have hB := isTest_towerL_iff (⟨N', E', I', d'⟩ : MarkedIdeal n X) .refl T
  have rA := record_towerL (⟨N, E', I, d⟩ : MarkedIdeal n X) .refl T
  have rB := record_towerL (⟨N', E', I', d'⟩ : MarkedIdeal n X) .refl T
  obtain ⟨h1, h2⟩ := h (towerL (.refl : LHist X E' X E') T) hk
  have hA' : IsTest (⟨N, E', I, d⟩ : MarkedIdeal n X) (towerL .refl T) ↔
      IsGeoTestTower (⟨N, E', I, d⟩ : MarkedIdeal n X) T := hA.trans ⟨And.right, fun h => ⟨trivial, h⟩⟩
  have hB' : IsTest (⟨N', E', I', d'⟩ : MarkedIdeal n X) (towerL .refl T) ↔
      IsGeoTestTower (⟨N', E', I', d'⟩ : MarkedIdeal n X) T := hB.trans ⟨And.right, fun h => ⟨trivial, h⟩⟩
  refine ⟨hA'.symm.trans (h1.trans hB'), fun hT => ?_⟩
  exact (congrArg MarkedIdeal.cosupp rA).symm.trans ((h2 (hA'.mpr hT)).trans (congrArg MarkedIdeal.cosupp rB))

/-- **Comparison with the global relations**: the local `s(i,ii)`-equivalence implies `ProjEquiv`. -/
theorem LocEquiv.projEquiv (h : LocEquiv Kinds.wp M M') : ProjEquiv M M' := by
  obtain ⟨N, E, I, d⟩ := M
  obtain ⟨N', E', I', d'⟩ := M'
  obtain ⟨hE, h⟩ := h
  change E' = E at hE
  subst hE
  refine ⟨rfl, fun H hn => ?_⟩
  obtain ⟨h1, h2⟩ := h (ofHist H) (inKinds_ofHist_of_noExc H hn)
  have hA := isTest_ofHist (⟨N, E', I, d⟩ : MarkedIdeal n X) H
  have hB := isTest_ofHist (⟨N', E', I', d'⟩ : MarkedIdeal n X) H
  have rA := record_ofHist (⟨N, E', I, d⟩ : MarkedIdeal n X) H
  have rB := record_ofHist (⟨N', E', I', d'⟩ : MarkedIdeal n X) H
  refine ⟨hA.symm.trans (h1.trans hB), fun hT => ?_⟩
  exact (congrArg MarkedIdeal.cosupp rA).symm.trans ((h2 (hA.mpr hT)).trans (congrArg MarkedIdeal.cosupp rB))

/-- **Comparison with the global relations**: the local BM equivalence implies `MixedEquiv`. -/
theorem LocEquiv.mixedEquiv (h : LocEquiv Kinds.bm M M') : MixedEquiv M M' := by
  obtain ⟨N, E, I, d⟩ := M
  obtain ⟨N', E', I', d'⟩ := M'
  obtain ⟨hE, h⟩ := h
  change E' = E at hE
  subst hE
  refine ⟨rfl, fun H => ?_⟩
  obtain ⟨h1, h2⟩ := h (ofHist H) (inKinds_bm _)
  have hA := isTest_ofHist (⟨N, E', I, d⟩ : MarkedIdeal n X) H
  have hB := isTest_ofHist (⟨N', E', I', d'⟩ : MarkedIdeal n X) H
  have rA := record_ofHist (⟨N, E', I, d⟩ : MarkedIdeal n X) H
  have rB := record_ofHist (⟨N', E', I', d'⟩ : MarkedIdeal n X) H
  refine ⟨hA.symm.trans (h1.trans hB), fun hT => ?_⟩
  exact (congrArg MarkedIdeal.cosupp rA).symm.trans ((h2 (hA.mpr hT)).trans (congrArg MarkedIdeal.cosupp rB))

/-- **At every node** of a common local test history of kinds `wp`, the records are `ProjEquiv` (so every G8 result for
`ProjEquiv`, e.g. the entries E1–E3, applies there). -/
theorem LocEquiv.record_projEquiv (h : LocEquiv Kinds.wp M M') {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)}
    (H₀ : LHist X M.E Y F) (hk₀ : InKinds Kinds.wp H₀) (hH₀ : IsTest M H₀) :
    ProjEquiv (LHist.record M H₀) (LHist.record (withBoundary M' M.E) H₀) :=
  (h.record H₀ hk₀ hH₀).projEquiv

/-- **At every restriction**: `LocWPEquiv` gives `ProjEquiv` of the restrictions to every open subset. -/
theorem LocEquiv.restrict_projEquiv (h : LocEquiv Kinds.wp M M') (U : Opens X) :
    ProjEquiv (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) M)
      (MarkedIdeal.pullback (Subtype.val : U → X) M') :=
  (h.restrict U).projEquiv

end Equiv

end

end Hironaka.HironakaG8LocalHistory
