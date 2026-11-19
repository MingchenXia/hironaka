import Hironaka.Resolution.HironakaG8LocalHistory

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Local equivalence from a relation stable under the test actions (G8 lane, run 0080, round 3; (B') ports, locality)

Blueprint: `hironaka-g8-resume-local-stable.tex`.

The local equivalences of `HironakaG8LocalHistory` quantify over local histories (admissible blowups, products with a
line, restrictions to open subsets of every stage).  A global equivalence theorem does not formally restrict to open
subsets, so every port of the (B') plan needs its local form.  This module reduces such local forms to ONE-STEP facts:

* `IsLocStable κ R`: a family `R` of relations between marked ideals on the same manifold (all dimensions) that forces
  the same boundary and the same cosupport, and is stable under one admissible blowup (centre admissible for the first
  ideal), under one product with a line (if `κ` allows it) and under restriction to an open subset;
* **`LocEquiv.of_isLocStable`**: if `κ` has no exceptional blowups, `R M M'` implies `LocEquiv κ M M'` — the
  coinduction principle of the local equivalence (the relation is carried along every local history by induction);
* `isLocStable_locEquiv`: the local equivalence itself is such a family (so the principle characterizes it);
* `IsLocStable.mono`, `IsLocStable.sup`: fewer kinds; the union of two stable families.

Typical use: a construction `Φ` with ideal-level "sandwich" inclusions `P^e ⊆ Φ(P) ⊆ Φ'(P)` on the carrier that are
preserved by one blowup (Giraud), one product and one restriction gives `LocWPEquiv P (Φ P)`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8LocalStable

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals
  MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
open Hironaka.HironakaActualProjectionTestRecord (projectionTest projectionAmbient)
open Hironaka.HironakaG8MixedEquiv (withBoundary isAdmissibleCentre_congr)
open Hironaka.HironakaActualExceptionalTestRecord (exceptionalTest)
open Hironaka.HironakaG8LocalHistory
open Hironaka.HironakaG8LocalHistory.LHist

noncomputable section

variable {n : ℕ}

/-- **A family of relations stable under the local test actions of kinds `κ`** (no condition for exceptional blowups;
the principle below is for kinds without them). -/
structure IsLocStable (κ : Kinds)
    (R : ∀ {m : ℕ} {Y : CMfd.{u} m}, MarkedIdeal m Y → MarkedIdeal m Y → Prop) : Prop where
  /-- the same boundary -/
  E_eq : ∀ {m : ℕ} {Y : CMfd.{u} m} {P Q : MarkedIdeal m Y}, R P Q → Q.E = P.E
  /-- the same cosupport -/
  cosupp_eq : ∀ {m : ℕ} {Y : CMfd.{u} m} {P Q : MarkedIdeal m Y}, R P Q → P.cosupp = Q.cosupp
  /-- stable under one admissible blowup -/
  controlled : ∀ {m : ℕ} {Y : CMfd.{u} m} {P Q : MarkedIdeal m Y}, R P Q → ∀ (C : Set Y) {Z : CMfd.{u} m}
    (π : Z → Y), IsBlowupAlong m C π → P.IsAdmissibleCentre C → R (P.geoTransform C π) (Q.geoTransform C π)
  /-- stable under one product with a line, if allowed -/
  projection : κ.proj = true → ∀ {m : ℕ} {Y : CMfd.{u} m} {P Q : MarkedIdeal m Y}, R P Q →
    R (projectionTest P) (projectionTest Q)
  /-- stable under restriction to an open subset -/
  restrict : ∀ {m : ℕ} {Y : CMfd.{u} m} {P Q : MarkedIdeal m Y}, R P Q → ∀ U : Opens Y,
    R (Y := CMfd.of (n := m) U) (MarkedIdeal.pullback (Subtype.val : U → Y) P)
      (MarkedIdeal.pullback (Subtype.val : U → Y) Q)

variable {κ : Kinds} {R : ∀ {m : ℕ} {Y : CMfd.{u} m}, MarkedIdeal m Y → MarkedIdeal m Y → Prop}

/-- Stability includes the actual exceptional pair test. -/
structure IsLocStableExceptional (κ : Kinds)
    (R : ∀ {m : ℕ} {Y : CMfd.{u} m}, MarkedIdeal m Y → MarkedIdeal m Y → Prop) : Prop where
  base : IsLocStable κ R
  exceptional : κ.exc = true → ∀ {m : ℕ} {Y : CMfd.{u} m}
    {N N' : Set Y} {E : List (Set Y)} {I I' : GermIdeal m Y} {d d' : ℕ},
    R (⟨N,E,I,d⟩ : MarkedIdeal m Y) ⟨N',E,I',d'⟩ →
    ∀ (i j : Fin E.length), i ≠ j → ∀ {Z : CMfd.{u} m} (π : Z → Y),
      IsBlowupAlong m (E.get i ∩ E.get j) π →
      R (exceptionalTest (⟨N,E,I,d⟩ : MarkedIdeal m Y) i j π)
        (exceptionalTest (⟨N',E,I',d'⟩ : MarkedIdeal m Y) i j π)

/-- The relation and equivalence of test conditions persist along a permitted history. -/
private theorem carry_mixed (hR : IsLocStableExceptional κ R) {X : CMfd.{u} n} {N N' : Set X} {E : List (Set X)}
    {I I' : GermIdeal n X} {d d' : ℕ} (h : R (⟨N, E, I, d⟩ : MarkedIdeal n X) ⟨N', E, I', d'⟩) :
    ∀ {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)} (L : LHist X E Y F), InKinds κ L →
      (IsTest (⟨N, E, I, d⟩ : MarkedIdeal n X) L ↔ IsTest (⟨N', E, I', d'⟩ : MarkedIdeal n X) L) ∧
        (IsTest (⟨N, E, I, d⟩ : MarkedIdeal n X) L →
          R (record (⟨N, E, I, d⟩ : MarkedIdeal n X) L) (record (⟨N', E, I', d'⟩ : MarkedIdeal n X) L))
  | _, _, _, .refl, _ => ⟨Iff.rfl, fun _ => h⟩
  | _, _, _, .controlled L C π hπ, hk => by
    obtain ⟨hiff, hrel⟩ := carry_mixed hR h L hk
    refine ⟨?_, fun hT => ?_⟩
    · show IsTest (⟨N, E, I, d⟩ : MarkedIdeal n X) L ∧
          (record (⟨N, E, I, d⟩ : MarkedIdeal n X) L).IsAdmissibleCentre C ↔
        IsTest (⟨N', E, I', d'⟩ : MarkedIdeal n X) L ∧
          (record (⟨N', E, I', d'⟩ : MarkedIdeal n X) L).IsAdmissibleCentre C
      constructor
      · rintro ⟨h1, h2⟩
        have hr := hrel h1
        exact ⟨hiff.mp h1, (isAdmissibleCentre_congr (hR.base.E_eq hr).symm (hR.base.cosupp_eq hr) C).mp h2⟩
      · rintro ⟨h1, h2⟩
        have h1' := hiff.mpr h1
        have hr := hrel h1'
        exact ⟨h1', (isAdmissibleCentre_congr (hR.base.E_eq hr).symm (hR.base.cosupp_eq hr) C).mpr h2⟩
    · exact hR.base.controlled (hrel hT.1) C π hπ hT.2
  | _, _, _, .projection L, hk => by
    obtain ⟨hiff, hrel⟩ := carry_mixed hR h L hk.2
    exact ⟨hiff, fun hT => hR.base.projection hk.1 (hrel hT)⟩
  | _, _, _, .exceptional L i j hij π hπ, hk => by
    obtain ⟨hiff, hrel⟩ := carry_mixed hR h L hk.2
    exact ⟨hiff, fun hT => hR.exceptional hk.1 (hrel hT) i j hij π hπ⟩
  | _, _, _, .restrict L U, hk => by
    obtain ⟨hiff, hrel⟩ := carry_mixed hR h L hk
    exact ⟨hiff, fun hT => hR.base.restrict (hrel hT) U⟩

/-- Stability under every allowed local action, including exceptional tests, implies local equivalence. -/
theorem LocEquiv.of_isLocStableExceptional (hR : IsLocStableExceptional κ R) {X : CMfd.{u} n}
    {M M' : MarkedIdeal n X} (h : R M M') : LocEquiv κ M M' := by
  obtain ⟨N, E, I, d⟩ := M
  obtain ⟨N', E', I', d'⟩ := M'
  have hE : E' = E := hR.base.E_eq h
  subst hE
  refine ⟨rfl, fun L hk => ?_⟩
  obtain ⟨hiff, hrel⟩ := carry_mixed hR h L hk
  exact ⟨hiff, fun hT => hR.base.cosupp_eq (hrel hT)⟩

/-- The original no-exception coinduction API, recovered from the general action-stability theorem. -/
theorem LocEquiv.of_isLocStable (hR : IsLocStable κ R) (hexc : κ.exc = false) {X : CMfd.{u} n}
    {M M' : MarkedIdeal n X} (h : R M M') : LocEquiv κ M M' := by
  apply LocEquiv.of_isLocStableExceptional ?_ h
  refine ⟨hR, ?_⟩
  intro htrue
  rw [hexc] at htrue
  contradiction

/-- **The local equivalence is stable** (so the principle characterizes it). -/
theorem isLocStable_locEquiv (κ : Kinds) :
    IsLocStable.{u} κ (fun {m} {Y} P Q => LocEquiv (n := m) (X := Y) κ P Q) where
  E_eq h := h.E_eq
  cosupp_eq h := h.cosupp_eq_base
  controlled := by
    intro m Y P Q h C Z π hπ hC
    obtain ⟨N, E, I, d⟩ := P
    obtain ⟨N', E', I', d'⟩ := Q
    have hE : E' = E := h.E_eq
    subst hE
    exact h.record (.controlled .refl C π hπ) (inKinds_refl κ) ⟨trivial, hC⟩
  projection := by
    intro hp m Y P Q h
    obtain ⟨N, E, I, d⟩ := P
    obtain ⟨N', E', I', d'⟩ := Q
    have hE : E' = E := h.E_eq
    subst hE
    exact h.record (.projection .refl) ⟨hp, trivial⟩ trivial
  restrict h U := h.restrict U

/-- **Fewer kinds.** -/
theorem IsLocStable.mono {κ' : Kinds} (hκ : κ.Le κ') (hR : IsLocStable κ' R) : IsLocStable κ R where
  E_eq := hR.E_eq
  cosupp_eq := hR.cosupp_eq
  controlled := hR.controlled
  projection hp := hR.projection (hκ.1 hp)
  restrict := hR.restrict

/-- **The union of two stable families is stable.** -/
theorem IsLocStable.sup {R' : ∀ {m : ℕ} {Y : CMfd.{u} m}, MarkedIdeal m Y → MarkedIdeal m Y → Prop}
    (hR : IsLocStable κ R) (hR' : IsLocStable κ R') :
    IsLocStable κ (fun {m} {Y} P Q => R (m := m) (Y := Y) P Q ∨ R' (m := m) (Y := Y) P Q) where
  E_eq h := h.elim hR.E_eq hR'.E_eq
  cosupp_eq h := h.elim hR.cosupp_eq hR'.cosupp_eq
  controlled h C _ π hπ hC := h.elim (fun h => Or.inl (hR.controlled h C π hπ hC))
    (fun h => Or.inr (hR'.controlled h C π hπ hC))
  projection hp _ _ _ _ h := h.elim (fun h => Or.inl (hR.projection hp h)) (fun h => Or.inr (hR'.projection hp h))
  restrict h U := h.elim (fun h => Or.inl (hR.restrict h U)) (fun h => Or.inr (hR'.restrict h U))

end

end Hironaka.HironakaG8LocalStable
