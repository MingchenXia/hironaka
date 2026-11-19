import Hironaka.Resolution.HironakaG8ClassStepCut

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Reordering the boundary keeps a local equivalence (G8C lane, run 0080, round 4; (B') plan module 10, Case T)

Blueprint: `hironaka-g8-class-step-perm.tex`.  Plan: lane G11B's `FALLBACK-DECISION-ANALYSIS.md` §2, Case T ("Step I.B with one
member cut ... after moving `H₁` to the front — needs a boundary-permutation lemma for `LocEquiv`").

The local equivalences `LocEquiv κ` compare marked ideals with the SAME boundary list.  Admissibility only sees the SET of members
(normal crossings with every member), so replacing the boundary by any list with the same members (a permutation, a repetition
or a deletion of repeated members) keeps a local equivalence, for kinds without exceptional blowups:

* `hasNormalCrossings_of_forall_mem`: normal crossings with `L` give normal crossings with every `L'` whose members are members
  of `L` (re-index the adapted coordinates);
* `ReorderRel`, `isLocStable_reorderRel`, **`locEquiv_reorder`**: `LocEquiv κ P Q → (L, P.E have the same members) →
  LocEquiv κ {P with E := L} {Q with E := L}`; **`locEquiv_perm`** (`L ~ P.E`).

Sorry-free.  Import discipline: no import of `Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8ClassStepPerm

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.BlowupStrictSubmanifold
  Hironaka.HironakaG8LocalHistory Hironaka.HironakaG8LocalStable
  Hironaka.MarkedIdealBiholomorphism Hironaka.NormalCrossings
open Hironaka.HironakaActualProjectionTestRecord (projectionTest projectionAmbient horizontal)
open scoped ProductComplexManifold

noncomputable section

/-! ### Normal crossings only see the members -/

section NC

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- **Normal crossings with `L` give normal crossings with any `L'` whose members are members of `L`.** -/
theorem hasNormalCrossings_of_forall_mem {C : Set M} {L L' : List (Set M)} (h : HasNormalCrossings n C L)
    (hsub : ∀ H ∈ L', H ∈ L) : HasNormalCrossings n C L' := by
  intro x hx
  obtain ⟨S₀, S, hfam, hcard⟩ := h x hx
  have hex : ∀ i : Fin L'.length, ∃ j : Fin L.length, L.get j = L'.get i := fun i =>
    List.mem_iff_get.mp (hsub _ (List.get_mem L' i))
  choose e he using hex
  have hA : ∀ o : Option (Fin L'.length), (o.elim C fun i => L'.get i) =
      (Option.map e o).elim C fun i => L.get i := by
    intro o
    cases o with
    | none => rfl
    | some i => exact (he i).symm
  have hS : ∀ o : Option (Fin L'.length), (o.elim S₀ fun i => S (e i)) = (Option.map e o).elim S₀ S := by
    intro o
    cases o <;> rfl
  refine ⟨S₀, fun i => S (e i),
    NormalCrossingsInvariance.IsCoordinateFamilyAt.reindex hfam (Option.map e) hA hS, fun i hi => hcard (e i) ?_⟩
  rw [he]
  exact hi

end NC

/-! ### The reordering relation -/

section Reorder

/-- **The relation of the coinduction for a reordered boundary**: a locally equivalent pair whose common boundary is replaced by
a list with the same members. -/
def ReorderRel (κ : Kinds) {m : ℕ} {Y : CMfd.{u} m} (P' Q' : MarkedIdeal m Y) : Prop :=
  ∃ (P Q : MarkedIdeal m Y) (L : List (Set Y)), LocEquiv κ P Q ∧ (∀ H ∈ L, H ∈ P.E) ∧ (∀ H ∈ P.E, H ∈ L) ∧
    P' = { P with E := L } ∧ Q' = { Q with E := L }

/-- **Reordering the boundary is stable under the local test actions.** -/
theorem isLocStable_reorderRel (κ : Kinds) :
    IsLocStable.{u} κ (fun {m} {Y} P Q => ReorderRel κ (m := m) (Y := Y) P Q) where
  E_eq := by
    rintro m Y P' Q' ⟨P, Q, L, -, -, -, rfl, rfl⟩
    rfl
  cosupp_eq := by
    rintro m Y P' Q' ⟨P, Q, L, h, -, -, rfl, rfl⟩
    exact h.cosupp_eq_base
  controlled := by
    rintro m Y P' Q' ⟨P, Q, L, h, h1, h2, rfl, rfl⟩ C Z π hπ hC
    have hCP : P.IsAdmissibleCentre C := ⟨hC.1, hC.2.1, hasNormalCrossings_of_forall_mem hC.2.2 h2⟩
    refine ⟨P.geoTransform C π, Q.geoTransform C π, L.map (geoStrictTransform π C) ++ [π ⁻¹' C],
      (isLocStable_locEquiv κ).controlled h C π hπ hCP, ?_, ?_, rfl, rfl⟩
    · intro H hH
      rcases List.mem_append.mp hH with hH | hH
      · obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
        exact List.mem_append_left _ (List.mem_map_of_mem (h1 H₀ hH₀))
      · exact List.mem_append_right _ hH
    · intro H hH
      change H ∈ P.E.map (geoStrictTransform π C) ++ [π ⁻¹' C] at hH
      rcases List.mem_append.mp hH with hH | hH
      · obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
        exact List.mem_append_left _ (List.mem_map_of_mem (h2 H₀ hH₀))
      · exact List.mem_append_right _ hH
  projection := by
    rintro hp m Y P' Q' ⟨P, Q, L, h, h1, h2, rfl, rfl⟩
    refine ⟨projectionTest P, projectionTest Q, L.map ((Prod.fst : projectionAmbient Y → Y) ⁻¹' ·) ++ [horizontal Y],
      (isLocStable_locEquiv κ).projection hp h, ?_, ?_, rfl, rfl⟩
    · intro H hH
      rcases List.mem_append.mp hH with hH | hH
      · obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
        exact List.mem_append_left _ (List.mem_map_of_mem (h1 H₀ hH₀))
      · exact List.mem_append_right _ hH
    · intro H hH
      change H ∈ P.E.map ((Prod.fst : projectionAmbient Y → Y) ⁻¹' ·) ++ [horizontal Y] at hH
      rcases List.mem_append.mp hH with hH | hH
      · obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
        exact List.mem_append_left _ (List.mem_map_of_mem (h2 H₀ hH₀))
      · exact List.mem_append_right _ hH
  restrict := by
    rintro m Y P' Q' ⟨P, Q, L, h, h1, h2, rfl, rfl⟩ U
    refine ⟨MarkedIdeal.pullback (Subtype.val : U → Y) P, MarkedIdeal.pullback (Subtype.val : U → Y) Q,
      L.map ((Subtype.val : U → Y) ⁻¹' ·), (isLocStable_locEquiv κ).restrict h U, ?_, ?_, rfl, rfl⟩
    · intro H hH
      obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
      exact List.mem_map_of_mem (h1 H₀ hH₀)
    · intro H hH
      change H ∈ P.E.map ((Subtype.val : U → Y) ⁻¹' ·) at hH
      obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
      exact List.mem_map_of_mem (h2 H₀ hH₀)

/-- **Replacing the boundary by a list with the same members keeps a local equivalence** (kinds without exceptional
blowups). -/
theorem locEquiv_reorder {κ : Kinds} (hexc : κ.exc = false) {n : ℕ} {X : CMfd.{u} n} {P Q : MarkedIdeal n X}
    (h : LocEquiv κ P Q) {L : List (Set X)} (h1 : ∀ H ∈ L, H ∈ P.E) (h2 : ∀ H ∈ P.E, H ∈ L) :
    LocEquiv κ { P with E := L } { Q with E := L } :=
  LocEquiv.of_isLocStable (isLocStable_reorderRel κ) hexc ⟨P, Q, L, h, h1, h2, rfl, rfl⟩

/-- **Permuting the boundary keeps a local equivalence.** -/
theorem locEquiv_perm {κ : Kinds} (hexc : κ.exc = false) {n : ℕ} {X : CMfd.{u} n} {P Q : MarkedIdeal n X}
    (h : LocEquiv κ P Q) {L : List (Set X)} (hL : L.Perm P.E) :
    LocEquiv κ { P with E := L } { Q with E := L } :=
  locEquiv_reorder hexc h (fun _ hH => hL.subset hH) (fun _ hH => hL.symm.subset hH)

end Reorder

end

end Hironaka.HironakaG8ClassStepPerm
