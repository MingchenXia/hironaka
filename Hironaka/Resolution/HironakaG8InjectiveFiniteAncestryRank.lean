import Hironaka.Resolution.HironakaG8FiniteBranchingAncestry
import Hironaka.Resolution.HironakaG8CofinalOccupiedAncestry
import Mathlib.Data.Prod.Lex

/-! Countable events with finite ancestry admit distinct natural slots. -/
set_option autoImplicit false
open Set

namespace Hironaka.HironakaG8InjectiveFiniteAncestryRank

open HironakaG8FiniteBranchingAncestry BlowupTowers HironakaG3RTowerClass
  HironakaG8CofinalOccupiedAncestry

/-- A countable transitive strict order with finite predecessor sets has an
injective natural rank increasing along the order. -/
theorem exists_injective_rank_of_finite_predecessors {ι : Type*} [Countable ι]
    {before : ι → ι → Prop} (hTrans : ∀ ⦃a b c⦄, before a b → before b c → before a c)
    (hIrrefl : ∀ b, ¬ before b b) (hFinite : ∀ b, {a | before a b}.Finite) :
    ∃ rank : ι → ℕ, Function.Injective rank ∧ ∀ ⦃a b⦄, before a b → rank a < rank b := by
  classical
  obtain ⟨code, hCode⟩ := Countable.exists_injective_nat ι
  let lower (b : ι) := {a | before a b}
  let closedLower (b : ι) := ((hFinite b).insert b).toFinset
  let cap (b : ι) := (closedLower b).sup code
  let key (b : ι) : ℕ ×ₗ (ℕ ×ₗ ℕ) := toLex (cap b, toLex ((lower b).ncard, code b))
  have hCap (b : ι) : code b ≤ cap b := by
    apply Finset.le_sup
    exact ((hFinite b).insert b).mem_toFinset.mpr (mem_insert _ _)
  have hKey : Function.Injective key := by
    intro a b h
    exact hCode (congrArg (fun z : ℕ ×ₗ (ℕ ×ₗ ℕ) => (ofLex (ofLex z).2).2) h)
  have hKeyOrder {a b : ι} (hab : before a b) : key a < key b := by
    have hCapMono : cap a ≤ cap b := by
      apply Finset.sup_mono
      intro c hc
      have hc' := ((hFinite a).insert a).mem_toFinset.mp hc
      apply ((hFinite b).insert b).mem_toFinset.mpr
      rcases mem_insert_iff.mp hc' with rfl | hca
      · exact mem_insert_of_mem _ hab
      · exact mem_insert_of_mem _ (hTrans hca hab)
    have hLower : lower a ⊂ lower b :=
      ⟨fun _ hc => hTrans hc hab, fun h => hIrrefl a (h hab)⟩
    have hDepth := Set.ncard_lt_ncard hLower (hFinite b)
    apply Prod.Lex.toLex_lt_toLex.mpr
    rcases lt_or_eq_of_le hCapMono with hlt | heq
    · exact Or.inl hlt
    · exact Or.inr ⟨heq, Prod.Lex.toLex_lt_toLex.mpr (Or.inl hDepth)⟩
  let keyLower (b : ι) := {a | key a < key b}
  have hKeyFinite (b : ι) : (keyLower b).Finite := by
    refine ((Set.finite_Iic (cap b)).preimage hCode.injOn).subset ?_
    intro a ha
    exact (hCap a).trans (Prod.Lex.monotone_fst_ofLex (le_of_lt ha))
  have hKeyCount {a b : ι} (hab : key a < key b) : (keyLower a).ncard < (keyLower b).ncard :=
    Set.ncard_lt_ncard ⟨fun _ hc => lt_trans hc hab, fun h => (lt_irrefl (key a)) (h hab)⟩ (hKeyFinite b)
  refine ⟨fun a => (keyLower a).ncard, ?_, fun {_ _} hab => hKeyCount (hKeyOrder hab)⟩
  intro a b h
  rcases lt_trichotomy (key a) (key b) with hab | he | hba
  · exact (ne_of_lt (hKeyCount hab) h).elim
  · exact hKey he
  · exact (ne_of_lt (hKeyCount hba) h.symm).elim

/-- Well-founded countable dependencies with finite incoming branching admit
distinct slots even when many unrelated events have the same ancestry depth. -/
theorem exists_injective_rank_of_finite_incoming {ι : Type*} [Countable ι]
    {before : ι → ι → Prop} (hWell : WellFounded before) (hFinite : ∀ b, {a | before a b}.Finite) :
    ∃ rank : ι → ℕ, Function.Injective rank ∧
      ∀ ⦃a b⦄, Relation.TransGen before a b → rank a < rank b := by
  obtain ⟨rank, hRank⟩ := exists_natural_rank_of_finite_incoming hWell hFinite
  exact exists_injective_rank_of_finite_predecessors (before := Relation.TransGen before)
    (fun {_ _ _} hab hbc => hab.trans hbc)
    (fun b h => (lt_irrefl (rank b)) (hRank h)) (finite_ancestors_of_finite_incoming hWell hFinite)

/-- Actual represented events of a countable chart chain are countable,
because every event has an occupied natural-number occurrence. -/
theorem cofinal_events_countable {n : ℕ} {X Z : CMfd.{0} n} {P : Z → X}
    {K : LocalTowerClass X} {c : ℕ → TowerChart K Z P} {ι : Type*} (A : CofinalEvents c ι)
    (hOccurs : ∀ e, ∃ i p, A.event i p = e) : Countable ι := by
  let label := fun p : (Σ i : ℕ, {k // Occupied (c i).T k}) => A.event p.1 p.2
  have hLabel : Function.Surjective label := by
    intro e
    obtain ⟨i,p,hp⟩ := hOccurs e
    exact ⟨⟨i,p⟩,hp⟩
  exact hLabel.countable

/-- A dependency relation on the represented physical events admits
distinct natural slots under finite incoming branching and well-foundedness. -/
theorem exists_injective_rank_of_cofinal_dependencies
    {n : ℕ} {X Z : CMfd.{0} n} {P : Z → X}
    {K : LocalTowerClass X} {c : ℕ → TowerChart K Z P} {ι : Type*} (A : CofinalEvents c ι)
    (hOccurs : ∀ e, ∃ i p, A.event i p = e) {before : ι → ι → Prop}
    (hWell : WellFounded before) (hFinite : ∀ b, {a | before a b}.Finite) :
    ∃ rank : ι → ℕ, Function.Injective rank ∧
      ∀ ⦃a b⦄, Relation.TransGen before a b → rank a < rank b := by
  let : Countable ι := cofinal_events_countable A hOccurs
  exact exists_injective_rank_of_finite_incoming hWell hFinite

end Hironaka.HironakaG8InjectiveFiniteAncestryRank
