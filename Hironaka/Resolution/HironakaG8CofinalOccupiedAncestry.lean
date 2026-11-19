import Hironaka.Resolution.HironakaG8StageRankCoherence

/-! Occupied events of nested physical charts and the finite-ancestry requirement. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8CofinalOccupiedAncestry

open Hironaka.BlowupSequences BlowupTowers HironakaG3RTowerClass
  HironakaG8StageRankCoherence HironakaG3EmptyAwareHistory BlowupTowerTransforms

/-- The raw zero-based steps whose actual centres are nonempty. -/
def Occupied {n : ℕ} {X : CMfd.{0} n} : {Y : CMfd.{0} n} → BlowupTower X Y → ℕ → Prop
  | _, .refl, _ => False
  | _, .step T C _ _, i => Occupied T i ∨ (i = T.length ∧ C.Nonempty)

theorem occupied_lt_length {n : ℕ} {X Y : CMfd.{0} n} (T : BlowupTower X Y)
    {i : ℕ} (h : Occupied T i) : i < T.length := by
  induction T with
  | refl => exact h.elim
  | step T C π hπ ih =>
    rw [BlowupTower.length_step]
    rcases h with h | ⟨rfl,_⟩
    · exact Nat.lt_succ_of_lt (ih h)
    · exact Nat.lt_succ_self _

/-- Each actual occupied trace on a literal open is the same raw slot of
an occupied step of the original tower. -/
theorem occupied_of_restrict {n : ℕ} {X Y : CMfd.{0} n} (U : Opens X)
    (T : BlowupTower X Y) {i : ℕ} (h : Occupied (restrict U T) i) : Occupied T i := by
  induction T with
  | refl => exact h
  | step T C π hπ ih =>
    rcases h with h | ⟨hi,⟨x,hx⟩⟩
    · exact Or.inl (ih h)
    · rw [length_restrict] at hi
      exact Or.inr ⟨hi,⟨x.val,hx⟩⟩

/-- Count only genuine occupied physical occurrences. -/
noncomputable def occupiedCount {n : ℕ} {X : CMfd.{0} n} :
    {Y : CMfd.{0} n} → BlowupTower X Y → ℕ
  | _, .refl => 0
  | _, .step T C _ _ => by classical exact occupiedCount T + if C.Nonempty then 1 else 0

theorem occupiedCount_emptyAware {n : ℕ} {X A Y B : CMfd.{0} n}
    {φ : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A}
    {ψ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B}
    {T : BlowupTower X Y} {S : BlowupTower A B} (h : EmptyAwareTowerIso φ T S ψ) :
    occupiedCount T = occupiedCount S := by
  classical
  induction h with
  | refl => rfl
  | @step Y B Z W T S ψ h C π hπ C' ρ hρ χ hMap hC ih =>
    have hne : C.Nonempty ↔ C'.Nonempty := by
      rw [← hC]
      exact ψ.surjective.nonempty_preimage
    simp only [occupiedCount,ih,hne]
  | leftEmpty h hρ e he ih => simpa [occupiedCount] using ih
  | rightEmpty h hρ e he ih => simpa [occupiedCount] using ih

/-- A chart labels each occupied raw occurrence. The nested maps retain
whole event identity and chronological position. These explicit data are
the required interpretation of nested overlap comparisons on events. -/
structure CofinalEvents {n : ℕ} {X Z : CMfd.{0} n} {P : Z → X}
    {K : LocalTowerClass X} (c : ℕ → TowerChart K Z P) (ι : Type*) where
  event : (i : ℕ) → {k // Occupied (c i).T k} → ι
  injective : ∀ i, Function.Injective (event i)
  lift : ∀ {i j : ℕ}, i ≤ j → {k // Occupied (c i).T k} → {k // Occupied (c j).T k}
  lift_event : ∀ {i j : ℕ} (h : i ≤ j) k, event j (lift h k) = event i k
  lift_mono : ∀ {i j : ℕ} (h : i ≤ j) {p q}, p.val < q.val →
    (lift h p).val < (lift h q).val

namespace CofinalEvents

variable {n : ℕ} {X Z : CMfd.{0} n} {P : Z → X} {K : LocalTowerClass X}
  {c : ℕ → TowerChart K Z P} {ι : Type*} (A : CofinalEvents c ι)

/-- Dependency means that one actual occupied occurrence precedes the
other in a single local physical chart. -/
def Before (a b : ι) : Prop :=
  ∃ (i : ℕ) (p q : {k // Occupied (c i).T k}),
    A.event i p = a ∧ A.event i q = b ∧ p.val < q.val

theorem before_iff_slot_lt (i : ℕ) (p q : {k // Occupied (c i).T k}) :
    A.Before (A.event i p) (A.event i q) ↔ p.val < q.val := by
  refine ⟨?_,fun h => ⟨i,p,q,rfl,rfl,h⟩⟩
  rintro ⟨j,r,s,hr,hs,hrs⟩
  let m := max i j
  let hi : i ≤ m := le_max_left _ _
  let hj : j ≤ m := le_max_right _ _
  have hp : A.lift hi p = A.lift hj r := A.injective m (by rw [A.lift_event,A.lift_event,hr])
  have hq : A.lift hi q = A.lift hj s := A.injective m (by rw [A.lift_event,A.lift_event,hs])
  have hM : (A.lift hi p).val < (A.lift hi q).val := by
    rw [hp,hq]
    exact A.lift_mono hj hrs
  by_contra h
  rcases lt_or_eq_of_le (le_of_not_gt h) with hLT | hEq
  · exact (not_lt_of_ge (A.lift_mono hi hLT).le) hM
  · exact (not_lt_of_ge (le_of_eq (congrArg (fun t => (A.lift hi t).val) (Subtype.ext hEq)))) hM

theorem before_trans {a b d : ι} (hab : A.Before a b) (hbd : A.Before b d) : A.Before a d := by
  obtain ⟨i,p,q,hp,hq,hpq⟩ := hab
  obtain ⟨j,r,s,hr,hs,hrs⟩ := hbd
  let m := max i j
  let hi : i ≤ m := le_max_left _ _
  let hj : j ≤ m := le_max_right _ _
  have he : A.lift hi q = A.lift hj r := A.injective m (by rw [A.lift_event,A.lift_event,hq,hr])
  refine ⟨m,A.lift hi p,A.lift hj s,(A.lift_event hi p).trans hp,(A.lift_event hj s).trans hs,?_⟩
  exact (A.lift_mono hi hpq).trans (he ▸ A.lift_mono hj hrs)

theorem before_irrefl (a : ι) : ¬ A.Before a a := by
  rintro ⟨i,p,q,hp,hq,h⟩
  exact (Nat.ne_of_lt h) (congrArg Subtype.val (A.injective i (hp.trans hq.symm)))

/-- If a single finite chart contains an event and *all* its predecessors,
its original slot bounds every incoming dependency chain. A common chart
for each finite subchain alone gives no such uniform bound. -/
theorem path_length_le_slot_of_ancestrally_complete
    (i : ℕ) (p : {k // Occupied (c i).T k})
    (hComplete : ∀ a, A.Before a (A.event i p) → ∃ q, A.event i q = a)
    {l : ℕ} (hPath : DependencyPath A.Before l (A.event i p)) : l ≤ p.val := by
  have hAux : ∀ (l : ℕ) (a : ι), DependencyPath A.Before l a →
      ∀ (q : {k // Occupied (c i).T k}), A.event i q = a →
      (a = A.event i p ∨ A.Before a (A.event i p)) → l ≤ q.val := by
    intro l a h
    induction h with
    | nil => intro q hq hLe; omega
    | @step a b l hab hPath ih =>
      intro q hq hb
      have ha : A.Before a (A.event i p) := by
        rcases hb with h | h
        · rwa [← h]
        · exact A.before_trans hab h
      obtain ⟨r,hr⟩ := hComplete a ha
      have hrq : r.val < q.val := (A.before_iff_slot_lt i r q).mp (by rwa [hr,hq])
      have hle := ih r hr (Or.inr ha)
      omega
  exact hAux l _ hPath p rfl (Or.inl rfl)

/-- An ancestry-complete nested chart for each event suffices for the
actual compatible natural rank, with no uniform global finite bound. -/
theorem exists_rank_of_ancestrally_complete_charts
    (hComplete : ∀ e, ∃ (i : ℕ) (p : {k // Occupied (c i).T k}),
      A.event i p = e ∧ ∀ a, A.Before a e → ∃ q, A.event i q = a) :
    ∃ rank : ι → ℕ, ∀ ⦃a b⦄, A.Before a b → rank a < rank b := by
  apply (exists_natural_rank_iff A.Before).mpr
  intro e
  obtain ⟨i,p,rfl,hp⟩ := hComplete e
  exact ⟨p.val,fun _ h => A.path_length_le_slot_of_ancestrally_complete i p hp h⟩

/-- Nested order-preserving windows place any two represented events
in one actual finite chart. -/
theorem before_total_of_occurs
    (hOccurs : ∀ a, ∃ (i : ℕ) (p : {k // Occupied (c i).T k}), A.event i p = a)
    {a b : ι} (hne : a ≠ b) : A.Before a b ∨ A.Before b a := by
  obtain ⟨i,p,hp⟩ := hOccurs a
  obtain ⟨j,q,hq⟩ := hOccurs b
  let m := max i j
  let hi : i ≤ m := le_max_left _ _
  let hj : j ≤ m := le_max_right _ _
  have ha := (A.lift_event hi p).trans hp
  have hb := (A.lift_event hj q).trans hq
  have hne' : (A.lift hi p).val ≠ (A.lift hj q).val := by
    intro he
    exact hne (ha.symm.trans ((congrArg (A.event m) (Subtype.ext he)).trans hb))
  rcases lt_or_gt_of_ne hne' with h | h
  · exact Or.inl ⟨m,_,_,ha,hb,h⟩
  · exact Or.inr ⟨m,_,_,hb,ha,h⟩

theorem finite_predecessors_of_rank
    (hOccurs : ∀ a, ∃ (i : ℕ) (p : {k // Occupied (c i).T k}), A.event i p = a)
    (rank : ι → ℕ) (hr : ∀ ⦃a b⦄, A.Before a b → rank a < rank b) (b : ι) :
    {a | A.Before a b}.Finite := by
  let f : {a // A.Before a b} → Fin (rank b) := fun a => ⟨rank a.val,hr a.property⟩
  have hf : Function.Injective f := by
    intro a d he
    apply Subtype.ext
    by_contra hn
    have hEq : rank a.val = rank d.val := congrArg Fin.val he
    rcases A.before_total_of_occurs hOccurs hn with h | h
    · exact (Nat.ne_of_lt (hr h)) hEq
    · exact (Nat.ne_of_lt (hr h)) hEq.symm
  exact @Set.toFinite _ _ (Finite.of_injective f hf)

theorem exists_chart_of_finset
    (hOccurs : ∀ a, ∃ (i : ℕ) (p : {k // Occupied (c i).T k}), A.event i p = a)
    (s : Finset ι) :
    ∃ i : ℕ, ∀ a ∈ s, ∃ p : {k // Occupied (c i).T k}, A.event i p = a := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0,by simp⟩
  | @insert a s ha ih =>
    obtain ⟨i,p,hp⟩ := hOccurs a
    obtain ⟨j,hj⟩ := ih
    refine ⟨max i j,?_⟩
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact ⟨A.lift (le_max_left i j) p,(A.lift_event _ _).trans hp⟩
    · obtain ⟨q,hq⟩ := hj b hb
      exact ⟨A.lift (le_max_right i j) q,(A.lift_event _ _).trans hq⟩

/-- Serial natural ranks are equivalent to each event having finitely many
predecessors across the entire nested system. Finite local length alone
gives only finite-stage witnesses for individual predecessor relations. -/
theorem exists_rank_iff_finite_predecessors
    (hOccurs : ∀ a, ∃ (i : ℕ) (p : {k // Occupied (c i).T k}), A.event i p = a) :
    (∃ rank : ι → ℕ, ∀ ⦃a b⦄, A.Before a b → rank a < rank b) ↔
      ∀ b, {a | A.Before a b}.Finite := by
  constructor
  · rintro ⟨r,hr⟩
    exact A.finite_predecessors_of_rank hOccurs r hr
  · intro h
    classical
    apply A.exists_rank_of_ancestrally_complete_charts
    intro b
    let s := (h b).toFinset
    obtain ⟨i,hi⟩ := A.exists_chart_of_finset hOccurs (insert b s)
    obtain ⟨p,hp⟩ := hi b (Finset.mem_insert_self _ _)
    refine ⟨i,p,hp,?_⟩
    intro a ha
    exact hi a (Finset.mem_insert_of_mem ((h b).mem_toFinset.mpr ha))

end CofinalEvents

/-- An abstract nested finite occurrence system can keep introducing an
earlier event. This example is about the ordering implication alone. -/
theorem nested_finite_reverse_occurrences :
    ∃ event : (i : ℕ) → Fin (i+1) → ℕ,
      (∀ i, Function.Injective (event i)) ∧
      (∀ i j, i ≤ j → ∃ lift : Fin (i+1) → Fin (j+1),
        StrictMono lift ∧ ∀ p, event j (lift p) = event i p) ∧
      ¬ ∃ rank : ℕ → ℕ, ∀ i (p q : Fin (i+1)), p < q → rank (event i p) < rank (event i q) := by
  let e (i : ℕ) (p : Fin (i+1)) := i - p.val
  refine ⟨e,?_,?_,?_⟩
  · intro i p q h
    apply Fin.ext
    dsimp [e] at h
    have hp := p.isLt
    have hq := q.isLt
    omega
  · intro i j hij
    let f (p : Fin (i+1)) : Fin (j+1) := ⟨p.val+(j-i),by have := p.isLt; omega⟩
    refine ⟨f,?_,?_⟩
    · intro p q h
      exact Nat.add_lt_add_right h _
    · intro p
      dsimp [e,f]
      have := p.isLt
      omega
  · rintro ⟨r,hr⟩
    apply no_natural_rank_for_reverse_links
    refine ⟨r,fun k => ?_⟩
    have h := hr (k+1) ⟨0,by omega⟩ ⟨1,by omega⟩ (show (0 : ℕ) < 1 by omega)
    simpa [e] using h

end Hironaka.HironakaG8CofinalOccupiedAncestry
