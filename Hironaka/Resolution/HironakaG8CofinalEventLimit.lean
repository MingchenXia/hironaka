import Hironaka.Resolution.HironakaG8CofinalOccupiedAncestry

/-! # Events from coherent embeddings of occupied chart occurrences -/
set_option autoImplicit false

namespace Hironaka.HironakaG8CofinalEventLimit

open Set
open BlowupTowers HironakaG3RTowerClass HironakaG8CofinalOccupiedAncestry

variable {n : ℕ} {X Z : CMfd.{0} n} {P : Z → X}
    {K : LocalTowerClass X} (c : ℕ → TowerChart K Z P)

abbrev Slots (i : ℕ) := {k // Occupied (c i).T k}

variable (up : ∀ {i j}, i ≤ j → Slots c i → Slots c j)
    (up_id : ∀ (i : ℕ) (p : Slots c i), up (le_refl i) p = p)
    (up_comp : ∀ {i j k} (hij : i ≤ j) (hjk : j ≤ k) (p : Slots c i),
      up hjk (up hij p) = up (hij.trans hjk) p)
    (up_mono : ∀ {i j} (hij : i ≤ j), StrictMono (up hij))

/-- Two occupied occurrences describe the same event when they agree
after lifting to a common physical chart. -/
def occurrenceSetoid : Setoid (Σ i : ℕ, Slots c i) where
  r p q := ∃ (k : ℕ) (hp : p.1 ≤ k) (hq : q.1 ≤ k), up hp p.2 = up hq q.2
  iseqv := by
    refine ⟨fun p => ⟨p.1, le_rfl, le_rfl, rfl⟩, ?_, ?_⟩
    · rintro p q ⟨k,hp,hq,h⟩
      exact ⟨k,hq,hp,h.symm⟩
    · rintro p q r ⟨k,hpk,hqk,hpq⟩ ⟨l,hql,hrl,hqr⟩
      let kM : k ≤ max k l := le_max_left _ _
      let lM : l ≤ max k l := le_max_right _ _
      refine ⟨max k l,hpk.trans kM,hrl.trans lM,?_⟩
      rw [← up_comp hpk kM, hpq, up_comp hqk kM, ← up_comp hql lM, hqr, up_comp hrl lM]

/-- The actual global event names need no separate input once the
occupied slot embeddings and their composition law are known. -/
def eventLimit : CofinalEvents c (Quotient (occurrenceSetoid c up up_comp)) where
  event i p := Quotient.mk _ ⟨i,p⟩
  injective i := by
    intro p q h
    obtain ⟨k,hik,_,he⟩ := Quotient.exact h
    exact (up_mono hik).injective he
  lift h := up h
  lift_event := by
    intro i j hij p
    apply Quotient.sound
    exact ⟨j,le_rfl,hij,up_id j (up hij p)⟩
  lift_mono := by
    intro i j hij p q hp
    exact up_mono hij hp

theorem eventLimit_occurs (e : Quotient (occurrenceSetoid c up up_comp)) :
    ∃ (i : ℕ) (p : Slots c i),
      (eventLimit c up (up_comp := up_comp) (up_id := up_id) (up_mono := up_mono)).event i p = e := by
  induction e using Quotient.inductionOn with
  | _ a => exact ⟨a.1,a.2,rfl⟩

/-- Equality of two represented events can be tested in any chart containing
both representatives, independently of which common chart is used. -/
theorem eventLimit_eq_iff_at_chart {i j k : ℕ} (hi : i ≤ k) (hj : j ≤ k)
    (p : Slots c i) (q : Slots c j) :
    let A := eventLimit c up (up_comp := up_comp) (up_id := up_id) (up_mono := up_mono)
    A.event i p = A.event j q ↔ up hi p = up hj q := by
  dsimp only
  let A := eventLimit c up (up_comp := up_comp) (up_id := up_id) (up_mono := up_mono)
  change A.event i p = A.event j q ↔ A.lift hi p = A.lift hj q
  rw [← A.lift_event hi p, ← A.lift_event hj q]
  exact (A.injective k).eq_iff

/-- The chronological order of represented events can likewise be
read in any larger chart containing both occupied occurrences. -/
theorem eventLimit_before_iff_at_chart {i j k : ℕ} (hi : i ≤ k) (hj : j ≤ k)
    (p : Slots c i) (q : Slots c j) :
    let A := eventLimit c up (up_comp := up_comp) (up_id := up_id) (up_mono := up_mono)
    A.Before (A.event i p) (A.event j q) ↔ (up hi p).val < (up hj q).val := by
  dsimp only
  let A := eventLimit c up (up_comp := up_comp) (up_id := up_id) (up_mono := up_mono)
  change A.Before (A.event i p) (A.event j q) ↔ (A.lift hi p).val < (A.lift hj q).val
  rw [← A.lift_event hi p, ← A.lift_event hj q]
  exact A.before_iff_slot_lt k _ _

end Hironaka.HironakaG8CofinalEventLimit
