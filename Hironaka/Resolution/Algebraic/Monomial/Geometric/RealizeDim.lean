/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Monomial.Geometric.Pieces
import Hironaka.Resolution.Algebraic.Monomial.Geometric.RealizeNil
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Step 3 and the dimension bound

The combinatorial state `MonomialState` carries the dimension bound `n` as a data field. It is
read by `step3` for the number of phases (`phases st.n 1 st _`, Kollár's Steps `3.1, …, 3.n` of
[Kol07, 111]) and by the invariant `nerve_card` (every face has at most `n` components), and by
nothing else: `faces`, `Star`, `choice`, `total`, `labelTuple`, `blowUpNerve` and `blowUp` never
consult it (`blowUp` copies it). The geometric Step 3 `PieceFamily.realize n m hV` therefore
depends on `n` only through the phase count, and the phases beyond the true bound are trivial:
a face of size `s > n'` does not exist when every face has at most `n'` components, so `(∗_s)`
holds vacuously (`star_of_lt`), Kollár's choice is empty (`choice_eq_empty_iff`) and the phase
returns the state unchanged with an empty run (`phase_of_not_nonempty`, `phases_eq_of_star`).
Hence *the realised Step 3 of a piece family is the same for any two dimension bounds `n' ≤ n`
for which the family's data are valid* (`realize_eq_of_le`).

The proof is a lockstep induction along the well-founded recursion of `phase` (`phase.induct`,
as in `Hironaka/Resolution/Algebraic/Monomial/Restrict/Phase.lean`): two states with the same data
and possibly different bounds (`EqUpToDim`) make the same choice, blow up to states again equal up
to the bound, and so run the same phase (`phase_eqUpToDim`); the phases `r, r + 1, …` of two such
states agree as soon as both runs reach the smaller bound (`phases_eqUpToDim_le`, an induction
on the phase counts carrying the invariant; the extra phases of the longer run are empty by
`phases_eq_of_star`, the bound read from the state with the smaller `n`, whose `nerve_card`
bounds the common nerve).

Not in the sources: Kollár's `n = dim X` is the dimension of the ambient variety, and the
question does not arise for him. It arises here because `BMO_{n,m}` is defined for every `n`
and the induction on the dimension in `Hironaka/Resolution/Algebraic/Stage/` compares the functors
at `n` and at `n' ≤ n` on the same triple (`Hironaka/Resolution/Algebraic/Stage/CongrBMO.lean`).
-/

@[expose] public section

universe u

open AlgebraicGeometry TopologicalSpace Finset

namespace Hironaka.Monomial

namespace MonomialState

/-- Two states with the same data (mark, counters, labels, exponents and nerve) and possibly
different dimension bounds `n`. -/
structure EqUpToDim (st st' : MonomialState) : Prop where
  m_eq : st.m = st'.m
  nextComp_eq : st.nextComp = st'.nextComp
  nextLabel_eq : st.nextLabel = st'.nextLabel
  label_eq : st.label = st'.label
  a_eq : st.a = st'.a
  nerve_eq : st.nerve = st'.nerve

/-- The state `st` with its dimension bound replaced by `n₀` (a bound for its nerve). -/
def withN (st : MonomialState) (n₀ : ℕ) (hc : ∀ T ∈ st.nerve, T.card ≤ n₀) : MonomialState :=
  { st with n := n₀, nerve_card := hc }

namespace EqUpToDim

variable {st st' : MonomialState}

/-- A state equal to `st` up to the dimension bound is `st` with the other state's bound. -/
theorem eq_withN (h : EqUpToDim st st') :
    st' = st.withN st'.n (fun T hT => st'.nerve_card T (h.nerve_eq ▸ hT)) :=
  MonomialState.ext rfl h.m_eq.symm h.nextComp_eq.symm h.nextLabel_eq.symm h.label_eq.symm
    h.a_eq.symm h.nerve_eq.symm

/-- States equal up to the dimension bound satisfy the same `(∗_s)`. -/
theorem star (h : EqUpToDim st st') (s : ℕ) : st.Star s ↔ st'.Star s := by
  rw [h.eq_withN]
  exact Iff.rfl

/-- States equal up to the dimension bound make the same choice at every phase. -/
theorem choice (h : EqUpToDim st st') (r : ℕ) : st.choice r = st'.choice r := by
  rw [h.eq_withN]
  rfl

/-- Blowing up two states equal up to the dimension bound along the same centre gives states
equal up to the dimension bound. -/
theorem blowUp (h : EqUpToDim st st') (S : Finset (Finset ℕ)) :
    EqUpToDim (st.blowUp S) (st'.blowUp S) := by
  rw [h.eq_withN]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end EqUpToDim

/-- Two states equal up to the dimension bound run the same phase: the same centres, and final
states again equal up to the dimension bound. -/
theorem phase_eqUpToDim (r : ℕ) (st : MonomialState) (hs : ∀ s < r, st.Star s) :
    ∀ (st' : MonomialState) (hs' : ∀ s < r, st'.Star s), EqUpToDim st st' →
      EqUpToDim (phase r st hs).1 (phase r st' hs').1 ∧ (phase r st hs).2 =
          (phase r st' hs').2 := by
  induction st, hs using phase.induct r with
  | case1 st hs hne ih =>
    intro st' hs' h
    have hne' : (st'.choice r).Nonempty := by rw [← h.choice r]; exact hne
    rw [phase_of_nonempty st hs hne, phase_of_nonempty st' hs' hne']
    have hb : EqUpToDim (st.blowUp (st.choice r)) (st'.blowUp (st'.choice r)) := by
      rw [← h.choice r]
      exact h.blowUp _
    obtain ⟨h1, h2⟩ := ih (st'.blowUp (st'.choice r)) (fun _ hsr => st'.star_blowUp hs' hsr) hb
    exact ⟨h1, congrArg₂ List.cons (h.choice r) h2⟩
  | case2 st hs hne =>
    intro st' hs' h
    have hne' : ¬ (st'.choice r).Nonempty := by rw [← h.choice r]; exact hne
    rw [phase_of_not_nonempty st hs hne, phase_of_not_nonempty st' hs' hne']
    exact ⟨h, rfl⟩

/-- The runs of the phases `r, …` of two states equal up to the dimension bound agree as soon
as both runs reach the smaller dimension bound: the phases beyond it are empty
(`phases_eq_of_star`, the bound read from the state with the smaller `n`). -/
theorem phases_eqUpToDim_le : ∀ (k k' r : ℕ) (st st' : MonomialState) (hs : ∀ s < r, st.Star s)
    (hs' : ∀ s < r, st'.Star s), EqUpToDim st st' → st'.n < r + k → st'.n < r + k' →
      (phases k r st hs).2 = (phases k' r st' hs').2
  | 0, k', r, st, st', hs, hs', _, hk, _ => by
    have hall' : ∀ s, st'.Star s := fun s => by
      by_cases hsr : s < r
      · exact hs' s hsr
      · exact st'.star_of_lt (by omega)
    rw [phases_zero, phases_eq_of_star k' r st' hs' hall']
  | k + 1, 0, r, st, st', hs, hs', h, _, hk' => by
    have hall : ∀ s, st.Star s := fun s => by
      by_cases hsr : s < r
      · exact hs s hsr
      · exact (h.star s).mpr (st'.star_of_lt (by omega))
    rw [phases_zero, phases_eq_of_star (k + 1) r st hs hall]
  | k + 1, k' + 1, r, st, st', hs, hs', h, hk, hk' => by
    rw [phases_succ, phases_succ]
    obtain ⟨h1, h2⟩ := phase_eqUpToDim r st hs st' hs' h
    have hn' : (phase r st' hs').1.n = st'.n := phase_n st' hs'
    have :=
        phases_eqUpToDim_le k k' (r + 1) _ _ (phase_star_succ st hs) (phase_star_succ st' hs') h1
      (by rw [hn']; omega) (by rw [hn']; omega)
    exact congrArg₂ (· ++ ·) h2 this

/-- The run of Step 3 of a state (Kollár's Steps `3.1, …, 3.n` of [Kol07, 111]) is that of any
state equal to it up to the dimension bound with a smaller bound: the phases `n' + 1, …, n` are
empty. -/
theorem step3_eqUpToDim_le {st st' : MonomialState} (h : EqUpToDim st st') (hle : st'.n ≤ st.n) :
    (step3 st).2 = (step3 st').2 :=
  phases_eqUpToDim_le st.n st'.n 1 st st' (star_of_lt_one st) (star_of_lt_one st') h (by omega)
    (by omega)

end MonomialState

namespace PieceFamily

/-- *The realised Step 3 of a piece family does not depend on the dimension bound*: for `n' ≤ n`
and the family's data valid for both, the geometric Step 3 at `n` is the one at `n'`. The two
combinatorial states are equal up to the dimension bound (`toState`'s data fields are the
family's), so their Step 3 runs agree (`step3_eqUpToDim_le`), and `realizeAux` reads the run
only. -/
theorem realize_eq_of_le {X : Scheme.{u}} (Φ : PieceFamily X) {n n' m : ℕ} (hV : Φ.IsValid n m)
    (hV' : Φ.IsValid n' m) (h : n' ≤ n) : Φ.realize n m hV = Φ.realize n' m hV' :=
  congrArg (realizeAux Φ m) (MonomialState.step3_eqUpToDim_le ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ h)

end PieceFamily

end Hironaka.Monomial
