/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Monomial.State

/-!
# The measure decreases under Kollár's choice

The termination argument of [Kol07, 111, Step 3.2 and 3.r] on the combinatorial state of
`Hironaka/Resolution/Algebraic/Monomial/State.lean`. Throughout, `r ≥ 1`, `(∗_s)` holds for every `s
< r`, `S = choice st r` is Kollár's centre at phase `r` (faces of size `r`, common sum `m_r ≥ m`,
common label tuple), and primes denote the state after `blowUp st S`.

* `total_newFace_lt`: a new face `T₁ ∪ {c_P}`, `P ∈ S`, and any `c ∈ P \ T₁` give the old face
  `T₁ ∪ {c}` of the same size with `a'(T₁ ∪ {c_P}) + m = a(T₁ ∪ {c}) + a(P \ {c})` and
  `a(P \ {c}) < m` by `(∗_{r-1})` (for `r = 1` the empty sum), hence
  `a'(T₁ ∪ {c_P}) < a(T₁ ∪ {c})`. This is Kollár's inequality
  `a_{i₁} + ⋯ + a_{i_{r-1}} + a_{j_ℓ} < a_{j₁} + ⋯ + a_{j_r}`, stated for faces of every size,
  not only of size `r`, and with the comparison face `T₁ ∪ {c}` named.
* `measure_blowUp_lt`: `(m'_r, n'_r) < (m_r, n_r)` in `ℕ ×ₗ ℕ`, the `r`-faces of the new state
  being the old `r`-faces outside `S` (same sums) and new faces of sums `< m_r`; so `m_r` does
  not increase, and if it is unchanged the number of maximizers drops by `|S| ≥ 1`.
* `star_blowUp`: `(∗_s)` is preserved for `s < r`. Kollár uses this throughout Step 3.r without
  stating it; not in the sources as a separate statement.
* `measure_blowUp_le`: no pair `(m_s, n_s)` increases. Not in the sources; it is the
  strengthening that makes the measure vectors of the example runs monotone
  (`HironakaExamples/Monomial/Example112.lean`).

`measure_blowUp_lt` is the decreasing measure of the well-founded recursion defining a phase,
and `star_blowUp` carries the hypothesis of the phase along it
(`Hironaka/Resolution/Algebraic/Monomial/Step3Phases.lean`).
-/

public section

namespace Hironaka.Monomial.MonomialState

open Finset

variable (st : MonomialState)

section NewFace

variable {r : ℕ} {P T₁ : Finset ℕ} {c : ℕ}

/-- The inequality of [Kol07, 111, Step 3.2 and 3.r], for faces of every size: for a new face
`T₁ ∪ {c_P}` of the blow-up along Kollár's centre at phase `r` and a component `c ∈ P \ T₁`, the
old face `T₁ ∪ {c}` has the same size, `a'(T₁ ∪ {c_P}) + m = a(T₁ ∪ {c}) + a(P \ {c})`, and
`a(P \ {c}) < m` by `(∗_{r-1})`; hence `a'(T₁ ∪ {c_P}) < a(T₁ ∪ {c})`. -/
theorem total_newFace_lt (hs : ∀ s < r, st.Star s) (hP : P ∈ st.choice r)
    (hT₁ : T₁ ∪ P ∈ st.nerve) (hc : c ∈ P) (hcT₁ : c ∉ T₁) :
    insert c T₁ ∈ st.nerve ∧
    (insert c T₁).card = (insert (st.newComp (st.choice r) P) T₁).card ∧
    (st.blowUp (st.choice r)).total (insert (st.newComp (st.choice r) P) T₁) + st.m =
      st.total (insert c T₁) + st.total (P.erase c) ∧
    st.total (P.erase c) < st.m ∧
    (st.blowUp (st.choice r)).total (insert (st.newComp (st.choice r) P) T₁) <
      st.total (insert c T₁) := by
  have hmem : insert c T₁ ∈ st.nerve :=
    st.mem_nerve_of_subset hT₁ (Finset.insert_subset (Finset.mem_union_right _ hc)
      Finset.subset_union_left) (Finset.insert_nonempty _ _)
  have hold : ∀ x ∈ T₁, x < st.nextComp := fun x hx =>
    st.lt_nextComp_of_mem hT₁ (Finset.mem_union_left _ hx)
  have hnew : st.newComp (st.choice r) P ∉ T₁ := fun h =>
    st.newComp_notMem hT₁ (Finset.mem_union_left _ h)
  have hcard : (insert c T₁).card = (insert (st.newComp (st.choice r) P) T₁).card := by
    rw [Finset.card_insert_of_notMem hcT₁, Finset.card_insert_of_notMem hnew]
  have hmP : st.m ≤ st.total P := st.m_le_total_of_mem_choice hP
  have h1 := st.blowUp_total_insert_newComp (st.choice r) hP hold
  have h2 := st.total_insert (T := T₁) hcT₁
  have h3 := st.total_erase_add hc
  have heq : (st.blowUp (st.choice r)).total (insert (st.newComp (st.choice r) P) T₁) + st.m =
      st.total (insert c T₁) + st.total (P.erase c) := by
    rw [h1, h2]; omega
  have hlt : st.total (P.erase c) < st.m := by
    by_cases hne : (P.erase c).Nonempty
    · have hface : P.erase c ∈ st.nerve :=
        st.mem_nerve_of_subset (st.mem_nerve_of_mem_choice hP) (Finset.erase_subset _ _) hne
      have hr : P.card = r := st.card_of_mem_choice hP
      have hpos : 0 < r := hr ▸ Finset.card_pos.mpr ⟨c, hc⟩
      refine hs (r - 1) (Nat.sub_lt hpos Nat.one_pos) _ (st.mem_faces.mpr ⟨hface, ?_⟩)
      rw [Finset.card_erase_of_mem hc, hr]
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, total_empty]
      exact st.one_le_m
  exact ⟨hmem, hcard, heq, hlt, by omega⟩

end NewFace

section Decrease

variable {r : ℕ} (hs : ∀ s < r, st.Star s)
include hs

/-- Every face of the new state of size `s` is an old face outside the center with its old sum, or
has sum strictly below that of an old face of size `s`: in either case its sum is at most `m_s`,
and a new face achieving `m_s` is an old `s`-face outside the center achieving `m_s`. -/
theorem total_le_maxTotal_of_mem_blowUp_faces {s : ℕ} {T : Finset ℕ}
    (hT : T ∈ (st.blowUp (st.choice r)).faces s) :
    (st.blowUp (st.choice r)).total T ≤ st.maxTotal s ∧
    ((st.blowUp (st.choice r)).total T = st.maxTotal s →
      T ∈ st.faces s ∧ st.total T = st.maxTotal s ∧ T ∉ st.choice r) := by
  obtain ⟨hTn, hTs⟩ := (st.blowUp (st.choice r)).mem_faces.mp hT
  rcases (st.mem_blowUp_nerve (st.choice r) (st.isCenter_choice r)).mp hTn with
    ⟨hTold, hnot⟩ | ⟨P, hP, T₁, hT₁, hPT₁, rfl⟩
  · have htot : (st.blowUp (st.choice r)).total T = st.total T :=
      st.blowUp_total_of_lt _ fun x hx => st.lt_nextComp_of_mem hTold hx
    have hTf : T ∈ st.faces s := st.mem_faces.mpr ⟨hTold, hTs⟩
    refine ⟨htot ▸ st.total_le_maxTotal hTf, fun he => ⟨hTf, htot ▸ he, fun hTS => ?_⟩⟩
    exact hnot T hTS subset_rfl
  · obtain ⟨c, hc, hcT₁⟩ := Finset.not_subset.mp hPT₁
    obtain ⟨hmem, hcard, -, -, hlt⟩ := st.total_newFace_lt hs hP hT₁ hc hcT₁
    have hface : insert c T₁ ∈ st.faces s := st.mem_faces.mpr ⟨hmem, hcard.trans hTs⟩
    have hle := st.total_le_maxTotal hface
    exact ⟨(hlt.trans_le hle).le, fun he => absurd he (ne_of_lt (hlt.trans_le hle))⟩

/-- [Kol07, 111, Step 3.2 and 3.r]: a blow-up along Kollár's centre at phase `r` strictly
decreases `(m_r, n_r)` in `ℕ ×ₗ ℕ`. -/
theorem measure_blowUp_lt (h : (st.choice r).Nonempty) :
    (st.blowUp (st.choice r)).measure r < st.measure r := by
  have hle : (st.blowUp (st.choice r)).maxTotal r ≤ st.maxTotal r :=
    maxTotal_le _ fun T hT => (st.total_le_maxTotal_of_mem_blowUp_faces hs hT).1
  rw [measure, measure, Prod.Lex.toLex_lt_toLex]
  rcases hle.lt_or_eq with hlt | heq
  · exact Or.inl hlt
  · refine Or.inr ⟨heq, ?_⟩
    obtain ⟨P, hP⟩ := h
    refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset fun T hT => ?_).mpr ⟨P, ?_, ?_⟩)
    · obtain ⟨hT1, hT2⟩ := Finset.mem_filter.mp hT
      obtain ⟨hf, ht, -⟩ := (st.total_le_maxTotal_of_mem_blowUp_faces hs hT1).2 (heq ▸ hT2)
      exact Finset.mem_filter.mpr ⟨hf, ht⟩
    · exact Finset.mem_filter.mpr ⟨st.mem_faces_of_mem_choice hP,
        st.total_eq_maxTotal_of_mem_choice hP⟩
    · intro hPm
      obtain ⟨hT1, hT2⟩ := Finset.mem_filter.mp hPm
      exact (st.total_le_maxTotal_of_mem_blowUp_faces hs hT1).2 (heq ▸ hT2) |>.2.2 hP

/-- A phase-`r` blow-up preserves `(∗_s)` for `s < r`. Kollár uses this throughout
[Kol07, 111, Step 3.r] without stating its preservation; not in the sources as such. -/
theorem star_blowUp {s : ℕ} (hsr : s < r) : (st.blowUp (st.choice r)).Star s := by
  intro T hT
  obtain ⟨hTn, hTs⟩ := (st.blowUp (st.choice r)).mem_faces.mp hT
  rcases (st.mem_blowUp_nerve (st.choice r) (st.isCenter_choice r)).mp hTn with
    ⟨hTold, -⟩ | ⟨P, hP, T₁, hT₁, hPT₁, rfl⟩
  · rw [st.blowUp_total_of_lt _ fun x hx => st.lt_nextComp_of_mem hTold hx]
    exact hs s hsr T (st.mem_faces.mpr ⟨hTold, hTs⟩)
  · obtain ⟨c, hc, hcT₁⟩ := Finset.not_subset.mp hPT₁
    obtain ⟨hmem, hcard, -, -, hlt⟩ := st.total_newFace_lt hs hP hT₁ hc hcT₁
    exact hlt.trans (hs s hsr _ (st.mem_faces.mpr ⟨hmem, hcard.trans hTs⟩))

/-- Under a phase-`r` blow-up no pair `(m_s, n_s)` increases. Not in the sources: a
strengthening of the decrease of `(m_r, n_r)`, by the same case analysis of the faces of the
new state. -/
theorem measure_blowUp_le (s : ℕ) :
    (st.blowUp (st.choice r)).measure s ≤ st.measure s := by
  have hle : (st.blowUp (st.choice r)).maxTotal s ≤ st.maxTotal s :=
    maxTotal_le _ fun T hT => (st.total_le_maxTotal_of_mem_blowUp_faces hs hT).1
  rw [measure, measure, Prod.Lex.toLex_le_toLex]
  rcases hle.lt_or_eq with hlt | heq
  · exact Or.inl hlt
  · refine Or.inr ⟨heq, Finset.card_le_card fun T hT => ?_⟩
    obtain ⟨hT1, hT2⟩ := Finset.mem_filter.mp hT
    obtain ⟨hf, ht, -⟩ := (st.total_le_maxTotal_of_mem_blowUp_faces hs hT1).2 (heq ▸ hT2)
    exact Finset.mem_filter.mpr ⟨hf, ht⟩

end Decrease

end Hironaka.Monomial.MonomialState
