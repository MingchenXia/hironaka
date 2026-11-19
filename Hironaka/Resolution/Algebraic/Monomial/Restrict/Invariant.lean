/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Monomial.Restrict
public import Hironaka.Resolution.Algebraic.Monomial.Step3Phases
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The invariant of the restriction argument

The invariant carried along the pair of runs in the proof that Kollár's Step 3 commutes with
restriction to a subnerve (`Sub` of `Hironaka/Resolution/Algebraic/Monomial/Restrict.lean`; the
second clause of [Kol07, 34.1]). Not in the sources. `Sub L N` is preserved by a blow-up along any
finset of faces (`Sub.blowUp`: the nerve rule is monotone in the nerve); if a face of Kollár's
centre of `N` lies in `L`, the centre of `L` is the centre of `N` restricted to the faces of `L`
(`Sub.choice_eq_of_mem`: `L`'s maximum is `N`'s and the lexicographically smallest label tuple
is the same); a blow-up along nonempty faces none of which is a face of `L` does not change the
nerve of `L` (`blowUp_nerve_of_forall_notMem`); and the pulled-back run ends in a state `Sub` the
final state of `N` (`Sub.foldl`, `sub_foldl_step3`). The induction that uses these is
`Hironaka/Resolution/Algebraic/Monomial/Restrict/Phase.lean`.
-/

public section

namespace Hironaka.Monomial.MonomialState

open Finset

theorem blowUpNerve_mono {N N' S : Finset (Finset ℕ)} {c : Finset ℕ → ℕ} (h : N ⊆ N') :
    blowUpNerve N S c ⊆ blowUpNerve N' S c := by
  intro T hT
  rcases mem_blowUpNerve.mp hT with ⟨h1, h2⟩ | ⟨P, hP, T₁, h1, h2, h3, rfl⟩
  · exact mem_blowUpNerve.mpr (Or.inl ⟨h h1, h2⟩)
  · exact mem_blowUpNerve.mpr (Or.inr ⟨P, hP, T₁, h1.imp_right (fun h1 => h h1), h h2, h3, rfl⟩)

theorem Sub.total_eq {L N : MonomialState} (h : Sub L N) (T : Finset ℕ) :
    L.total T = N.total T := by
  simp only [total, h.a_eq]

theorem Sub.newComp_eq {L N : MonomialState} (h : Sub L N) (S : Finset (Finset ℕ)) (P : Finset ℕ) :
    L.newComp S P = N.newComp S P := by
  simp only [newComp, h.nextComp_eq]

/-- The invariant `L_i ⊆ N_i` with equal exponents and labels is preserved by a blow-up along
any `S`: the rule is monotone in the nerve. -/
theorem Sub.blowUp {L N : MonomialState} (h : Sub L N) (S : Finset (Finset ℕ)) :
    Sub (L.blowUp S) (N.blowUp S) where
  n_eq := h.n_eq
  m_eq := h.m_eq
  nextComp_eq := by simp only [blowUp_nextComp, h.nextComp_eq]
  nextLabel_eq := by simp only [blowUp_nextLabel, h.nextLabel_eq]
  label_eq := by
    funext c
    change (if c < L.nextComp then L.label c else L.nextLabel) =
      (if c < N.nextComp then N.label c else N.nextLabel)
    rw [h.nextComp_eq, h.label_eq, h.nextLabel_eq]
  a_eq := by
    funext c
    change (if c < L.nextComp then L.a c
        else (S.filter fun P => L.newComp S P = c).sup fun P => L.total P - L.m) =
      (if c < N.nextComp then N.a c
        else (S.filter fun P => N.newComp S P = c).sup fun P => N.total P - N.m)
    simp only [h.nextComp_eq, h.a_eq, h.m_eq, h.total_eq, h.newComp_eq]
  nerve_sub := by
    rw [blowUp_nerve, blowUp_nerve]
    have : L.newComp S = N.newComp S := funext (h.newComp_eq S)
    rw [this]
    exact blowUpNerve_mono h.nerve_sub

theorem Sub.mem_faces {L N : MonomialState} (h : Sub L N) {r : ℕ} {T : Finset ℕ}
    (hT : T ∈ L.faces r) : T ∈ N.faces r := by
  obtain ⟨h1, h2⟩ := L.mem_faces.mp hT
  exact N.mem_faces.mpr ⟨h.nerve_sub h1, h2⟩

theorem Sub.labelTuple_eq {L N : MonomialState} (h : Sub L N) (T : Finset ℕ) :
    L.labelTuple T = N.labelTuple T := by
  simp only [labelTuple, labels, h.label_eq]

/-- If a face of Kollár's centre of `N` lies in `L`, the centre of `L` is the centre of `N`
restricted to the faces of `L`. -/
theorem Sub.choice_eq_of_mem {L N : MonomialState} (h : Sub L N) {r : ℕ} {P : Finset ℕ}
    (hP : P ∈ N.choice r) (hPL : P ∈ L.nerve) :
    L.choice r = (N.choice r).filter (· ∈ L.nerve) := by
  obtain ⟨hPf, hPm, hPmax, hPlex⟩ := N.mem_choice.mp hP
  have hPfL : P ∈ L.faces r := L.mem_faces.mpr ⟨hPL, (N.mem_faces.mp hPf).2⟩
  ext T
  rw [Finset.mem_filter, L.mem_choice, N.mem_choice]
  constructor
  · rintro ⟨hTf, hTm, hTmax, hTlex⟩
    have hTN : T ∈ N.faces r := h.mem_faces hTf
    have hTL : T ∈ L.nerve := (L.mem_faces.mp hTf).1
    have hPT : N.total P ≤ N.total T := by
      rw [← h.total_eq, ← h.total_eq]; exact hTmax P hPfL (h.m_eq ▸ (h.total_eq P).symm ▸ hPm)
    have hTP : N.total T ≤ N.total P := hPmax T hTN (h.m_eq ▸ h.total_eq T ▸ hTm)
    have hTeq : N.total T = N.total P := le_antisymm hTP hPT
    refine ⟨⟨hTN, h.m_eq ▸ h.total_eq T ▸ hTm, fun T' hT' hm => (hPmax T' hT' hm).trans hPT,
      fun T' hT' he => ?_⟩, hTL⟩
    have h1 : L.labelTuple T ≤ L.labelTuple P := hTlex P hPfL (by
      rw [h.total_eq, h.total_eq]; exact hTeq.symm)
    rw [h.labelTuple_eq, h.labelTuple_eq] at h1
    exact h1.trans (hPlex T' hT' (he.trans hTeq))
  · rintro ⟨⟨hTf, hTm, hTmax, hTlex⟩, hTL⟩
    refine ⟨L.mem_faces.mpr ⟨hTL, (N.mem_faces.mp hTf).2⟩, ?_, fun T' hT' hm => ?_,
      fun T' hT' he => ?_⟩
    · rw [h.m_eq, h.total_eq]; exact hTm
    · rw [h.total_eq, h.total_eq]
      exact hTmax T' (h.mem_faces hT') (by rw [← h.m_eq, ← h.total_eq]; exact hm)
    · rw [h.labelTuple_eq, h.labelTuple_eq]
      exact hTlex T' (h.mem_faces hT') (by rw [← h.total_eq, ← h.total_eq]; exact he)

/-- A blow-up along faces none of which is a face of `L` does not change the nerve of `L`: no face
of `L` contains such a face, and no new face is created. -/
theorem blowUp_nerve_of_forall_notMem (L : MonomialState) {S : Finset (Finset ℕ)}
    (hS0 : ∀ P ∈ S, P.Nonempty) (hS : ∀ P ∈ S, P ∉ L.nerve) : (L.blowUp S).nerve = L.nerve := by
  ext T
  rw [blowUp_nerve, mem_blowUpNerve]
  constructor
  · rintro (⟨h1, -⟩ | ⟨P, hP, T₁, -, h1, h3, rfl⟩)
    · exact h1
    · exact absurd (L.mem_nerve_of_subset h1 Finset.subset_union_right (hS0 P hP)) (hS P hP)
  · intro hT
    exact Or.inl ⟨hT, fun P hP hPT => hS P hP (L.mem_nerve_of_subset hT hPT (hS0 P hP))⟩

/-- `Sub` is preserved along a list of centres. -/
theorem Sub.foldl {L N : MonomialState} (h : Sub L N) (Ns : List (Finset (Finset ℕ))) :
    Sub (Ns.foldl MonomialState.blowUp L) (Ns.foldl MonomialState.blowUp N) := by
  induction Ns generalizing L N with
  | nil => exact h
  | cons S Ns ih => exact ih (h.blowUp S)

/-- The pulled-back run ends in a state `Sub` the final state of `N`. -/
theorem sub_foldl_step3 {L N : MonomialState} (h : Sub L N) :
    Sub ((step3 N).2.foldl MonomialState.blowUp L) (step3 N).1 := by
  rw [(step3_isRun N).fold]
  exact h.foldl _

end Hironaka.Monomial.MonomialState
