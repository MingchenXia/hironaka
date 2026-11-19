/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Monomial.Restrict
public import Hironaka.Resolution.Algebraic.Monomial.Restrict.Extend
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Refinement: the transport lemmas and the extension across a blow-up

The first clause of [Kol07, 34.1], commutation with smooth surjections, for the combinatorial
Step 3: along a refinement `Refines ρ Y L` (`Hironaka/Resolution/Algebraic/Monomial/Restrict.lean`;
`ρ` maps the components of `Y` onto those of `L` preserving labels and exponents, is injective on
every face of `Y`, and maps the faces of `Y` onto the faces of `L`) sums, sizes and label tuples of
faces are preserved (`Refines.total_image`, `card_image`, `labelTuple_image`) and faces lift
(`exists_lift_faces`), so Kollár's choice on `Y` is the `ρ`-preimage of the choice on `L`
(`Refines.choice_eq`) and the choice on `L` is the image of the choice on `Y`
(`Refines.choice_image`). Across a blow-up along a centre `S_Y` of `Y` and its image `S_L`
(with `S_Y` the full preimage of `S_L` among the faces of `Y`, as Kollár's choices are), `ρ`
extends by `c_{P_Y} ↦ c_{ρ(P_Y)}`, the same `extendComp` as for restriction
(`Hironaka/Resolution/Algebraic/Monomial/Restrict/Extend.lean`), and `Refines` persists
(`Refines.blowUp`): a face of `Y` survives iff its image does (the components of a face over a face
of the centre form a face of the centre), the new faces map onto the new faces of `L`, and every new
face of `L` lifts. Not in the sources. The induction along the phases is
`Hironaka/Resolution/Algebraic/Monomial/Restrict/RefinePhase.lean`.
-/

public section

namespace Hironaka.Monomial.MonomialState

open Finset

/-- The image of the part of `W` over `A` is `A`, when `A ⊆ ρ(W)`. -/
theorem image_filter_mem_image {ρ : ℕ → ℕ} {W A : Finset ℕ} (hA : A ⊆ W.image ρ) :
    (W.filter fun c => ρ c ∈ A).image ρ = A := by
  ext y
  constructor
  · intro hy
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hy
    exact (Finset.mem_filter.mp hc).2
  · intro hy
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp (hA hy)
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hw, hy⟩)

namespace Refines

variable {ρ : ℕ → ℕ} {Y L : MonomialState} (h : Refines ρ Y L)
include h

theorem card_image {T : Finset ℕ} (hT : T ∈ Y.nerve) : (T.image ρ).card = T.card :=
  Finset.card_image_of_injOn (h.injOn T hT)

theorem total_image {T : Finset ℕ} (hT : T ∈ Y.nerve) : L.total (T.image ρ) = Y.total T := by
  rw [total, total, Finset.sum_image (h.injOn T hT)]
  exact Finset.sum_congr rfl fun c hc => h.a_eq c (MonomialState.lt_nextComp_of_mem _ hT hc)

theorem labels_image {T : Finset ℕ} (hT : T ∈ Y.nerve) : L.labels (T.image ρ) = Y.labels T := by
  rw [labels, labels, Finset.image_image]
  exact Finset.image_congr fun c hc => h.label_eq c (MonomialState.lt_nextComp_of_mem _ hT hc)

theorem labelTuple_image {T : Finset ℕ} (hT : T ∈ Y.nerve) :
    L.labelTuple (T.image ρ) = Y.labelTuple T := by
  rw [labelTuple, labelTuple, h.labels_image hT]

theorem image_mem_faces {r : ℕ} {T : Finset ℕ} (hT : T ∈ Y.faces r) : T.image ρ ∈ L.faces r := by
  obtain ⟨hT, hc⟩ := Y.mem_faces.mp hT
  exact L.mem_faces.mpr ⟨h.image_mem T hT, (h.card_image hT).trans hc⟩

theorem exists_lift_faces {r : ℕ} {T' : Finset ℕ} (hT' : T' ∈ L.faces r) :
    ∃ T ∈ Y.faces r, T.image ρ = T' := by
  obtain ⟨hT', hc⟩ := L.mem_faces.mp hT'
  obtain ⟨T, hT, rfl⟩ := h.exists_lift T' hT'
  exact ⟨T, Y.mem_faces.mpr ⟨hT, (h.card_image hT).symm.trans hc⟩, rfl⟩

theorem star_iff (s : ℕ) : L.Star s ↔ Y.Star s := by
  constructor
  · intro hs T hT
    have := hs _ (h.image_mem_faces hT)
    rwa [h.total_image (Y.mem_faces.mp hT).1, ← h.m_eq] at this
  · intro hs T' hT'
    obtain ⟨T, hT, rfl⟩ := h.exists_lift_faces hT'
    rw [h.total_image (Y.mem_faces.mp hT).1, ← h.m_eq]
    exact hs T hT

/-- Kollár's choice on `Y` is the `ρ`-preimage of the choice on `L`. -/
theorem choice_eq (r : ℕ) : Y.choice r = Y.nerve.filter fun Q => Q.image ρ ∈ L.choice r := by
  ext Q
  rw [Finset.mem_filter, Y.mem_choice, L.mem_choice]
  constructor
  · rintro ⟨hf, hm, hmax, hlex⟩
    have hQ : Q ∈ Y.nerve := (Y.mem_faces.mp hf).1
    refine ⟨hQ, h.image_mem_faces hf, ?_, fun T' hT' hm' => ?_, fun T' hT' he => ?_⟩
    · rw [h.total_image hQ, ← h.m_eq]; exact hm
    · obtain ⟨T, hT, rfl⟩ := h.exists_lift_faces hT'
      have hTn : T ∈ Y.nerve := (Y.mem_faces.mp hT).1
      rw [h.total_image hTn, h.total_image hQ]
      exact hmax T hT (by rwa [h.total_image hTn, ← h.m_eq] at hm')
    · obtain ⟨T, hT, rfl⟩ := h.exists_lift_faces hT'
      have hTn : T ∈ Y.nerve := (Y.mem_faces.mp hT).1
      rw [h.labelTuple_image hQ, h.labelTuple_image hTn]
      exact hlex T hT (by rwa [h.total_image hTn, h.total_image hQ] at he)
  · rintro ⟨hQ, hf, hm, hmax, hlex⟩
    have hQf : Q ∈ Y.faces r := Y.mem_faces.mpr ⟨hQ, by
      have := (L.mem_faces.mp hf).2; rwa [h.card_image hQ] at this⟩
    refine ⟨hQf, ?_, fun T hT hm' => ?_, fun T hT he => ?_⟩
    · rwa [h.total_image hQ, ← h.m_eq] at hm
    · have hTn : T ∈ Y.nerve := (Y.mem_faces.mp hT).1
      have := hmax (T.image ρ) (h.image_mem_faces hT)
        (by rw [h.total_image hTn, ← h.m_eq]; exact hm')
      rwa [h.total_image hTn, h.total_image hQ] at this
    · have hTn : T ∈ Y.nerve := (Y.mem_faces.mp hT).1
      have := hlex (T.image ρ) (h.image_mem_faces hT)
        (by rw [h.total_image hTn, h.total_image hQ]; exact he)
      rwa [h.labelTuple_image hQ, h.labelTuple_image hTn] at this

/-- The choice on `L` is the image of the choice on `Y`. -/
theorem choice_image (r : ℕ) : L.choice r = (Y.choice r).image (Finset.image ρ) := by
  ext T'
  rw [Finset.mem_image]
  constructor
  · intro hT'
    obtain ⟨T, hT, rfl⟩ := h.exists_lift T' (L.mem_nerve_of_mem_choice hT')
    exact ⟨T, by rw [h.choice_eq]; exact Finset.mem_filter.mpr ⟨hT, hT'⟩, rfl⟩
  · rintro ⟨T, hT, rfl⟩
    rw [h.choice_eq] at hT
    exact (Finset.mem_filter.mp hT).2

theorem choice_nonempty_iff (r : ℕ) : (Y.choice r).Nonempty ↔ (L.choice r).Nonempty := by
  rw [h.choice_image, Finset.image_nonempty]

/-! ### The extension across a blow-up -/

section Extend

variable {S_Y S_L : Finset (Finset ℕ)} (hSY : S_Y ⊆ Y.nerve)
  (hSL : S_L = S_Y.image (Finset.image ρ)) (hpre : ∀ Q ∈ Y.nerve, Q.image ρ ∈ S_L → Q ∈ S_Y)

omit h in
theorem image_mem_center' (hSL : S_L = S_Y.image (Finset.image ρ)) {Q : Finset ℕ} (hQ : Q ∈ S_Y) :
    Q.image ρ ∈ S_L := by
  rw [hSL]; exact Finset.mem_image_of_mem _ hQ

omit h in
theorem exists_of_mem_center' (hSL : S_L = S_Y.image (Finset.image ρ)) {Q' : Finset ℕ}
    (hQ' : Q' ∈ S_L) : ∃ Q ∈ S_Y, Q.image ρ = Q' := by
  rw [hSL] at hQ'; exact Finset.mem_image.mp hQ'

omit h in
theorem nonempty_of_mem_center' (hSY : S_Y ⊆ Y.nerve) (hSL : S_L = S_Y.image (Finset.image ρ))
    {Q' : Finset ℕ} (hQ' : Q' ∈ S_L) : Q'.Nonempty := by
  obtain ⟨Q, hQ, rfl⟩ := exists_of_mem_center' hSL hQ'
  exact (Y.nerve_nonempty Q (hSY hQ)).image _

omit h in
include hSY hSL hpre in
/-- No face of `S_L` lies inside the image of a face `T` of `Y` containing no face of `S_Y`: the
components of `T` over such a face would form a face of `S_Y` inside `T`. -/
theorem not_subset_image_of_forall {T : Finset ℕ} (hT : T ∈ Y.nerve)
    (hTS : ∀ Q ∈ S_Y, ¬ Q ⊆ T) : ∀ Q' ∈ S_L, ¬ Q' ⊆ T.image ρ := fun Q' hQ' hQ'T => by
  have hQ'ne : Q'.Nonempty := nonempty_of_mem_center' hSY hSL hQ'
  have hfil : (T.filter fun c => ρ c ∈ Q').image ρ = Q' := image_filter_mem_image hQ'T
  have hne : (T.filter fun c => ρ c ∈ Q').Nonempty := by
    rw [← Finset.image_nonempty (f := ρ), hfil]; exact hQ'ne
  have hmem : (T.filter fun c => ρ c ∈ Q') ∈ Y.nerve :=
    Y.mem_nerve_of_subset hT (Finset.filter_subset _ _) hne
  exact hTS _ (hpre _ hmem (by rw [hfil]; exact hQ')) (Finset.filter_subset _ _)

include hSY hSL hpre in
/-- `Refines` extends across a blow-up along `S_Y` and its image `S_L`. -/
theorem blowUp : Refines (extendComp ρ Y L S_Y S_L) (Y.blowUp S_Y) (L.blowUp S_L) where
  n_eq := by rw [blowUp_n, blowUp_n, h.n_eq]
  m_eq := by rw [blowUp_m, blowUp_m, h.m_eq]
  nextLabel_eq := by rw [blowUp_nextLabel, blowUp_nextLabel, h.nextLabel_eq]
  lt c hc := by
    rw [blowUp_nextComp] at hc ⊢
    rcases lt_or_exists_newComp Y S_Y hc with hc' | ⟨Q, hQ, rfl⟩
    · rw [extendComp_of_lt ρ Y L S_Y S_L hc']
      exact (h.lt c hc').trans_le (Nat.le_add_right _ _)
    · rw [extendComp_newComp ρ Y L S_Y S_L hQ]
      exact L.newComp_lt (image_mem_center' hSL hQ)
  label_eq c hc := by
    rw [blowUp_nextComp] at hc
    rcases lt_or_exists_newComp Y S_Y hc with hc' | ⟨Q, hQ, rfl⟩
    · rw [extendComp_of_lt ρ Y L S_Y S_L hc', L.blowUp_label_of_lt S_L (h.lt c hc'),
        Y.blowUp_label_of_lt S_Y hc', h.label_eq c hc']
    · rw [extendComp_newComp ρ Y L S_Y S_L hQ, L.blowUp_label_newComp, Y.blowUp_label_newComp,
        h.nextLabel_eq]
  a_eq c hc := by
    rw [blowUp_nextComp] at hc
    rcases lt_or_exists_newComp Y S_Y hc with hc' | ⟨Q, hQ, rfl⟩
    · rw [extendComp_of_lt ρ Y L S_Y S_L hc', L.blowUp_a_of_lt S_L (h.lt c hc'),
        Y.blowUp_a_of_lt S_Y hc', h.a_eq c hc']
    · rw [extendComp_newComp ρ Y L S_Y S_L hQ, L.blowUp_a_newComp S_L (image_mem_center' hSL hQ),
        Y.blowUp_a_newComp S_Y hQ, h.total_image (hSY hQ), h.m_eq]
  injOn T hT := by
    rw [Y.blowUp_nerve] at hT
    rcases mem_blowUpNerve.mp hT with ⟨h1, -⟩ | ⟨Q, hQ, T₁, -, h2, -, rfl⟩
    · exact (h.injOn T h1).congr fun c hc =>
        (extendComp_of_lt ρ Y L S_Y S_L (MonomialState.lt_nextComp_of_mem _ h1 hc)).symm
    · have hT₁c : ∀ c ∈ T₁, c < Y.nextComp := fun c hc =>
        MonomialState.lt_nextComp_of_mem _ h2 (Finset.mem_union_left _ hc)
      have hnew : ¬ Y.newComp S_Y Q < Y.nextComp := not_lt.mpr (Y.nextComp_le_newComp S_Y Q)
      intro x hx y hy hxy
      rcases Finset.mem_insert.mp hx with rfl | hx <;> rcases Finset.mem_insert.mp hy with rfl | hy
      · rfl
      · rw [extendComp_newComp ρ Y L S_Y S_L hQ, extendComp_of_lt ρ Y L S_Y S_L (hT₁c y hy)] at hxy
        exact absurd hxy (ne_of_gt ((h.lt y (hT₁c y hy)).trans_le (L.nextComp_le_newComp _ _)))
      · rw [extendComp_of_lt ρ Y L S_Y S_L (hT₁c x hx), extendComp_newComp ρ Y L S_Y S_L hQ] at hxy
        exact absurd hxy (ne_of_lt ((h.lt x (hT₁c x hx)).trans_le (L.nextComp_le_newComp _ _)))
      · rw [extendComp_of_lt ρ Y L S_Y S_L (hT₁c x hx),
          extendComp_of_lt ρ Y L S_Y S_L (hT₁c y hy)] at hxy
        exact h.injOn _ h2 (Finset.mem_union_left _ hx) (Finset.mem_union_left _ hy) hxy
  image_mem T hT := by
    rw [Y.blowUp_nerve] at hT
    rw [L.blowUp_nerve]
    rcases mem_blowUpNerve.mp hT with ⟨h1, h2⟩ | ⟨Q, hQ, T₁, h1, h2, h3, rfl⟩
    · rw [image_extendComp_of_lt ρ Y L S_Y S_L
        (fun _ hc => MonomialState.lt_nextComp_of_mem _ h1 hc)]
      exact mem_blowUpNerve.mpr (Or.inl ⟨h.image_mem T h1,
        not_subset_image_of_forall hSY hSL hpre h1 h2⟩)
    · have hT₁c : ∀ c ∈ T₁, c < Y.nextComp := fun c hc =>
        MonomialState.lt_nextComp_of_mem _ h2 (Finset.mem_union_left _ hc)
      rw [Finset.image_insert, extendComp_newComp ρ Y L S_Y S_L hQ,
        image_extendComp_of_lt ρ Y L S_Y S_L hT₁c]
      refine mem_blowUpNerve.mpr (Or.inr ⟨Q.image ρ, image_mem_center' hSL hQ, T₁.image ρ, ?_, ?_,
        fun Q' hQ' hQ'T => ?_, rfl⟩)
      · rcases h1 with h1 | h1
        · exact Or.inl (by rw [h1, Finset.image_empty])
        · exact Or.inr (h.image_mem T₁ h1)
      · rw [← Finset.image_union]; exact h.image_mem _ h2
      · have hQ'ne : Q'.Nonempty := nonempty_of_mem_center' hSY hSL hQ'
        have hfil : (T₁.filter fun c => ρ c ∈ Q').image ρ = Q' := image_filter_mem_image hQ'T
        have hne : (T₁.filter fun c => ρ c ∈ Q').Nonempty := by
          rw [← Finset.image_nonempty (f := ρ), hfil]; exact hQ'ne
        have hmem : (T₁.filter fun c => ρ c ∈ Q') ∈ Y.nerve :=
          Y.mem_nerve_of_subset h2 ((Finset.filter_subset _ _).trans Finset.subset_union_left) hne
        exact h3 _ (hpre _ hmem (by rw [hfil]; exact hQ')) (Finset.filter_subset _ _)
  exists_lift T' hT' := by
    rw [L.blowUp_nerve] at hT'
    rcases mem_blowUpNerve.mp hT' with ⟨h1, h2⟩ | ⟨Q', hQ', T₁', h1, h2, h3, rfl⟩
    · obtain ⟨T, hT, rfl⟩ := h.exists_lift T' h1
      refine ⟨T, ?_,
        image_extendComp_of_lt ρ Y L S_Y S_L (fun _ hc => MonomialState.lt_nextComp_of_mem _ hT hc)⟩
      rw [Y.blowUp_nerve]
      exact mem_blowUpNerve.mpr (Or.inl ⟨hT, fun Q hQ hQT =>
        h2 (Q.image ρ) (image_mem_center' hSL hQ) (Finset.image_subset_image hQT)⟩)
    · obtain ⟨W, hW, hWe⟩ := h.exists_lift _ h2
      have hQ'ne : Q'.Nonempty := nonempty_of_mem_center' hSY hSL hQ'
      have hQe : (W.filter fun c => ρ c ∈ Q').image ρ = Q' :=
        image_filter_mem_image (hWe ▸ Finset.subset_union_right)
      have hT₁e : (W.filter fun c => ρ c ∈ T₁').image ρ = T₁' :=
        image_filter_mem_image (hWe ▸ Finset.subset_union_left)
      have hQne : (W.filter fun c => ρ c ∈ Q').Nonempty := by
        rw [← Finset.image_nonempty (f := ρ), hQe]; exact hQ'ne
      have hQmem : (W.filter fun c => ρ c ∈ Q') ∈ Y.nerve :=
        Y.mem_nerve_of_subset hW (Finset.filter_subset _ _) hQne
      have hQS : (W.filter fun c => ρ c ∈ Q') ∈ S_Y := hpre _ hQmem (by rw [hQe]; exact hQ')
      have hunion : (W.filter fun c => ρ c ∈ T₁') ∪ (W.filter fun c => ρ c ∈ Q') ∈ Y.nerve :=
        Y.mem_nerve_of_subset hW (Finset.union_subset (Finset.filter_subset _ _)
          (Finset.filter_subset _ _)) (hQne.mono Finset.subset_union_right)
      have hT₁c : ∀ c ∈ (W.filter fun c => ρ c ∈ T₁'), c < Y.nextComp := fun c hc =>
        MonomialState.lt_nextComp_of_mem _ hW (Finset.mem_filter.mp hc).1
      refine ⟨insert (Y.newComp S_Y (W.filter fun c => ρ c ∈ Q')) (W.filter fun c => ρ c ∈ T₁'),
        ?_, ?_⟩
      · rw [Y.blowUp_nerve]
        refine mem_blowUpNerve.mpr (Or.inr ⟨_, hQS, _, ?_, hunion, fun Q hQ hQT => ?_, rfl⟩)
        · by_cases he : (W.filter fun c => ρ c ∈ T₁') = ∅
          · exact Or.inl he
          · exact Or.inr (Y.mem_nerve_of_subset hW (Finset.filter_subset _ _)
              (Finset.nonempty_iff_ne_empty.mpr he))
        · exact h3 (Q.image ρ) (image_mem_center' hSL hQ)
            (hT₁e ▸ Finset.image_subset_image hQT)
      · rw [Finset.image_insert, extendComp_newComp ρ Y L S_Y S_L hQS,
          image_extendComp_of_lt ρ Y L S_Y S_L hT₁c, hQe, hT₁e]

end Extend

end Refines

end Hironaka.Monomial.MonomialState
