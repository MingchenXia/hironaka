/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Monomial.State
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.Sort

/-!
# Renumbering components and labels

The direct run of Kollár's Step 3 on a subnerve and the pulled-back run of
`Hironaka/Resolution/Algebraic/Monomial/Restrict.lean` allocate components and labels differently
(the empty blow-ups of the pulled-back run still allocate), so the two are compared through an
order-preserving renumbering. `Rel ρ σ D P` says that the state `P` (the pulled-back one) is the
state `D` (the direct one) with components renamed by `ρ` and labels by `σ`, both strictly
monotone on the allocated ranges; the faces of `P` are exactly the images of the faces of `D`,
with the same exponents and renamed labels, and `P` may have further dead components and unused
labels. Everything Kollár's choice looks at is transported: face sizes and sums
(`Rel.total_image`), label tuples (`Rel.labelTuple_image`, through `sortedList_image`: the
increasing enumeration commutes with a strictly monotone map, and `map_lt_map_iff`: so does the
lexicographic order), hence the faces of a size, `(∗_s)` and the choice itself (`Rel.choice_eq`).
Not in the sources; this is the bookkeeping behind the reindexing of [Kol07, 34.1]. The
relation is extended across a blow-up in
`Hironaka/Resolution/Algebraic/Monomial/Restrict/Extend.lean`, and the real-analytic strand states
its own refinement relation with it
(`Hironaka/Resolution/Analytic/OrderReduction/BMO/Step3Monomial/RefinesAlong.lean`).
-/

@[expose] public section

namespace Hironaka.Monomial.MonomialState

open Finset

/-! ### Sorted lists and the lexicographic order under strictly monotone maps -/

/-- The increasing enumeration of the image under a map strictly monotone on the set is the
mapped enumeration. -/
theorem sortedList_image {s : Finset ℕ} {f : ℕ → ℕ} (hf : StrictMonoOn f s) :
    sortedList (s.image f) = (sortedList s).map f := by
  have h1 : ((sortedList s).map f).Pairwise (· < ·) :=
    List.pairwise_map.mpr ((sortedList_pairwise s).imp_of_mem fun ha hb h =>
      hf (mem_sortedList.mp ha) (mem_sortedList.mp hb) h)
  have h2 := sortedList_pairwise (s.image f)
  have hperm : List.Perm (sortedList (s.image f)) ((sortedList s).map f) := by
    apply List.perm_of_nodup_nodup_toFinset_eq (h2.imp ne_of_lt) (h1.imp ne_of_lt)
    ext x
    simp only [List.mem_toFinset, mem_sortedList, List.mem_map, Finset.mem_image]
  exact hperm.eq_of_sortedLE (List.sortedLE_iff_pairwise.mpr (h2.imp le_of_lt))
    (List.sortedLE_iff_pairwise.mpr (h1.imp le_of_lt))

theorem lex_cons_cons_iff {a b : ℕ} {l l' : List ℕ} :
    List.Lex (· < ·) (a :: l) (b :: l') ↔ a < b ∨ (a = b ∧ List.Lex (· < ·) l l') := by
  constructor
  · intro h
    cases h with
    | cons h => exact Or.inr ⟨rfl, h⟩
    | rel h => exact Or.inl h
  · rintro (h | ⟨rfl, h⟩)
    · exact List.Lex.rel h
    · exact List.Lex.cons h

/-- The lexicographic order of lists is preserved by a map strictly monotone on their
elements. -/
theorem lex_map_iff {f : ℕ → ℕ} {A : Set ℕ} (hf : StrictMonoOn f A) :
    ∀ {l l' : List ℕ}, (∀ x ∈ l, x ∈ A) → (∀ x ∈ l', x ∈ A) →
      (List.Lex (· < ·) (l.map f) (l'.map f) ↔ List.Lex (· < ·) l l')
  | [], [], _, _ => ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
  | [], _ :: _, _, _ => ⟨fun _ => List.Lex.nil, fun _ => List.Lex.nil⟩
  | _ :: _, [], _, _ => ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
  | a :: l, b :: l', hl, hl' => by
    simp only [List.map_cons, lex_cons_cons_iff]
    have ha : a ∈ A := hl a (List.mem_cons_self ..)
    have hb : b ∈ A := hl' b (List.mem_cons_self ..)
    rw [hf.lt_iff_lt ha hb, hf.injOn.eq_iff ha hb,
      lex_map_iff hf (fun x hx => hl x (List.mem_cons_of_mem _ hx))
        (fun x hx => hl' x (List.mem_cons_of_mem _ hx))]

theorem map_lt_map_iff {f : ℕ → ℕ} {A : Set ℕ} (hf : StrictMonoOn f A) {l l' : List ℕ}
    (hl : ∀ x ∈ l, x ∈ A) (hl' : ∀ x ∈ l', x ∈ A) : l.map f < l'.map f ↔ l < l' :=
  lex_map_iff hf hl hl'

theorem map_le_map_iff {f : ℕ → ℕ} {A : Set ℕ} (hf : StrictMonoOn f A) {l l' : List ℕ}
    (hl : ∀ x ∈ l, x ∈ A) (hl' : ∀ x ∈ l', x ∈ A) : l.map f ≤ l'.map f ↔ l ≤ l' := by
  rw [← not_lt, ← not_lt, map_lt_map_iff hf hl' hl]

/-! ### The renumbering relation -/

/-- `Rel ρ σ D P`: the state `P` is the state `D` with components renamed by `ρ` and labels by
`σ` (both strictly monotone on the allocated ranges, landing below `P`'s counters): the same
dimension bound and mark, the exponents and (renamed) labels of `D`'s components, and the faces
of `P` exactly the images of the faces of `D`. `P` may carry further dead components and unused
labels. -/
structure Rel (ρ σ : ℕ → ℕ) (D P : MonomialState) : Prop where
  n_eq : D.n = P.n
  m_eq : D.m = P.m
  mono : StrictMonoOn ρ (Set.Iio D.nextComp)
  lt : ∀ c, c < D.nextComp → ρ c < P.nextComp
  a_eq : ∀ c, c < D.nextComp → P.a (ρ c) = D.a c
  label_eq : ∀ c, c < D.nextComp → P.label (ρ c) = σ (D.label c)
  σmono : StrictMonoOn σ (Set.Iio D.nextLabel)
  σlt : ∀ ℓ, ℓ < D.nextLabel → σ ℓ < P.nextLabel
  nerve_eq : P.nerve = D.nerve.image (Finset.image ρ)

namespace Rel

theorem refl (D : MonomialState) : Rel id id D D where
  n_eq := rfl
  m_eq := rfl
  mono := strictMono_id.strictMonoOn _
  lt _ hc := hc
  a_eq _ _ := rfl
  label_eq _ _ := rfl
  σmono := strictMono_id.strictMonoOn _
  σlt _ hℓ := hℓ
  nerve_eq := by
    rw [show Finset.image (id : ℕ → ℕ) = id from funext fun T => Finset.image_id, Finset.image_id]

variable {ρ σ : ℕ → ℕ} {D P : MonomialState} (h : Rel ρ σ D P)
include h

theorem injOn_of_subset {T : Finset ℕ} (hT : ∀ c ∈ T, c < D.nextComp) : Set.InjOn ρ T :=
  h.mono.injOn.mono hT

theorem injOn_face {T : Finset ℕ} (hT : T ∈ D.nerve) : Set.InjOn ρ T :=
  h.injOn_of_subset fun _ hc => D.lt_nextComp_of_mem hT hc

theorem card_image {T : Finset ℕ} (hT : ∀ c ∈ T, c < D.nextComp) : (T.image ρ).card = T.card :=
  Finset.card_image_of_injOn (h.injOn_of_subset hT)

theorem total_image {T : Finset ℕ} (hT : ∀ c ∈ T, c < D.nextComp) :
    P.total (T.image ρ) = D.total T := by
  rw [total, total, Finset.sum_image (h.injOn_of_subset hT)]
  exact Finset.sum_congr rfl fun c hc => h.a_eq c (hT c hc)

theorem labels_image {T : Finset ℕ} (hT : ∀ c ∈ T, c < D.nextComp) :
    P.labels (T.image ρ) = (D.labels T).image σ := by
  rw [labels, labels, Finset.image_image, Finset.image_image]
  exact Finset.image_congr fun c hc => h.label_eq c (hT c hc)

omit h in
theorem labels_lt {T : Finset ℕ} (hT : ∀ c ∈ T, c < D.nextComp) :
    ∀ ℓ ∈ D.labels T, ℓ < D.nextLabel := fun ℓ hℓ => by
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hℓ
  exact D.label_lt c (hT c hc)

theorem labelTuple_image {T : Finset ℕ} (hT : ∀ c ∈ T, c < D.nextComp) :
    P.labelTuple (T.image ρ) = (D.labelTuple T).map σ := by
  rw [labelTuple, labelTuple, h.labels_image hT]
  exact sortedList_image fun ℓ hℓ ℓ' hℓ' hlt =>
    h.σmono (labels_lt hT ℓ hℓ) (labels_lt hT ℓ' hℓ') hlt

theorem labelTuple_le_iff {T T' : Finset ℕ} (hT : ∀ c ∈ T, c < D.nextComp)
    (hT' : ∀ c ∈ T', c < D.nextComp) :
    P.labelTuple (T.image ρ) ≤ P.labelTuple (T'.image ρ) ↔ D.labelTuple T ≤ D.labelTuple T' := by
  rw [h.labelTuple_image hT, h.labelTuple_image hT']
  exact map_le_map_iff h.σmono (fun ℓ hℓ => labels_lt hT ℓ (mem_sortedList.mp hℓ))
    (fun ℓ hℓ => labels_lt hT' ℓ (mem_sortedList.mp hℓ))

theorem image_mem_nerve {T : Finset ℕ} (hT : T ∈ D.nerve) : T.image ρ ∈ P.nerve := by
  rw [h.nerve_eq]; exact Finset.mem_image_of_mem _ hT

theorem exists_of_mem_nerve {T' : Finset ℕ} (hT' : T' ∈ P.nerve) :
    ∃ T ∈ D.nerve, T.image ρ = T' := by
  rw [h.nerve_eq] at hT'; exact Finset.mem_image.mp hT'

theorem image_mem_nerve_iff {T : Finset ℕ} (hT : ∀ c ∈ T, c < D.nextComp) :
    T.image ρ ∈ P.nerve ↔ T ∈ D.nerve := by
  refine ⟨fun hi => ?_, h.image_mem_nerve⟩
  obtain ⟨T₀, hT₀, he⟩ := h.exists_of_mem_nerve hi
  have h1 : (↑(T₀.image ρ) : Set ℕ) = ↑(T.image ρ) := by rw [he]
  rw [Finset.coe_image, Finset.coe_image] at h1
  have : T₀ = T := Finset.coe_inj.mp ((h.mono.injOn.image_eq_image_iff
    (fun _ hc => D.lt_nextComp_of_mem hT₀ hc) (fun c hc => hT c hc)).mp h1)
  exact this ▸ hT₀

theorem faces_eq (r : ℕ) : P.faces r = (D.faces r).image (Finset.image ρ) := by
  ext T'
  rw [Finset.mem_image, P.mem_faces]
  constructor
  · rintro ⟨hT', hc⟩
    obtain ⟨T, hT, rfl⟩ := h.exists_of_mem_nerve hT'
    refine ⟨T, D.mem_faces.mpr ⟨hT, ?_⟩, rfl⟩
    rwa [h.card_image fun _ hc => D.lt_nextComp_of_mem hT hc] at hc
  · rintro ⟨T, hT, rfl⟩
    obtain ⟨hT, hc⟩ := D.mem_faces.mp hT
    exact ⟨h.image_mem_nerve hT, hc ▸ h.card_image fun _ hc => D.lt_nextComp_of_mem hT hc⟩

theorem star_iff (s : ℕ) : P.Star s ↔ D.Star s := by
  constructor
  · intro hs T hT
    have := hs (T.image ρ) (by rw [h.faces_eq]; exact Finset.mem_image_of_mem _ hT)
    rwa [h.total_image fun _ hc => D.lt_nextComp_of_mem (D.mem_faces.mp hT).1 hc, ← h.m_eq] at this
  · intro hs T' hT'
    rw [h.faces_eq, Finset.mem_image] at hT'
    obtain ⟨T, hT, rfl⟩ := hT'
    rw [h.total_image fun _ hc => D.lt_nextComp_of_mem (D.mem_faces.mp hT).1 hc, ← h.m_eq]
    exact hs T hT

/-- Kollár's choice is transported by the renumbering. -/
theorem choice_eq (r : ℕ) : P.choice r = (D.choice r).image (Finset.image ρ) := by
  ext T'
  rw [Finset.mem_image]
  constructor
  · intro hT'
    obtain ⟨hf, hm, hmax, hlex⟩ := P.mem_choice.mp hT'
    rw [h.faces_eq, Finset.mem_image] at hf
    obtain ⟨T, hT, rfl⟩ := hf
    have hTc : ∀ c ∈ T, c < D.nextComp := fun c hc =>
      D.lt_nextComp_of_mem (D.mem_faces.mp hT).1 hc
    refine ⟨T, D.mem_choice.mpr ⟨hT, ?_, fun T₁ hT₁ hm₁ => ?_, fun T₁ hT₁ he => ?_⟩, rfl⟩
    · rwa [h.total_image hTc, ← h.m_eq] at hm
    · have hT₁c : ∀ c ∈ T₁, c < D.nextComp := fun c hc =>
        D.lt_nextComp_of_mem (D.mem_faces.mp hT₁).1 hc
      have := hmax (T₁.image ρ) (by rw [h.faces_eq]; exact Finset.mem_image_of_mem _ hT₁)
        (by rw [h.total_image hT₁c, ← h.m_eq]; exact hm₁)
      rwa [h.total_image hT₁c, h.total_image hTc] at this
    · have hT₁c : ∀ c ∈ T₁, c < D.nextComp := fun c hc =>
        D.lt_nextComp_of_mem (D.mem_faces.mp hT₁).1 hc
      have := hlex (T₁.image ρ) (by rw [h.faces_eq]; exact Finset.mem_image_of_mem _ hT₁)
        (by rw [h.total_image hT₁c, h.total_image hTc]; exact he)
      rwa [h.labelTuple_le_iff hTc hT₁c] at this
  · rintro ⟨T, hT, rfl⟩
    obtain ⟨hf, hm, hmax, hlex⟩ := D.mem_choice.mp hT
    have hTc : ∀ c ∈ T, c < D.nextComp := fun c hc =>
      D.lt_nextComp_of_mem (D.mem_faces.mp hf).1 hc
    refine P.mem_choice.mpr ⟨by rw [h.faces_eq]; exact Finset.mem_image_of_mem _ hf, ?_,
      fun T₁' hT₁' hm₁ => ?_, fun T₁' hT₁' he => ?_⟩
    · rw [h.total_image hTc, ← h.m_eq]; exact hm
    · rw [h.faces_eq, Finset.mem_image] at hT₁'
      obtain ⟨T₁, hT₁, rfl⟩ := hT₁'
      have hT₁c : ∀ c ∈ T₁, c < D.nextComp := fun c hc =>
        D.lt_nextComp_of_mem (D.mem_faces.mp hT₁).1 hc
      rw [h.total_image hT₁c, h.total_image hTc]
      exact hmax T₁ hT₁ (by rwa [h.total_image hT₁c, ← h.m_eq] at hm₁)
    · rw [h.faces_eq, Finset.mem_image] at hT₁'
      obtain ⟨T₁, hT₁, rfl⟩ := hT₁'
      have hT₁c : ∀ c ∈ T₁, c < D.nextComp := fun c hc =>
        D.lt_nextComp_of_mem (D.mem_faces.mp hT₁).1 hc
      rw [h.labelTuple_le_iff hTc hT₁c]
      exact hlex T₁ hT₁ (by rwa [h.total_image hT₁c, h.total_image hTc] at he)

theorem choice_eq_empty_iff (r : ℕ) : P.choice r = ∅ ↔ D.choice r = ∅ := by
  rw [h.choice_eq, Finset.image_eq_empty]

end Rel

end Hironaka.Monomial.MonomialState
