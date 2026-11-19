/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.SncGlobalSubfamily
public import Hironaka.Scheme.BlowUpSequence.EraseEmptyConcat
public import Hironaka.Scheme.BlowUpSequence.PullbackEraseEmpty
public import Mathlib.Data.Fintype.Sort
import Hironaka.Resolution.Algebraic.Kol07.AppendLast
import Hironaka.Resolution.Algebraic.Kol07.EraseEmptyInduced
import Hironaka.Resolution.Algebraic.Kol07.TotalTransformPositions
import Hironaka.Scheme.BlowUpSequence.Functoriality
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The boundary of an erased sequence embeds into the boundary of the sequence

The empty blow-up convention [Kol07, 32] deletes the empty blow-ups, and the second clause of
functoriality for smooth morphisms [Kol07, 34.1] reindexes. Here the total transform appends one
member per blow-up, the member appended by an empty blow-up being the unit ideal
(`exceptionalDivisor_top`); so the boundary induced at the end of `S.eraseEmpty` has fewer
members than the inverse image, along `eraseEmptyLastHom`, of the boundary induced at the end of
`S`: it embeds order-preservingly into it, matching members, with the unit ideal at every index
outside the range, a **deletion of `⊤` members** (`IsTopErasure`), which is the relation behind
`IndifferentToEmptyMembers` (`Hironaka/Resolution/Algebraic/OrderReduction/EmptyIndifferent.lean`),
and the embedding carries the transforms of the original members to the transforms of the original
members (`originalIdx`). The boundary is a divisor with ordered index set as in [Kol07, Definition
31].

* `IsTopErasure E' E e`: `E'` is `E` with `⊤` members deleted along the order embedding `e`;
  reflexive, transitive, preserved by `comap` and by the total transform (`sumLexMapEmb`, the lift
  of an embedding to the lexicographic sums that index total transforms).
* `exists_isTopErasure_totalTransformSeq`: a deletion of `⊤` members of the starting family
  induces one between the families at the end of any sequence, compatible with `originalIdx`.
* `EraseEmbeds S' E' R F φ e₀`: the relation between the end data of two sequences along a
  morphism of last stages; `eraseEmbeds_eraseEmpty : EraseEmbeds S.eraseEmpty E S E
  S.eraseEmptyLastHom id` is the theorem, by induction on `S` with the pull-back
  (`EraseEmbeds.pullback`, along the trivial blow-up's `inv (blowUpπ X ⊤)`) and the extension of
  the target family by the empty exceptional member (`EraseEmbeds.extend`).
* `monoEquivOfFin_totalTransformSeq_of_lt`: the first `card E.ι` positions of the induced family
  are the transforms of the original members, in order.
* `exceptionalFamily_eraseEmpty_embeds`: the exceptional sub-family of the erased sequence is the
  exceptional sub-family of the sequence with `⊤` members deleted.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Scheme IdealSheafData BlowUpSequence

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-! ### Deletion of `⊤` members along an order embedding -/

/-- `E'` is `E` with `⊤` members deleted along the order embedding `e`: the members of `E'` are
the members of `E` at the indices in the range of `e`, and every index of `E` outside the range
carries the unit ideal [Kol07, 32]. -/
def IsTopErasure (E' E : DivisorFamily X) (e : E'.ι ↪o E.ι) : Prop :=
  (∀ i, E.component (e i) = E'.component i) ∧ ∀ b, b ∉ Set.range e → E.component b = ⊤

/-- A deletion of unit members is an extension by empty members (`ExtendsByEmpty`): the same
data, the order embedding forgotten to an injection. -/
theorem IsTopErasure.extendsByEmpty {E' E : DivisorFamily X} {e : E'.ι ↪o E.ι}
    (h : IsTopErasure E' E e) : ExtendsByEmpty E' E :=
  ⟨e, e.injective, h.1, h.2⟩

theorem IsTopErasure.refl (E : DivisorFamily X) :
    IsTopErasure E E (OrderIso.refl E.ι).toOrderEmbedding :=
  ⟨fun _ => rfl, fun b hb => (hb ⟨b, rfl⟩).elim⟩

theorem IsTopErasure.trans {E₁ E₂ E₃ : DivisorFamily X} {e₁ : E₁.ι ↪o E₂.ι} {e₂ : E₂.ι ↪o E₃.ι}
    (h₁ : IsTopErasure E₁ E₂ e₁) (h₂ : IsTopErasure E₂ E₃ e₂) :
    IsTopErasure E₁ E₃ (e₁.trans e₂) := by
  refine ⟨fun i => ?_, fun b hb => ?_⟩
  · change E₃.component (e₂ (e₁ i)) = E₁.component i
    rw [h₂.1, h₁.1]
  · by_cases hb₂ : b ∈ Set.range e₂
    · obtain ⟨c, rfl⟩ := hb₂
      rw [h₂.1]
      exact h₁.2 c fun ⟨a, ha⟩ => hb ⟨a, by change e₂ (e₁ a) = e₂ c; rw [ha]⟩
    · exact h₂.2 b hb₂

theorem IsTopErasure.comap {E' E : DivisorFamily X} {e : E'.ι ↪o E.ι} (h : IsTopErasure E' E e)
    (g : Y ⟶ X) : IsTopErasure (E'.comap g) (E.comap g) e := by
  refine ⟨fun i => ?_, fun b hb => ?_⟩
  · exact congrArg (fun J : X.IdealSheafData => J.comap g) (h.1 i)
  · exact (congrArg (fun J : X.IdealSheafData => J.comap g) (h.2 b hb)).trans
      (Scheme.IdealSheafData.comap_top _)

/-- The lift of an order embedding to the lexicographic sums with a common right summand
(`Sum.map e id`), the index sets of total transforms (`totalTransform`, `append`). -/
def sumLexMapEmb {α β γ : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder γ] (e : α ↪o β) :
    α ⊕ₗ γ ↪o β ⊕ₗ γ :=
  OrderEmbedding.ofMapLEIff (fun x => toLex (Sum.map e id (ofLex x))) (by
    intro x y
    obtain ⟨x, rfl⟩ := toLex.surjective x
    obtain ⟨y, rfl⟩ := toLex.surjective y
    rcases x with a | c <;> rcases y with b | d
    · simp only [ofLex_toLex, Sum.map_inl, Sum.Lex.inl_le_inl_iff, e.le_iff_le]
    · simp only [ofLex_toLex, Sum.map_inl, Sum.map_inr, Sum.Lex.inl_le_inr]
    · simp only [ofLex_toLex, Sum.map_inl, Sum.map_inr, Sum.Lex.not_inr_le_inl]
    · simp only [ofLex_toLex, Sum.map_inr, id_eq, Sum.Lex.inr_le_inr_iff])

theorem sumLexMapEmb_apply_inl {α β γ : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder γ]
    (e : α ↪o β) (a : α) : sumLexMapEmb (γ := γ) e (toLex (Sum.inl a)) = toLex (Sum.inl (e a)) :=
  rfl

theorem sumLexMapEmb_apply_inr {α β γ : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder γ]
    (e : α ↪o β) (c : γ) : sumLexMapEmb e (toLex (Sum.inr c)) = toLex (Sum.inr c) :=
  rfl

/-- Deletion of `⊤` members is preserved by the total transform: the strict transform of the unit
ideal is the unit ideal (`strictTransform_top_right`), the exceptional members match. -/
theorem IsTopErasure.totalTransform {E' E : DivisorFamily X} {e : E'.ι ↪o E.ι}
    (h : IsTopErasure E' E e) (D : X.IdealSheafData) :
    IsTopErasure (E'.totalTransform D) (E.totalTransform D) (sumLexMapEmb e) := by
  refine ⟨fun i => ?_, fun b hb => ?_⟩
  · obtain ⟨a, rfl⟩ := toLex.surjective i
    rcases a with a | u
    · change (E.component (e a)).strictTransform D = (E'.component a).strictTransform D
      rw [h.1]
    · rfl
  · obtain ⟨a, rfl⟩ := toLex.surjective b
    rcases a with b₀ | u
    · change (E.component b₀).strictTransform D = ⊤
      have hb₀ : b₀ ∉ Set.range e := fun ⟨a, ha⟩ =>
        hb ⟨toLex (Sum.inl a), (sumLexMapEmb_apply_inl e a).trans (congrArg _ (congrArg _ ha))⟩
      rw [h.2 b₀ hb₀, strictTransform_top_right]
    · exact (hb ⟨toLex (Sum.inr u), rfl⟩).elim

/-- A deletion of `⊤` members of the starting family induces one between the families at the end
of any sequence, carrying the transforms of the original members to the transforms of the
original members. -/
theorem exists_isTopErasure_totalTransformSeq :
    ∀ {X : Scheme.{u}} (S : BlowUpSequence X) (E' E : DivisorFamily X) (e : E'.ι ↪o E.ι)
      (_he : IsTopErasure E' E e),
      ∃ e' : (S.totalTransformSeq E' (Fin.last _)).ι ↪o (S.totalTransformSeq E (Fin.last _)).ι,
        IsTopErasure (S.totalTransformSeq E' (Fin.last _)) (S.totalTransformSeq E (Fin.last _)) e' ∧
        ∀ a, e' (S.originalIdx E' (Fin.last _) a) = S.originalIdx E (Fin.last _) (e a)
  | _, nil _, _, _, e, he => ⟨e, he, fun _ => rfl⟩
  | _, cons X D rest, E', E, e, he => by
    obtain ⟨e', h1, h2⟩ := exists_isTopErasure_totalTransformSeq rest (E'.totalTransform D)
      (E.totalTransform D) (sumLexMapEmb e) (he.totalTransform D)
    exact ⟨e', h1, fun a => h2 (toLex (Sum.inl a))⟩

/-! ### Casts along equalities of families, and `originalIdx` under pullback -/

/-- The order isomorphism of index sets induced by an equality of families. -/
def castι {F₁ F₂ : DivisorFamily X} (h : F₁ = F₂) : F₁.ι ≃o F₂.ι := by
  subst h
  exact OrderIso.refl _

theorem component_castι {F₁ F₂ : DivisorFamily X} (h : F₁ = F₂) (i : F₁.ι) :
    F₂.component (castι h i) = F₁.component i := by
  subst h
  rfl

theorem castι_eq_of_heq {F₁ F₂ : DivisorFamily X} (h : F₁ = F₂) {x : F₁.ι} {y : F₂.ι}
    (hxy : HEq x y) : castι h x = y := by
  subst h
  exact eq_of_heq hxy

theorem originalIdx_congr_heq (S : BlowUpSequence X) {F₁ F₂ : DivisorFamily X} (h : F₁ = F₂)
    (i : Fin (S.length + 1)) {a₁ : F₁.ι} {a₂ : F₂.ι} (ha : HEq a₁ a₂) :
    HEq (S.originalIdx F₁ i a₁) (S.originalIdx F₂ i a₂) := by
  subst h
  cases ha
  rfl

theorem originalIdx_eq_idx_heq (S : BlowUpSequence X) (E : DivisorFamily X)
    {i j : Fin (S.length + 1)} (h : i = j) (a : E.ι) :
    HEq (S.originalIdx E i a) (S.originalIdx E j a) := by
  cases h
  rfl

/-- `originalIdx` commutes with pull-back: the transform of an original member along the
pulled-back sequence is the transform along the sequence (the index sets agree definitionally;
the heterogeneous equality carries the equality of the families). -/
theorem originalIdx_pullback_heq : ∀ {X : Scheme.{u}} (S : BlowUpSequence X) {Y : Scheme.{u}}
    (g : Y ⟶ X) [Flat g] (E : DivisorFamily X) (j : ℕ) (hj : j < S.length + 1) (a : E.ι),
    HEq ((S.pullback g).originalIdx (E.comap g) (S.pullbackStageIdx g ⟨j, hj⟩) a)
      (S.originalIdx E ⟨j, hj⟩ a)
  | _, nil _, _, _, _, _, _, _, _ => HEq.rfl
  | _, cons _ _ _, _, _, _, _, 0, _, _ => HEq.rfl
  | _, cons X D rest, Y, g, _, E, j + 1, hj, a => by
    have hflat : Flat (Scheme.Hom.blowUpMap g D) := flat_blowUpMap g D
    have h1 := originalIdx_pullback_heq rest (Scheme.Hom.blowUpMap g D) (E.totalTransform D) j
      (Nat.lt_of_succ_lt_succ hj) (toLex (Sum.inl a))
    have h2 := originalIdx_congr_heq (rest.pullback (Scheme.Hom.blowUpMap g D))
      (totalTransform_comap_of_flat g D E)
      (rest.pullbackStageIdx (Scheme.Hom.blowUpMap g D) ⟨j, Nat.lt_of_succ_lt_succ hj⟩)
      (a₁ := toLex (Sum.inl a)) (a₂ := toLex (Sum.inl a)) HEq.rfl
    exact h2.trans h1

theorem originalIdx_pullback_last_heq (S : BlowUpSequence X) (g : Y ⟶ X) [Flat g]
    (E : DivisorFamily X) (a : E.ι) :
    HEq ((S.pullback g).originalIdx (E.comap g) (Fin.last _) a) (S.originalIdx E (Fin.last _) a) :=
  (originalIdx_eq_idx_heq (S.pullback g) (E.comap g) (pullbackStageIdx_last S g).symm a).trans
    (originalIdx_pullback_heq S g E S.length (Nat.lt_succ_self _) a)

/-! ### The relation between the end data of two sequences -/

/-- The end data of `S'` (with family `E'`) embed into the end data of `R` (with family `F`) along
`φ` and the map of original members `e₀`: an order embedding of the induced families matching the
members through the inverse image along `φ`, with the unit ideal at every index outside its range,
carrying the transforms of the original members of `E'` to those of `F` along `e₀`. -/
def EraseEmbeds {X' : Scheme.{u}} (S' : BlowUpSequence X') (E' : DivisorFamily X')
    (R : BlowUpSequence X) (F : DivisorFamily X)
    (φ : S'.stage (Fin.last _) ⟶ R.stage (Fin.last _)) (e₀ : E'.ι → F.ι) : Prop :=
  ∃ e : (S'.totalTransformSeq E' (Fin.last _)).ι ↪o (R.totalTransformSeq F (Fin.last _)).ι,
    (∀ i, ((R.totalTransformSeq F (Fin.last _)).component (e i)).comap φ =
      (S'.totalTransformSeq E' (Fin.last _)).component i) ∧
    (∀ b, b ∉ Set.range e → ((R.totalTransformSeq F (Fin.last _)).component b).comap φ = ⊤) ∧
    ∀ a, e (S'.originalIdx E' (Fin.last _) a) = R.originalIdx F (Fin.last _) (e₀ a)

theorem eraseEmbeds_nil (E : DivisorFamily X) : EraseEmbeds (nil X) E (nil X) E (𝟙 X) id :=
  ⟨(OrderIso.refl _).toOrderEmbedding, fun _ => Scheme.IdealSheafData.comap_id _,
    fun b hb => (hb ⟨b, rfl⟩).elim, fun _ => rfl⟩

theorem eraseEmbeds_congr_hom {X' : Scheme.{u}} {S' : BlowUpSequence X'} {E' : DivisorFamily X'}
    {R : BlowUpSequence X} {F : DivisorFamily X}
    {φ₁ φ₂ : S'.stage (Fin.last _) ⟶ R.stage (Fin.last _)} (h : φ₁ = φ₂) {e₀ : E'.ι → F.ι}
    (hh : EraseEmbeds S' E' R F φ₁ e₀) : EraseEmbeds S' E' R F φ₂ e₀ := by
  subst h
  exact hh

theorem castι_rfl_apply (F : DivisorFamily X) (a : F.ι) : castι (rfl : F = F) a = a := rfl

/-- Transport along an equality of source families. -/
theorem EraseEmbeds.of_family_eq {X' : Scheme.{u}} {S' : BlowUpSequence X'}
    {E₁ E₂ : DivisorFamily X'} (h : E₁ = E₂) {R : BlowUpSequence X} {F : DivisorFamily X}
    {φ : S'.stage (Fin.last _) ⟶ R.stage (Fin.last _)} {e₀ : E₁.ι → F.ι} (e₀' : E₂.ι → F.ι)
    (he : ∀ a, e₀ a = e₀' (castι h a)) (hh : EraseEmbeds S' E₁ R F φ e₀) :
    EraseEmbeds S' E₂ R F φ e₀' := by
  subst h
  obtain ⟨e, hc, ht, ho⟩ := hh
  exact ⟨e, hc, ht, fun a => (ho a).trans
    (congrArg _ ((he a).trans (congrArg e₀' (castι_rfl_apply _ a))))⟩

theorem eraseEmbeds_congr_left {X' : Scheme.{u}} {S₁ S₂ : BlowUpSequence X'} (h : S₁ = S₂)
    (E' : DivisorFamily X') (R : BlowUpSequence X) (F : DivisorFamily X)
    (φ : S₂.stage (Fin.last _) ⟶ R.stage (Fin.last _)) (e₀ : E'.ι → F.ι)
    (p : S₁.stage (Fin.last _) = S₂.stage (Fin.last _)) (hh : EraseEmbeds S₂ E' R F φ e₀) :
    EraseEmbeds S₁ E' R F (eqToHom p ≫ φ) e₀ := by
  subst h
  have : eqToHom p ≫ φ = φ := by rw [eqToHom_refl, Category.id_comp]
  rw [this]
  exact hh

/-- Peeling one blow-up on both sides. -/
theorem eraseEmbeds_cons {X' : Scheme.{u}} (D' : X'.IdealSheafData)
    (S' : BlowUpSequence D'.blowUp) (E' : DivisorFamily X') (D : X.IdealSheafData)
    (R : BlowUpSequence D.blowUp) (F : DivisorFamily X)
    (φ : S'.stage (Fin.last _) ⟶ R.stage (Fin.last _)) (e₀ : E'.ι → F.ι)
    (e₁ : (E'.totalTransform D').ι → (F.totalTransform D).ι)
    (he : ∀ a, e₁ (toLex (Sum.inl a)) = toLex (Sum.inl (e₀ a)))
    (h : EraseEmbeds S' (E'.totalTransform D') R (F.totalTransform D) φ e₁) :
    EraseEmbeds (cons X' D' S') E' (cons X D R) F φ e₀ := by
  obtain ⟨e, h1, h2, h3⟩ := h
  refine ⟨e, h1, h2, fun a => ?_⟩
  exact (h3 (toLex (Sum.inl a))).trans (congrArg _ (he a))

/-- Peeling one blow-up on the target side only. -/
theorem eraseEmbeds_cons_right {X' : Scheme.{u}} (S' : BlowUpSequence X') (E' : DivisorFamily X')
    (D : X.IdealSheafData) (R : BlowUpSequence D.blowUp) (F : DivisorFamily X)
    (φ : S'.stage (Fin.last _) ⟶ R.stage (Fin.last _)) (e₀ : E'.ι → F.ι)
    (e₁ : E'.ι → (F.totalTransform D).ι) (he : ∀ a, e₁ a = toLex (Sum.inl (e₀ a)))
    (h : EraseEmbeds S' E' R (F.totalTransform D) φ e₁) :
    EraseEmbeds S' E' (cons X D R) F φ e₀ := by
  obtain ⟨e, h1, h2, h3⟩ := h
  refine ⟨e, h1, h2, fun a => ?_⟩
  exact (h3 a).trans (congrArg _ (he a))

/-- Extending the target family by a deletion of `⊤` members. -/
theorem EraseEmbeds.extend {X' : Scheme.{u}} {S' : BlowUpSequence X'} {E' : DivisorFamily X'}
    {R : BlowUpSequence X} {F F' : DivisorFamily X}
    {φ : S'.stage (Fin.last _) ⟶ R.stage (Fin.last _)} {e₀ : E'.ι → F.ι}
    (h : EraseEmbeds S' E' R F φ e₀) {e₁ : F.ι ↪o F'.ι} (h₁ : IsTopErasure F F' e₁) :
    EraseEmbeds S' E' R F' φ (e₁ ∘ e₀) := by
  obtain ⟨e, hc, ht, ho⟩ := h
  obtain ⟨e₂, ⟨hc₂, ht₂⟩, ho₂⟩ := exists_isTopErasure_totalTransformSeq R F F' e₁ h₁
  refine ⟨e.trans e₂, fun i => ?_, fun b hb => ?_, fun a => ?_⟩
  · change ((R.totalTransformSeq F' (Fin.last _)).component (e₂ (e i))).comap φ = _
    rw [hc₂, hc]
  · by_cases hb₂ : b ∈ Set.range e₂
    · obtain ⟨c, rfl⟩ := hb₂
      rw [hc₂]
      exact ht c fun ⟨a, ha⟩ => hb ⟨a, by change e₂ (e a) = e₂ c; rw [ha]⟩
    · rw [ht₂ b hb₂, Scheme.IdealSheafData.comap_top]
  · change e₂ (e (S'.originalIdx E' (Fin.last _) a)) = _
    rw [ho, ho₂]
    rfl

/-- Pulling back the source sequence along a flat morphism. -/
theorem EraseEmbeds.pullback {X' : Scheme.{u}} {S' : BlowUpSequence X'} {E' : DivisorFamily X'}
    {R : BlowUpSequence X} {F : DivisorFamily X}
    {φ : S'.stage (Fin.last _) ⟶ R.stage (Fin.last _)} {e₀ : E'.ι → F.ι}
    (h : EraseEmbeds S' E' R F φ e₀) {Y' : Scheme.{u}} (g : Y' ⟶ X') [Flat g] :
    EraseEmbeds (S'.pullback g) (E'.comap g) R F (S'.pullbackLastHom g ≫ φ) e₀ := by
  obtain ⟨e, hc, ht, ho⟩ := h
  have hT : (S'.pullback g).totalTransformSeq (E'.comap g) (Fin.last _) =
      (S'.totalTransformSeq E' (Fin.last _)).comap (S'.pullbackLastHom g) := by
    rw [totalTransformSeq_eq_idx (S'.pullback g) (E'.comap g) (pullbackStageIdx_last S' g),
      totalTransformSeq_pullback]
    exact (DivisorFamily.comap_comp _ _ _).symm
  refine ⟨(castι hT).toOrderEmbedding.trans e, fun i => ?_, fun b hb => ?_, fun a => ?_⟩
  · exact (Scheme.IdealSheafData.comap_comp _ _ _).trans
      ((congrArg (fun J : (S'.stage (Fin.last _)).IdealSheafData =>
        J.comap (S'.pullbackLastHom g)) (hc (castι hT i))).trans (component_castι hT i))
  · have hb' : b ∉ Set.range e := fun ⟨c, hcb⟩ =>
      hb ⟨(castι hT).symm c, (congrArg e (OrderIso.apply_symm_apply (castι hT) c)).trans hcb⟩
    exact (Scheme.IdealSheafData.comap_comp _ _ _).trans
      ((congrArg (fun J : (S'.stage (Fin.last _)).IdealSheafData =>
        J.comap (S'.pullbackLastHom g)) (ht b hb')).trans (Scheme.IdealSheafData.comap_top _))
  · exact (congrArg e (castι_eq_of_heq hT (originalIdx_pullback_last_heq S' g E' a))).trans (ho a)

/-- The original members of `E`, embedded into the total transform of the trivial blow-up. -/
noncomputable def inlEmb (E : DivisorFamily X) (D : X.IdealSheafData) :
    (E.comap D.blowUpπ).ι ↪o (E.totalTransform D).ι :=
  OrderEmbedding.ofMapLEIff (fun a => toLex (Sum.inl a)) fun _ _ => Sum.Lex.inl_le_inl_iff

/-- Under the trivial blow-up, the inverse image of `E` is its total transform with the (empty)
exceptional member deleted (`strictTransform_top_left`, `exceptionalDivisor_top`). -/
theorem isTopErasure_inlEmb_top (E : DivisorFamily X) :
    IsTopErasure (E.comap (⊤ : X.IdealSheafData).blowUpπ) (E.totalTransform ⊤) (inlEmb E ⊤) := by
  refine ⟨fun i => ?_, fun b hb => ?_⟩
  · exact strictTransform_top_left _
  · obtain ⟨a, rfl⟩ := toLex.surjective b
    rcases a with a | u
    · exact (hb ⟨a, rfl⟩).elim
    · exact exceptionalDivisor_top

theorem isTopErasure_inlEmb_of_eq_top (E : DivisorFamily X) {D : X.IdealSheafData} (h : D = ⊤) :
    IsTopErasure (E.comap D.blowUpπ) (E.totalTransform D) (inlEmb E D) := by
  subst h
  exact isTopErasure_inlEmb_top E

/-- The trivial blow-up case of `eraseEmbeds_eraseEmpty`: the erased sequence is the erased tail
carried back along `inv (D.blowUpπ)` (`EraseEmbeds.pullback`), and the family of the sequence is
the inverse image of `E` extended by the empty exceptional member (`EraseEmbeds.extend` along
`isTopErasure_inlEmb_of_eq_top`). -/
theorem eraseEmbeds_eraseEmpty_cons_of_eq_top_aux₀ (D : X.IdealSheafData)
    (rest : BlowUpSequence D.blowUp) (E : DivisorFamily X) [IsIso
        D.blowUpπ]
    (ih : EraseEmbeds rest.eraseEmpty (E.comap D.blowUpπ) rest (E.comap
        D.blowUpπ)
      rest.eraseEmptyLastHom id) :
    EraseEmbeds (rest.eraseEmpty.pullback (inv D.blowUpπ))
      ((E.comap D.blowUpπ).comap (inv D.blowUpπ)) rest (E.comap
          D.blowUpπ)
      (rest.eraseEmpty.pullbackLastHom (inv D.blowUpπ) ≫ rest.eraseEmptyLastHom) id :=
  ih.pullback (inv D.blowUpπ)

/-- The transport of the source family (`(E.comap π).comap (inv π) = E`); the equality is a
hypothesis, not a local `have` — with the proof term in scope the kernel check does not
terminate. -/
theorem eraseEmbeds_eraseEmpty_cons_of_eq_top_aux₁ (D : X.IdealSheafData)
    (rest : BlowUpSequence D.blowUp) (E : DivisorFamily X) [IsIso
        D.blowUpπ]
    (hE : (E.comap D.blowUpπ).comap (inv D.blowUpπ) = E)
    (h1 : EraseEmbeds (rest.eraseEmpty.pullback (inv D.blowUpπ))
      ((E.comap D.blowUpπ).comap (inv D.blowUpπ)) rest (E.comap
          D.blowUpπ)
      (rest.eraseEmpty.pullbackLastHom (inv D.blowUpπ) ≫ rest.eraseEmptyLastHom) id) :
    EraseEmbeds (rest.eraseEmpty.pullback (inv D.blowUpπ)) E rest (E.comap
        D.blowUpπ)
      (rest.eraseEmpty.pullbackLastHom (inv D.blowUpπ) ≫ rest.eraseEmptyLastHom) id :=
          by
  have he : ∀ a : E.ι, (id : ((E.comap D.blowUpπ).comap (inv
      D.blowUpπ)).ι →
      (E.comap D.blowUpπ).ι) a = id (castι hE a) :=
    fun a => (castι_eq_of_heq hE HEq.rfl).symm
  exact EraseEmbeds.of_family_eq (F := E.comap D.blowUpπ) hE id he h1

theorem eraseEmbeds_eraseEmpty_cons_of_eq_top_aux₂ (D : X.IdealSheafData)
    (rest : BlowUpSequence D.blowUp) (E : DivisorFamily X) (h : D = ⊤)
    [IsIso D.blowUpπ]
    (h1 : EraseEmbeds (rest.eraseEmpty.pullback (inv D.blowUpπ)) E rest (E.comap
        D.blowUpπ)
      (rest.eraseEmpty.pullbackLastHom (inv D.blowUpπ) ≫ rest.eraseEmptyLastHom) id) :
    EraseEmbeds (rest.eraseEmpty.pullback (inv D.blowUpπ)) E (cons X D rest) E
      (rest.eraseEmpty.pullbackLastHom (inv D.blowUpπ) ≫ rest.eraseEmptyLastHom) id :=
          by
  have h2 := h1.extend (isTopErasure_inlEmb_of_eq_top E h)
  exact eraseEmbeds_cons_right _ E D rest E _ id _ (fun _ => rfl) h2

theorem eraseEmbeds_eraseEmpty_cons_of_eq_top (D : X.IdealSheafData)
    (rest : BlowUpSequence D.blowUp) (E : DivisorFamily X) (h : D = ⊤)
    (ih : EraseEmbeds rest.eraseEmpty (E.comap D.blowUpπ) rest (E.comap
        D.blowUpπ)
      rest.eraseEmptyLastHom id) :
    EraseEmbeds (cons X D rest).eraseEmpty E (cons X D rest) E (cons X D rest).eraseEmptyLastHom
      id := by
  have hiso : IsIso D.blowUpπ := isIso_blowUpπ_of_eq_top h
  have e := eraseEmpty_cons_of_eq_top rest h
  have h3 := eraseEmbeds_eraseEmpty_cons_of_eq_top_aux₂ D rest E h
    (eraseEmbeds_eraseEmpty_cons_of_eq_top_aux₁ D rest E
      (DivisorFamily.comap_comap_inv D.blowUpπ E)
      (eraseEmbeds_eraseEmpty_cons_of_eq_top_aux₀ D rest E ih))
  have h4 := eraseEmbeds_congr_left e E (cons X D rest) E _ id
    (congrArg (fun S : BlowUpSequence X => S.stage (Fin.last _)) e) h3
  exact eraseEmbeds_congr_hom (eraseEmptyLastHom_cons_of_eq_top D rest h).symm h4

/-- The nontrivial blow-up case of `eraseEmbeds_eraseEmpty`: peel the common first blow-up. -/
theorem eraseEmbeds_eraseEmpty_cons_of_ne_top (D : X.IdealSheafData)
    (rest : BlowUpSequence D.blowUp) (E : DivisorFamily X) (h : ¬ D = ⊤)
    (ih : EraseEmbeds rest.eraseEmpty (E.totalTransform D) rest (E.totalTransform D)
      rest.eraseEmptyLastHom id) :
    EraseEmbeds (cons X D rest).eraseEmpty E (cons X D rest) E (cons X D rest).eraseEmptyLastHom
      id := by
  have e := eraseEmpty_cons_of_ne_top rest h
  have h3 := eraseEmbeds_cons D rest.eraseEmpty E D rest E rest.eraseEmptyLastHom id id
    (fun _ => rfl) ih
  have h4 := eraseEmbeds_congr_left e E (cons X D rest) E _ id
    (congrArg (fun S : BlowUpSequence X => S.stage (Fin.last _)) e) h3
  exact eraseEmbeds_congr_hom (eraseEmptyLastHom_cons_of_ne_top D rest h).symm h4

/-- The boundary at the end of the erased sequence is the inverse image, along the last-stage
isomorphism, of the boundary at the end of the sequence with `⊤` members deleted, the transforms
of the original members carried to the transforms of the original members [Kol07, 32]. -/
theorem eraseEmbeds_eraseEmpty : ∀ {X : Scheme.{u}} (S : BlowUpSequence X) (E : DivisorFamily X),
    EraseEmbeds S.eraseEmpty E S E S.eraseEmptyLastHom id
  | _, nil X, E => eraseEmbeds_nil E
  | _, cons X D rest, E => by
    classical
    by_cases h : D = ⊤
    · exact eraseEmbeds_eraseEmpty_cons_of_eq_top D rest E h (eraseEmbeds_eraseEmpty rest _)
    · exact eraseEmbeds_eraseEmpty_cons_of_ne_top D rest E h (eraseEmbeds_eraseEmpty rest _)

/-! ### Positions of the original members; the exceptional sub-family -/

/-- The first `card E.ι` positions of the family induced at the end of a sequence are the
transforms of the original members, in the original order (`monoEquivOfFin_lex_inl`). -/
theorem monoEquivOfFin_totalTransformSeq_of_lt : ∀ {X : Scheme.{u}} (S : BlowUpSequence X)
    (E : DivisorFamily X) {j : ℕ} (hj : j < Fintype.card E.ι)
    (hj' : j < Fintype.card (S.totalTransformSeq E (Fin.last _)).ι),
    monoEquivOfFin (S.totalTransformSeq E (Fin.last _)).ι rfl ⟨j, hj'⟩ =
      S.originalIdx E (Fin.last _) (monoEquivOfFin E.ι rfl ⟨j, hj⟩)
  | _, nil _, _, _, _, _ => rfl
  | _, cons X D rest, E, j, hj, hj' => by
    have hj₁ : j < Fintype.card (E.totalTransform D).ι := by
      change j < Fintype.card (E.ι ⊕ₗ PUnit.{u + 1})
      rw [card_lex_punit]
      exact Nat.lt_succ_of_lt hj
    have ih := monoEquivOfFin_totalTransformSeq_of_lt rest (E.totalTransform D) hj₁ hj'
    change monoEquivOfFin (rest.totalTransformSeq (E.totalTransform D) (Fin.last _)).ι rfl ⟨j, hj'⟩
      =
      rest.originalIdx (E.totalTransform D) (Fin.last _)
        (toLex (Sum.inl (monoEquivOfFin E.ι rfl ⟨j, hj⟩)))
    rw [ih]
    exact congrArg _ (monoEquivOfFin_lex_inl hj hj₁)

/-- The exceptional sub-family of the erased sequence is the inverse image of the exceptional
sub-family of the sequence with `⊤` members deleted. -/
theorem exceptionalFamily_eraseEmpty_embeds (S : BlowUpSequence X) (E : DivisorFamily X) :
    ∃ e : (S.eraseEmpty.exceptionalFamily E).ι ↪o (S.exceptionalFamily E).ι,
      IsTopErasure (S.eraseEmpty.exceptionalFamily E)
        ((S.exceptionalFamily E).comap S.eraseEmptyLastHom) e := by
  obtain ⟨e, hc, ht, ho⟩ := eraseEmbeds_eraseEmpty S E
  refine ⟨OrderEmbedding.ofMapLEIff
    (fun b => ⟨e b.1, fun a hb => b.2 a (e.injective (hb.trans (ho a).symm))⟩)
    (fun b c => Subtype.mk_le_mk.trans e.le_iff_le), fun i => ?_, fun b hb => ?_⟩
  · exact hc i.1
  · refine ht b.1 fun ⟨c, hcb⟩ => hb ⟨⟨c, fun a hca => b.2 a ?_⟩, Subtype.ext hcb⟩
    rw [← hcb, hca]
    exact ho a

end Hironaka.Sequence
