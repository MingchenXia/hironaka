/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.EraseEmptyEmbedding
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.Bookkeeping
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Deleting unit members of the boundary: the exceptional family and the positions

A member of the boundary equal to the unit ideal is invisible: the empty blow-up convention
[Kol07, 32] and the reindexing in the second clause of [Kol07, 34.1]. `IsTopErasure E' E e`
(`Hironaka/Resolution/Algebraic/Kol07/EraseEmptyEmbedding.lean`) names the relation "`E'` is `E`
with unit members deleted along the order embedding `e`". This module proves what the
boundary-clearing rounds of the proof of Theorem 103 [Kol07, 104, Steps 2.1 and 2.2] (one round per
member of the boundary, then the restriction to the hypersurface with the exceptional sub-family
`F_r`) need about it:

* `strictTransformSeq_top`: the strict transform of the unit ideal along any sequence is the unit
  ideal (`strictTransform_top_right` iterated), so a deleted member's transform is `⊤` at every
  stage;
* `exists_isTopErasure_totalTransformSeq_exceptional`: the deletion induced at the end of a
  sequence (`exists_isTopErasure_totalTransformSeq`) sends the exceptional indices, those not of
  the form `originalIdx`, onto the exceptional indices; hence
  `exists_orderEmbedding_exceptionalFamily`: the exceptional sub-families of the two boundaries
  are the same family up to a surjective order embedding matching the members;
* `card_subtype_lt_eq_symm_monoEquivOfFin`: in a finite linear order the number of elements below
  `x` is the position of `x` in the enumeration `monoEquivOfFin`, used to count the surviving
  positions below a given one;
* `eraseEmpty_cons_nil_eq_nil`, `concat_eq_of_eq_nil`: a one-step sequence with an empty center
  erases to the empty sequence; concatenating the empty sequence changes nothing.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme IdealSheafData BlowUpSequence

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### The unit ideal along a sequence, the empty center, the empty tail -/

/-- The strict transform of the unit ideal along a blow-up sequence is the unit ideal at every
stage (`strictTransform_top_right` iterated). -/
theorem strictTransformSeq_top : ∀ {X : Scheme.{u}} (S : BlowUpSequence X) (i : Fin (S.length + 1)),
    S.strictTransformSeq ⊤ i = ⊤
  | _, nil _, _ => rfl
  | _, cons _ _ _, ⟨0, _⟩ => rfl
  | _, cons _ D rest, ⟨j + 1, h⟩ => by
    change rest.strictTransformSeq (Scheme.IdealSheafData.strictTransform ⊤ D) ⟨j,
        Nat.lt_of_succ_lt_succ h⟩ = ⊤
    rw [strictTransform_top_right]
    exact strictTransformSeq_top rest _

/-- A one-step sequence whose center is the unit ideal (the empty blow-up) erases to the empty
sequence [Kol07, 32]. -/
theorem eraseEmpty_cons_nil_eq_nil (D : X.IdealSheafData) (hD : D = ⊤) :
    (cons X D (nil _)).eraseEmpty = nil X :=
  eraseEmpty_eq_nil _ fun i => by
    obtain ⟨i, hi⟩ := i
    obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
    exact hD

/-- Concatenating the empty sequence does not change a sequence (the empty sequence is a right
unit for `concat`). -/
theorem concat_nil_right : ∀ {X : Scheme.{u}} (S : BlowUpSequence X), S.concat (nil _) = S
  | _, nil _ => rfl
  | _, cons _ D rest => congrArg (cons _ D) (concat_nil_right rest)

/-- Concatenating a tail equal to the empty sequence does not change a sequence (the form used
when the tail is a functor's value). -/
theorem concat_eq_of_eq_nil (S : BlowUpSequence X) {R : BlowUpSequence S.last} (hR : R = nil _) :
    S.concat R = S := by
  subst hR
  exact concat_nil_right S

/-! ### Counting positions in a finite linear order -/

/-- In a finite linear order the number of elements strictly below `x` is the position of `x` in
the enumeration `monoEquivOfFin`; this is how the reindexing of [Kol07, 34.1] is counted. -/
theorem card_subtype_lt_eq_symm_monoEquivOfFin (α : Type*) [Fintype α] [LinearOrder α] (x : α) :
    Fintype.card {a : α // a < x} = ((monoEquivOfFin α rfl).symm x : ℕ) := by
  classical
  rw [Fintype.card_congr ((monoEquivOfFin α rfl).symm.toEquiv.subtypeEquiv
    (q := fun i : Fin (Fintype.card α) => i < (monoEquivOfFin α rfl).symm x)
    fun a => ((monoEquivOfFin α rfl).symm.lt_iff_lt (x := a) (y := x)).symm)]
  rw [Fintype.card_subtype (fun i : Fin (Fintype.card α) => i < (monoEquivOfFin α rfl).symm x),
    Finset.filter_gt_eq_Iio, Fin.card_Iio]

/-- The number of elements at most `x` is the position of `x` plus one. -/
theorem card_subtype_le_eq_symm_monoEquivOfFin (α : Type*) [Fintype α] [LinearOrder α] (x : α) :
    Fintype.card {a : α // a ≤ x} = ((monoEquivOfFin α rfl).symm x : ℕ) + 1 := by
  classical
  rw [Fintype.card_congr ((monoEquivOfFin α rfl).symm.toEquiv.subtypeEquiv
    (q := fun i : Fin (Fintype.card α) => i ≤ (monoEquivOfFin α rfl).symm x)
    fun a => ((monoEquivOfFin α rfl).symm.le_iff_le (x := a) (y := x)).symm)]
  rw [Fintype.card_subtype (fun i : Fin (Fintype.card α) => i ≤ (monoEquivOfFin α rfl).symm x),
    Finset.filter_ge_eq_Iic, Fin.card_Iic]

/-! ### The deletion at the end of a sequence sends exceptional indices onto exceptional indices -/

/-- A deletion of unit members of the starting family induces a deletion between the families at
the end of any sequence which carries the transforms of the original members to the transforms of
the original members, hits every index that is not the transform of an original member, and sends
an index onto the transform of an original member only if it is one
(`exists_isTopErasure_totalTransformSeq` with the exceptional indices tracked). -/
theorem exists_isTopErasure_totalTransformSeq_exceptional :
    ∀ {X : Scheme.{u}} (S : BlowUpSequence X) (E' E : DivisorFamily X) (e : E'.ι ↪o E.ι)
      (_he : IsTopErasure E' E e),
      ∃ e' : (S.totalTransformSeq E' (Fin.last _)).ι ↪o (S.totalTransformSeq E (Fin.last _)).ι,
        IsTopErasure (S.totalTransformSeq E' (Fin.last _)) (S.totalTransformSeq E (Fin.last _)) e' ∧
        (∀ a, e' (S.originalIdx E' (Fin.last _) a) = S.originalIdx E (Fin.last _) (e a)) ∧
        (∀ b, (∀ a, b ≠ S.originalIdx E (Fin.last _) a) → ∃ b', e' b' = b) ∧
        ∀ b' a, e' b' = S.originalIdx E (Fin.last _) a → ∃ a', b' = S.originalIdx E' (Fin.last _) a'
  | _, nil _, _, _, e, he =>
    ⟨e, he, fun _ => rfl, fun b hb => (hb b rfl).elim, fun b' _ _ => ⟨b', rfl⟩⟩
  | _, cons X D rest, E', E, e, he => by
    obtain ⟨e', h1, h2, h3, h4⟩ := exists_isTopErasure_totalTransformSeq_exceptional rest
      (E'.totalTransform D) (E.totalTransform D) (sumLexMapEmb e) (he.totalTransform D)
    refine ⟨e', h1, fun a => h2 (toLex (Sum.inl a)), fun b hb => ?_, fun b' a hb' => ?_⟩
    · by_cases hexc :
          b = rest.originalIdx (E.totalTransform D) (Fin.last _) (toLex (Sum.inr PUnit.unit))
      · exact ⟨rest.originalIdx (E'.totalTransform D) (Fin.last _) (toLex (Sum.inr PUnit.unit)),
          (h2 (toLex (Sum.inr PUnit.unit))).trans hexc.symm⟩
      · refine h3 b fun c hc => ?_
        obtain ⟨c, rfl⟩ := toLex.surjective c
        rcases c with a | u
        · exact hb a hc
        · exact hexc hc
    · obtain ⟨c', hc'⟩ := h4 b' (toLex (Sum.inl a)) hb'
      obtain ⟨c', rfl⟩ := toLex.surjective c'
      rcases c' with a' | u
      · exact ⟨a', hc'⟩
      · exfalso
        subst hc'
        have h5 : rest.originalIdx (E.totalTransform D) (Fin.last _) (toLex (Sum.inr u)) =
            rest.originalIdx (E.totalTransform D) (Fin.last _) (toLex (Sum.inl a)) :=
          (h2 (toLex (Sum.inr u))).symm.trans hb'
        have h6 : toLex (Sum.inr u) = toLex (Sum.inl a) :=
          originalIdx_injective rest (E.totalTransform D) (Fin.last _) h5
        exact Sum.inr_ne_inl (toLex.injective h6)

/-- Deleting unit members of the starting family does not change the exceptional sub-family at
the end of a sequence: the two exceptional sub-families are matched by a surjective order
embedding with equal members [Kol07, 32 and 34.1]. -/
theorem exists_orderEmbedding_exceptionalFamily (S : BlowUpSequence X) (E' E : DivisorFamily X)
    (e : E'.ι ↪o E.ι) (he : IsTopErasure E' E e) :
    ∃ g : (S.exceptionalFamily E').ι ↪o (S.exceptionalFamily E).ι, Function.Surjective g ∧
      ∀ b, (S.exceptionalFamily E).component (g b) = (S.exceptionalFamily E').component b := by
  obtain ⟨e', h1, h2, h3, h4⟩ := exists_isTopErasure_totalTransformSeq_exceptional S E' E e he
  have hexc : ∀ b' : (S.exceptionalFamily E').ι, ∀ a, e' b'.1 ≠ S.originalIdx E (Fin.last _) a :=
    fun b' a h => by
      obtain ⟨a', ha'⟩ := h4 b'.1 a h
      exact b'.2 a' ha'
  refine ⟨OrderEmbedding.ofMapLEIff (fun b' => ⟨e' b'.1, hexc b'⟩) fun a b => e'.le_iff_le,
    fun b => ?_, fun b' => h1.1 b'.1⟩
  obtain ⟨c, hc⟩ := h3 b.1 b.2
  refine ⟨⟨c, fun a' ha' => ?_⟩, Subtype.ext hc⟩
  exact b.2 (e a') (hc.symm.trans (ha' ▸ h2 a'))

end Hironaka.Sequence
