/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.OrderReduction.Step21BoundaryClearing
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Positions of the original members in the total transform

In the total transform of a divisor family along a blow-up [Kol07, Definition 65] the exceptional
divisor is "added as the last divisor": here the index set becomes `Lex (ι ⊕ PUnit)`. So the first
`card E.ι` positions of `totalTransformSeq E i` are the birational transforms of the original
members, position by position (`nth_totalTransformSeq_of_lt`): the `j`-th member of the total
transform (in the order of the index set, through `monoEquivOfFin`; `DivisorFamily.nth`) at a
position `j < card E.ι` is the strict transform of the `j`-th member of `E`. The one fact about
finite linear orders this needs: in a lexicographic sum `α ⊕ₗ β` the `j`-th element, for
`j < card α`, is `inl` of the `j`-th element of `α` (`monoEquivOfFin_lex_inl`). Every `inl`
precedes every `inr`, so an `inr` at position `j` would leave only `j < card α` positions for the
`card α` elements `inl a`; the resulting map `Fin (card α) → α` is strictly monotone into `α`,
hence Mathlib's unique increasing enumeration (`Finset.orderEmbOfFin_unique`).

This is what lets the boundary-clearing step of the proof of Theorem 103 [Kol07, 104, Step 2.1]
speak of the transform of the `j`-th original member at every stage. -/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme IdealSheafData BlowUpSequence

namespace Hironaka.Sequence

/-- In a lexicographic sum of finite linear orders, the `j`-th element for `j < card α` is `inl`
of the `j`-th element of `α`; the finite-order fact behind "new divisors come after old ones"
[Kol07, Definition 65]. -/
theorem monoEquivOfFin_lex_inl {α β : Type*} [Fintype α] [LinearOrder α] [Fintype β]
    [LinearOrder β] {j : ℕ} (hj : j < Fintype.card α) (hj' : j < Fintype.card (α ⊕ₗ β)) :
    monoEquivOfFin (α ⊕ₗ β) rfl ⟨j, hj'⟩ = toLex (Sum.inl (monoEquivOfFin α rfl ⟨j, hj⟩)) := by
  classical
  set e := monoEquivOfFin (α ⊕ₗ β) rfl with he
  have hcard : Fintype.card α ≤ Fintype.card (α ⊕ₗ β) := by
    rw [Fintype.card_congr (toLex : α ⊕ β ≃ α ⊕ₗ β).symm, Fintype.card_sum]
    exact Nat.le_add_right _ _
  -- the first `card α` positions are `inl`'s
  have hinl : ∀ i : Fin (Fintype.card (α ⊕ₗ β)), i.val < Fintype.card α →
      ∃ a, e i = toLex (Sum.inl a) := by
    intro i hi
    rcases hx : ofLex (e i) with a | b
    · exact ⟨a, by rw [← toLex_ofLex (e i), hx]⟩
    · exfalso
      have hbound : ∀ a : α, (e.symm (toLex (Sum.inl a))).val < i.val := by
        intro a
        have h1 : toLex (Sum.inl a) < e i := by
          rw [← toLex_ofLex (e i), hx]
          exact Sum.Lex.inl_lt_inr a b
        have h2 : e.symm (toLex (Sum.inl a)) < e.symm (e i) := e.symm.lt_iff_lt.mpr h1
        rw [e.symm_apply_apply] at h2
        exact h2
      have hinj : Function.Injective
          (fun a : α => (⟨(e.symm (toLex (Sum.inl a))).val, hbound a⟩ : Fin i.val)) := by
        intro a a' haa'
        have h0 : (e.symm (toLex (Sum.inl a))).val = (e.symm (toLex (Sum.inl a'))).val :=
          Fin.mk.inj_iff.mp haa'
        have h1 : e.symm (toLex (Sum.inl a)) = e.symm (toLex (Sum.inl a')) := Fin.ext h0
        exact Sum.inl_injective (toLex.injective (e.symm.injective h1))
      have := Fintype.card_le_of_injective _ hinj
      rw [Fintype.card_fin] at this
      exact absurd (lt_of_le_of_lt this hi) (lt_irrefl _)
  -- the induced enumeration of `α`
  let f : Fin (Fintype.card α) → α := fun k =>
    Classical.choose (hinl (Fin.castLE hcard k) k.2)
  have hf : ∀ k, e (Fin.castLE hcard k) = toLex (Sum.inl (f k)) := fun k =>
    Classical.choose_spec (hinl (Fin.castLE hcard k) k.2)
  have hmono : StrictMono f := by
    intro k l hkl
    have h1 : e (Fin.castLE hcard k) < e (Fin.castLE hcard l) :=
      e.strictMono (Fin.strictMono_castLE hcard hkl)
    rw [hf, hf] at h1
    exact Sum.Lex.inl_lt_inl_iff.mp h1
  have hfe : ∀ k, f k = monoEquivOfFin α rfl k := fun k => by
    have := congrFun (Finset.orderEmbOfFin_unique (s := (Finset.univ : Finset α))
      (rfl : (Finset.univ : Finset α).card = Fintype.card α) (fun x => Finset.mem_univ (f x))
      hmono) k
    exact this
  have hidx : (⟨j, hj'⟩ : Fin (Fintype.card (α ⊕ₗ β))) = Fin.castLE hcard ⟨j, hj⟩ := Fin.ext rfl
  rw [hidx, hf, hfe]

variable {X : Scheme.{u}}

/-- `card E.ι ≤ card (E.totalTransform D).ι`: one member is appended [Kol07, Definition 65]. -/
theorem card_le_card_ι_totalTransform (E : DivisorFamily X) (D : X.IdealSheafData) :
    Fintype.card E.ι ≤ Fintype.card (E.totalTransform D).ι := by
  change Fintype.card E.ι ≤ Fintype.card (E.ι ⊕ₗ PUnit.{u + 1})
  rw [Fintype.card_congr (toLex : E.ι ⊕ PUnit.{u + 1} ≃ E.ι ⊕ₗ PUnit.{u + 1}).symm,
    Fintype.card_sum]
  exact Nat.le_add_right _ _

/-- The exceptional divisor is added as the last member [Kol07, Definition 65], so for one blow-up
the `j`-th member of the total transform, `j < card E.ι`, is the strict transform of the `j`-th
member of `E`. -/
theorem nth_totalTransform_inl (E : DivisorFamily X) (D : X.IdealSheafData) {j : ℕ}
    (hj : j < Fintype.card E.ι) (hj' : j < Fintype.card (E.totalTransform D).ι) :
    (E.totalTransform D).nth ⟨j, hj'⟩ = (E.nth ⟨j, hj⟩).strictTransform D := by
  change (E.totalTransform D).component (monoEquivOfFin (E.ι ⊕ₗ PUnit.{u + 1}) rfl ⟨j, hj'⟩) =
    (E.component (monoEquivOfFin E.ι rfl ⟨j, hj⟩)).strictTransform D
  rw [monoEquivOfFin_lex_inl hj hj']
  rfl

/-- The first `card E.ι` positions of the total transform at any stage are the birational
transforms of the original members, position by position [Kol07, Definition 65]. -/
theorem nth_totalTransformSeq_of_lt : ∀ {X : Scheme.{u}} (S : BlowUpSequence X)
    (E : DivisorFamily X) (i : Fin (S.length + 1)) {j : ℕ} (hj : j < Fintype.card E.ι),
    (S.totalTransformSeq E i).nth
        ⟨j, lt_of_lt_of_le hj (Hironaka.BO.card_le_card_ι_totalTransformSeq S E i)⟩ =
      S.strictTransformSeq (E.nth ⟨j, hj⟩) i
  | _, nil _, _, _, _, _ => rfl
  | _, cons _ _ _, _, ⟨0, _⟩, _, _ => rfl
  | _, cons _ D rest, E, ⟨k + 1, h⟩, j, hj => by
    have ih := nth_totalTransformSeq_of_lt rest (E.totalTransform D) ⟨k, Nat.lt_of_succ_lt_succ h⟩
      (lt_of_lt_of_le hj (card_le_card_ι_totalTransform E D))
    change (rest.totalTransformSeq (E.totalTransform D) ⟨k, _⟩).nth ⟨j, _⟩ =
      rest.strictTransformSeq ((E.nth ⟨j, hj⟩).strictTransform D) ⟨k, _⟩
    rw [ih, nth_totalTransform_inl]

end Hironaka.Sequence
