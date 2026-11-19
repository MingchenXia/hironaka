/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.BoundaryClearing.Data
public import Hironaka.Scheme.Snc.Basic
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The appended member of a divisor family is its last member

In the maximal contact case of the proof of Theorem 103, Kollár declares `E^0 := H` to be the
first divisor of `H + E` and applies Lemma 102 with `j = 0` [Kol07, 104, Step 2.2]. In this
library `DivisorFamily.append E J` puts the new member last (its index set is `E.ι ⊕ₗ PUnit`,
every `inl` before the `inr`), and `DivisorFamily.nth` counts positions from `0` in the linear
order of the index set. So Kollár's position `0` is the position `card E.ι` here:
`(E.append J).nth ⟨card E.ι, _⟩ = J` (`nth_append_last`). The finite-order fact behind it is that
the last position of a lexicographic sum with a one-element right summand is that summand
(`monoEquivOfFin_lex_inr_last`), the counterpart for `inr` of `monoEquivOfFin_lex_inl`.
-/

public section

universe u v

open AlgebraicGeometry.Scheme

namespace Hironaka.Sequence

/-- The last position of a lexicographic sum of finite linear orders whose right summand has a top
is the top: an order isomorphism `Fin k ≃o α ⊕ₗ β` sends the last index to the greatest element. -/
theorem monoEquivOfFin_lex_top {α β : Type*} [Fintype α] [LinearOrder α] [Fintype β]
    [LinearOrder β] [OrderTop β] (hpos : 0 < Fintype.card (α ⊕ₗ β)) :
    monoEquivOfFin (α ⊕ₗ β) rfl ⟨Fintype.card (α ⊕ₗ β) - 1, Nat.sub_lt hpos Nat.one_pos⟩ = ⊤ := by
  set e := monoEquivOfFin (α ⊕ₗ β) rfl
  refine le_antisymm le_top ?_
  obtain ⟨i, hi⟩ := e.surjective ⊤
  rw [← hi]
  exact e.monotone (Fin.le_def.mpr (Nat.le_sub_one_of_lt i.2))

/-- `card (α ⊕ₗ PUnit) = card α + 1`. -/
theorem card_lex_punit (α : Type*) [Fintype α] :
    Fintype.card (α ⊕ₗ PUnit.{v + 1}) = Fintype.card α + 1 := by
  rw [Fintype.card_congr (toLex : α ⊕ PUnit.{v + 1} ≃ α ⊕ₗ PUnit.{v + 1}).symm, Fintype.card_sum,
    Fintype.card_punit]

/-- In `α ⊕ₗ PUnit` the element at position `card α`, the last one, is the `inr`; the counterpart
for `inr` of `monoEquivOfFin_lex_inl`. -/
theorem monoEquivOfFin_lex_inr_last {α : Type*} [Fintype α] [LinearOrder α]
    (h : Fintype.card α < Fintype.card (α ⊕ₗ PUnit.{v + 1})) :
    monoEquivOfFin (α ⊕ₗ PUnit.{v + 1}) rfl ⟨Fintype.card α, h⟩ = toLex (Sum.inr PUnit.unit) := by
  have hcard : Fintype.card (α ⊕ₗ PUnit.{v + 1}) = Fintype.card α + 1 := card_lex_punit α
  have hpos : 0 < Fintype.card (α ⊕ₗ PUnit.{v + 1}) := lt_of_le_of_lt (Nat.zero_le _) h
  have hidx : (⟨Fintype.card α, h⟩ : Fin (Fintype.card (α ⊕ₗ PUnit.{v + 1}))) =
      ⟨Fintype.card (α ⊕ₗ PUnit.{v + 1}) - 1, Nat.sub_lt hpos Nat.one_pos⟩ :=
    Fin.ext (by change Fintype.card α = Fintype.card (α ⊕ₗ PUnit.{v + 1}) - 1; omega)
  rw [hidx, monoEquivOfFin_lex_top hpos]
  rfl

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- One member is appended: `card E.ι < card (E.append J).ι`. -/
theorem card_lt_card_ι_append (E : DivisorFamily X) (J : X.IdealSheafData) :
    Fintype.card E.ι < Fintype.card (E.append J).ι := by
  change Fintype.card E.ι < Fintype.card (E.ι ⊕ₗ PUnit.{u + 1})
  rw [card_lex_punit]
  exact Nat.lt_succ_self _

/-- The appended member `J` of `E.append J` sits at the last position `card E.ι` (positions are
counted from `0`, new members come last). Kollár's instruction to "declare `E^0 := H` to be the
first divisor in `H + E`" and apply Lemma 102 with `j = 0` [Kol07, 104, Step 2.2] therefore reads
`j := card E.ι` here. -/
theorem nth_append_last (E : DivisorFamily X) (J : X.IdealSheafData)
    (h : Fintype.card E.ι < Fintype.card (E.append J).ι) :
    (E.append J).nth ⟨Fintype.card E.ι, h⟩ = J := by
  change (E.append J).component (monoEquivOfFin (E.ι ⊕ₗ PUnit.{u + 1}) rfl ⟨_, h⟩) = J
  rw [monoEquivOfFin_lex_inr_last h]
  rfl

end Hironaka.Sequence
