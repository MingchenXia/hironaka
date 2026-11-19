/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The original components inside the total transform

The total transform at stage `i` of a blow-up sequence ([Kol07, Definition 25], with the
exceptional divisors appended last as in [Kol07, Definition 65]) lists the birational transforms
`(π_0 ⋯ π_{i-1})^{-1}_* E_a` of the original components followed by the exceptional divisors;
`BlowUpSequence.originalIdx S E i` is the index of the transform of `E_a`. Two facts about it, both
by the recursion that defines `totalTransformSeq`: distinct components have distinct indices, and
the component at the index of `E_a` is the strict transform of `E_a` along the sequence
(`strictTransformSeq`, the birational transform of [Kol07, 30.2]).
-/

public section

universe u

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Scheme.BlowUpSequence

variable {X : Scheme.{u}}

/-- Distinct components have distinct indices in the total transform. -/
theorem originalIdx_injective : ∀ {X : Scheme.{u}} (S : BlowUpSequence X) (E : DivisorFamily X)
    (i : Fin (S.length + 1)), Function.Injective (S.originalIdx E i)
  | _, nil _, _, _ => fun _ _ h => h
  | _, cons _ _ _, _, ⟨0, _⟩ => fun _ _ h => h
  | _, cons _ D rest, E, ⟨j + 1, h⟩ => fun _ _ hab =>
    Sum.inl_injective (toLex.injective
      (originalIdx_injective rest (E.totalTransform D) ⟨j, Nat.lt_of_succ_lt_succ h⟩ hab))

/-- The component of the total transform at the index of `E_a` is the birational transform
`(π_0 ⋯ π_{i-1})^{-1}_* E_a` [Kol07, Definition 25]. -/
theorem component_originalIdx : ∀ {X : Scheme.{u}} (S : BlowUpSequence X) (E : DivisorFamily X)
    (i : Fin (S.length + 1)) (a : E.ι),
    (S.totalTransformSeq E i).component (S.originalIdx E i a) =
      S.strictTransformSeq (E.component a) i
  | _, nil _, _, _, _ => rfl
  | _, cons _ _ _, _, ⟨0, _⟩, _ => rfl
  | _, cons _ D rest, E, ⟨j + 1, h⟩, a =>
    component_originalIdx rest (E.totalTransform D) ⟨j, Nat.lt_of_succ_lt_succ h⟩
      (toLex (Sum.inl a))

end AlgebraicGeometry.Scheme.BlowUpSequence
