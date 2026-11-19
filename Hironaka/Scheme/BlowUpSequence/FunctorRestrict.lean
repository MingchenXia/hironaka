/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Restriction of a blow-up sequence functor to a smaller class

Kollár's functors are defined on classes of triples (the class of [Kol07, Theorem 103] is the
triples with `dim X = n` and `max-ord I ≤ m`); `OrderSeqFunctor k m Dom` carries its class `Dom`
in its type, so the same assignment of sequences on a smaller class is a different term. The
**restriction** of a functor along an inclusion of classes `Dom' ⊆ Dom` is the functor on `Dom'`
with the same values; it inherits the order condition and the absence of empty blow-ups (the
functor's fields) and the commutation with the surjections of a class of morphisms (hypothesis (3)
of [Kol07, Theorem 105]). The tower of order reduction functors indexed by the dimension is
compared stage against stage through such restrictions, using the uniqueness of the
globalization of [Kol07, Theorem 105].
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace Hironaka.OrderSeqAssignment

variable {k : Type u} [Field k] {m : ℕ} {Dom : Triple k → Prop}

/-- The **restriction** of a blow-up sequence functor of order `m` to a smaller class `Dom'` along
the inclusion `h : ∀ T, Dom' T → Dom T`: the same sequences, the same fields. -/
def restrict (B : OrderSeqAssignment k m Dom) (Dom' : Triple k → Prop) (h : ∀ T, Dom' T → Dom T) :
    OrderSeqAssignment k m Dom' where
  seq T hT := B.seq T (h T hT)
  isOrderSeq T hT := B.isOrderSeq T (h T hT)
  noEmptyCenters T hT := B.noEmptyCenters T (h T hT)

/-- The restricted functor has the same values. -/
theorem restrict_seq {Dom' : Triple k → Prop} (B : OrderSeqAssignment k m Dom)
    (h : ∀ T, Dom' T → Dom T) (T : Triple k) (hT : Dom' T) :
    (B.restrict Dom' h).seq T hT = B.seq T (h T hT) :=
  rfl

/-- A functor commuting with the surjections of a class of morphisms (hypothesis (3) of
[Kol07, Theorem 105]) restricts to one: the same pairs, the class proofs carried along the
inclusion. -/
theorem restrict_commutesWithSurjectionsIn {Dom' : Triple k → Prop} (B : OrderSeqAssignment k m Dom)
    (h : ∀ T, Dom' T → Dom T) (M : MorphismProperty Scheme.{u})
    (hB : B.CommutesWithSurjectionsIn M) : (B.restrict Dom' h).CommutesWithSurjectionsIn M :=
  fun T T' g hM hs hpb hT hT' => hB T T' g hM hs hpb (h T hT) (h T' hT')

end Hironaka.OrderSeqAssignment
