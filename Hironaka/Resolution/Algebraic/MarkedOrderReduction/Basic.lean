/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.OrderReduction.EmptyIndifferent
import Hironaka.Scheme.BlowUpSequence.Functor
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The marked order-reduction functor `BMO_{n,m}`: its class and its data

Kollár's order reduction for marked ideals in dimension `n`, [Kol07, Theorem 107]: assuming order
reduction for ideals in dimensions `≤ n`, for every `m` there is a smooth blow-up sequence functor
`BMO_{n,m}` on marked triples `(X, I, m, E)` with `dim X = n` such that (1) the final marked
transform `I_r` has `max-ord I_r < m`, (2) `BMO_{n,m}` commutes with smooth morphisms and with
change of fields ([Kol07, 34.1–34.2]), and (3) if `m = max-ord I` then
`BMO_{n,m}(X, I, m, ∅) = BO_{n,m}(X, I, ∅)`.

This module fixes the vocabulary in which the theorem is stated and proved in
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/`: marked triples `(X, I, m, E)`
(`MarkedTriple`), smooth blow-up sequence functors of order `≥ m` (`OrderGeSeqFunctor`, [Kol07,
Definition 31] with the order condition (1′)–(4′) of [Kol07, Definition 66] and the convention of
[Kol07, 32]), their functoriality predicates, the dimension bound `Triple.HasDimLE` and the
indifference to empty boundary members of
`Hironaka/Resolution/Algebraic/OrderReduction/EmptyIndifferent.lean`.

* `MarkedTriple.BMOClass n m` is the domain of `BMO_{n,m}`: the marked triples of mark `m ≥ 1` with
  `dim X ≤ n`. As for the class of `BO_{n,m}`, Kollár's `dim X = n` is read as `dim X ≤ n`, and the
  mark is `≥ 1`: clause (1), `max-ord I_r < 0`, has no solution on a nonempty scheme, so
  Theorem 107's "for every `m`" ranges over the marks `m ≥ 1`; the class is empty at `m = 0`.
* `BMOData n m` packages clauses (1)–(2) of Theorem 107 together with the indifference to empty
  boundary members: a smooth blow-up sequence functor of order `≥ m` on `BMOClass n m` for every
  field of characteristic zero at once, whose final marked transform has maximal order `< m`,
  which commutes with smooth morphisms and with change of fields, and whose value does not change
  when unit-ideal members of `E` are deleted along an order embedding of index types
  (`OrderGeSeqAssignment.IndifferentToEmptyMembers`). The indifference is Kollár's "reindexing" of
  [Kol07, 34.1] and the convention [Kol07, 32] read as a property of the functor; it is what the
  boundary-clearing functor of [Kol07, Lemma 102] and clause (2) of [Kol07, Theorem 103] need of
  the marked functor in dimensions `< n`, and the assembled functor provides it in dimension `n`
  (`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Theorem107.lean`). The existence of such data
  under the inductive hypothesis (order reduction for ideals in dimension `n`, `BOData n m'` for all
  `m'`) is Theorem 107 itself (`Hironaka.BMO.data`); clause (3) is a theorem about the assembled
  functor (`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Clause3.lean`).
* `BMOData.ext`: two `BMOData n m` with the same values are equal.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace Hironaka

namespace MarkedTriple

variable {k : Type u} [Field k]

/-- The domain of the marked order-reduction functor `BMO_{n,m}` of [Kol07, Theorem 107]: the
marked triples `(X, I, m, E)` of mark `m` with `dim X ≤ n`, for a mark `m ≥ 1`. Kollár states the
theorem for `dim X = n`; the weaker bound is the convention of every functoriality class of this
development. Clause (1) of the theorem is unsatisfiable at `m = 0` on a nonempty scheme, so `1 ≤ m`
is part of the class, as for `BOClass`. Reducible, so that its three clauses are projections of the
hypothesis `hT` under instance transparency. -/
abbrev BMOClass (n m : ℕ) (T : MarkedTriple k) : Prop :=
  1 ≤ m ∧ T.toTriple.HasDimLE n ∧ T.m = m

end MarkedTriple

/-- **Clauses (1)–(2) of [Kol07, Theorem 107] as data**, together with the indifference to empty
boundary members. For every field `k` of characteristic zero, a smooth blow-up sequence functor of
order `≥ m` on the marked triples of `BMOClass n m` (`OrderGeSeqFunctor`: [Kol07, Definition 31]
with the order condition (2′)–(4′) of [Kol07, Definition 66] and the convention of [Kol07, 32] that
the output contains no empty blow-up), such that (1) for every marked triple `(X, I, m, E)` of the
class with `BMO_{n,m}(X, I, m, E) = Π : X_r → ⋯ → X_0 = X` the final marked transform
`I_r = Π^{-1}_*(I, m)` has `max-ord I_r < m`; (2) the functor commutes with smooth morphisms
([Kol07, 34.1], `CommutesWithSmooth`) and with change of fields ([Kol07, 34.2],
`CommutesWithBaseChange`, relating the functors over `k` and over `L`); and the functor is
indifferent to empty boundary members (`IndifferentToEmptyMembers`: deleting unit-ideal members of
`E` along an order embedding of index types does not change the value, Kollár's reindexing of
[Kol07, 34.1] and convention [Kol07, 32] as a property of the data). Theorem 107 asserts the
existence of such data under the inductive hypothesis; it is constructed as `Hironaka.BMO.data` in
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Theorem107.lean`. Clause (3) of the theorem is
proved in `Hironaka/Resolution/Algebraic/MarkedOrderReduction/Clause3.lean`. -/
structure BMOData (n m : ℕ) where
  /-- The functor `BMO_{n,m}` over each field `k` of characteristic zero. -/
  functor : ∀ (k : Type u) [Field k] [CharZero k],
    OrderGeSeqAssignment k (MarkedTriple.BMOClass n m)
  /-- Clause (1) of [Kol07, Theorem 107]: `max-ord I_r < m`. -/
  maxOrd_lt : ∀ (k : Type u) [Field k] [CharZero k] (T : MarkedTriple k)
    (hT : MarkedTriple.BMOClass n m T),
    (((functor k).seq T hT).markedTransformSeq T.I T.m (Fin.last _)).maxOrd < (m : ℕ∞)
  /-- Clause (2) of [Kol07, Theorem 107], first half: `BMO_{n,m}` commutes with smooth morphisms
  ([Kol07, 34.1]). -/
  commutesWithSmooth : ∀ (k : Type u) [Field k] [CharZero k], (functor k).CommutesWithSmooth
  /-- Clause (2) of [Kol07, Theorem 107], second half: `BMO_{n,m}` commutes with change of fields
  ([Kol07, 34.2]). -/
  commutesWithBaseChange : ∀ (k L : Type u) [Field k] [CharZero k] [Field L] [CharZero L]
    (σ : k →+* L), (functor k).CommutesWithBaseChange (functor L) σ
  /-- `BMO_{n,m}` is indifferent to empty boundary members (the convention [Kol07, 32] and the
  reindexing of [Kol07, 34.1] as a property of the functor). -/
  indifferentToEmptyMembers : ∀ (k : Type u) [Field k] [CharZero k],
    (functor k).IndifferentToEmptyMembers

end Hironaka

/-! ### Extensionality of `BMOData` -/

namespace Hironaka

/-- Two `BMOData n m` with the same values are equal: `OrderGeSeqAssignment.ext` on the functor
field, the other fields being propositions. Used to show that the stage-`0` package of the dimension
tower is unique (`HironakaExamples/Stage/BaseCases.lean`). -/
theorem BMOData.ext {n m : ℕ} {D D' : BMOData.{u} n m}
    (h : ∀ (k : Type u) [Field k] [CharZero k] (T : MarkedTriple k) (hT : T.BMOClass n m),
      (D.functor k).seq T hT = (D'.functor k).seq T hT) : D = D' := by
  cases D with
  | mk f _ _ _ _ =>
    cases D' with
    | mk f' _ _ _ _ =>
      obtain rfl : f = f' := by
        funext k _ _
        exact OrderGeSeqAssignment.ext fun T hT => h k T hT
      rfl

end Hironaka
