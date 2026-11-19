/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Step1NonmonomialPart
public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Step2Separation
public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Step3Input
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.InducedClass
import Hironaka.Scheme.BlowUpSequence.ConcatMarked
import Hironaka.Scheme.BlowUpSequence.ConcatTransforms
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The functor `BMO_{n,m}` assembled

[Kol07, Theorem 107] asserts, assuming order reduction for ideals in dimensions `≤ n`, a smooth
blow-up sequence functor `BMO_{n,m}` on marked triples `(X, I, m, E)` with `dim X = n` such that
(1) `max-ord I_r < m` at the end, (2) `BMO_{n,m}` commutes with smooth morphisms and with change of
fields, and (3) `BMO_{n,m}(X, I, m, ∅) = BO_{n,m}(X, I, ∅)` when `m = max-ord I`. Its proof
([Kol07, 111]) is the concatenation of three steps, each run on the marked triple induced at the
end of the previous one: Step 1 reduces `max-ord N(I)` below `m`
(`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Step1NonmonomialPart.lean`, `step1`), Step 2
separates `cosupp(I, m)` from `cosupp N(I)`
(`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Step2Separation.lean`, `step2`), and Step 3
reduces the order of the monomial part `M(I)` below `m` (the geometric Step 3 of
`Hironaka/Resolution/Algebraic/Monomial/Geometric/`, run on `X` for `(M(I), m, E)`;
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Step3Input.lean`). Empty blow-ups are to be
deleted ([Kol07, 32]); none occur, each step being without empty blow-ups, so the concatenation is
the functor's value as it stands.

* `afterStep1 bo T hT`, `afterStep2 bo T hT`: the marked triples induced at the ends of Steps 1
  and 2 (`MarkedTriple.induced`), again of `BMOClass n m` (`MarkedTriple.bmoClass_induced`).
* `bmoSeq bo T hT`: **`BMO_{n,m}(X, I, m, E)`**, Step 1, then Step 2 of `afterStep1`, then Step 3
  of `afterStep2` (`concat`); a smooth blow-up sequence of order `≥ m` for `(X, I, m, E)`
  (`bmoSeq_isOrderGeSeq`) without empty blow-ups (`bmoSeq_noEmptyCenters`; `eraseEmpty_bmoSeq`:
  the deletion of [Kol07, 32] is the identity).
* `functor bo`: **the functor `BMO_{n,m}`** on the class `BMOClass n m`, an `OrderGeSeqFunctor`
  (the sequence, the order condition of [Kol07, Definition 66], no empty blow-ups).

The input is `bo : ∀ d, BOData n d`, order reduction for ideals in dimension `n` at every order,
since the orders that Steps 1–2 call are not bounded in terms of `m`. Clause (1)
(`BMO.maxOrd_lt`), clause (2) (`BMO.commutesWithSmooth`, `BMO.commutesWithBaseChange`, with
`BMO.indifferentToEmptyMembers`) and clause (3) (`BMO.eq_BO_of_maxOrd`) are the theorems of
`Clause1.lean`, `Smooth.lean`, `BaseChangeLoop.lean` and `Clause3.lean`; the data
`BMO.data : BMOData n m` are assembled from them in `Theorem107.lean`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Hironaka Scheme BlowUpSequence

namespace Hironaka.BMO

variable {k : Type u} [Field k] [CharZero k] {n : ℕ} (bo : ∀ d : ℕ, BOData.{u} n d) {m : ℕ}
  (T : MarkedTriple k) (hT : MarkedTriple.BMOClass n m T)

/-- The marked triple induced at the end of Step 1 ([Kol07, 111]: "instead of
`(X^1, (Π_1)^{-1}_*(I, m), (Π_1)^{-1}_{tot}(E))`, write `(X, I, m, E)`"). -/
noncomputable def afterStep1 : MarkedTriple k :=
  T.induced (step1 bo T hT).1 (step1_isOrderGeSeq bo T hT) (Fin.last _)

/-- The end of Step 1 is again a marked triple of `BMOClass n m`
(`MarkedTriple.bmoClass_induced`). -/
theorem bmoClass_afterStep1 : MarkedTriple.BMOClass n m (afterStep1 bo T hT) :=
  MarkedTriple.bmoClass_induced T hT (step1_isOrderGeSeq bo T hT) (Fin.last _)

/-- After Step 1, `max-ord N(I) < m` ([Kol07, 111]: "we may assume that `max-ord N(I) < m`";
`roundOrder_induced_step1_lt` read on the induced triple). -/
theorem roundOrder_afterStep1_lt : roundOrder (afterStep1 bo T hT) < m :=
  roundOrder_induced_step1_lt bo T hT

/-- The marked triple induced at the end of Step 2 of `afterStep1`, with
`cosupp(I, m) ∩ cosupp N(I) = ∅` ([Kol07, 111, Step 2]). -/
noncomputable def afterStep2 : MarkedTriple k :=
  (afterStep1 bo T hT).induced (step2 bo (afterStep1 bo T hT) (bmoClass_afterStep1 bo T hT)).1
    (step2_isOrderGeSeq bo (afterStep1 bo T hT) (bmoClass_afterStep1 bo T hT)) (Fin.last _)

/-- The end of Step 2 is again a marked triple of `BMOClass n m`. -/
theorem bmoClass_afterStep2 : MarkedTriple.BMOClass n m (afterStep2 bo T hT) :=
  MarkedTriple.bmoClass_induced (afterStep1 bo T hT) (bmoClass_afterStep1 bo T hT)
    (step2_isOrderGeSeq bo (afterStep1 bo T hT) (bmoClass_afterStep1 bo T hT)) (Fin.last _)

/-- After Step 2 the separation order is `0` ([Kol07, 111, Step 2]:
"`cosupp(I, m) ∩ cosupp N(I) = ∅`"; `sepOrder_induced_step2_eq_zero` read on the induced triple). -/
theorem sepOrder_afterStep2_eq_zero : sepOrder (afterStep2 bo T hT) = 0 :=
  sepOrder_induced_step2_eq_zero bo (afterStep1 bo T hT) (bmoClass_afterStep1 bo T hT)

/-- **The smooth blow-up sequence `BMO_{n,m}(X, I, m, E)`** ([Kol07, Theorem 107] and
[Kol07, 111]): Step 1, then Step 2 of the induced marked triple, then the geometric Step 3 (on `X`
for `(M(I), m, E)`) of the induced marked triple, concatenated. -/
noncomputable def bmoSeq : BlowUpSequence T.X.left :=
  (step1 bo T hT).1.concat
    ((step2 bo (afterStep1 bo T hT) (bmoClass_afterStep1 bo T hT)).1.concat
      (step3Seq (afterStep2 bo T hT) (bmoClass_afterStep2 bo T hT)))

/-- **`BMO_{n,m}(X, I, m, E)` is a smooth blow-up sequence of order `≥ m` for `(X, I, m, E)`**
(conditions (2′)–(4′) of [Kol07, Definition 66]): each step is one for the marked triple induced
at the end of the previous step, and the order condition concatenates (`isOrderGeSeq_concat`). -/
theorem bmoSeq_isOrderGeSeq :
    (bmoSeq bo T hT).IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E :=
  isOrderGeSeq_concat _ _ _ (step1_isOrderGeSeq bo T hT)
    (isOrderGeSeq_concat _ _ _
      (step2_isOrderGeSeq bo (afterStep1 bo T hT) (bmoClass_afterStep1 bo T hT))
      (step3Seq_isOrderGeSeq (afterStep2 bo T hT) (bmoClass_afterStep2 bo T hT)))

/-- **`BMO_{n,m}(X, I, m, E)` contains no empty blow-up** ([Kol07, 32]): none of the three steps
does. -/
theorem bmoSeq_noEmptyCenters : (bmoSeq bo T hT).NoEmptyCenters :=
  noEmptyCenters_concat _ _ (step1_noEmptyCenters bo T hT)
    (noEmptyCenters_concat _ _
      (step2_noEmptyCenters bo (afterStep1 bo T hT) (bmoClass_afterStep1 bo T hT))
      (step3Seq_noEmptyCenters (afterStep2 bo T hT) (bmoClass_afterStep2 bo T hT)))

/-- The deletion of empty blow-ups ([Kol07, 32]) leaves `BMO_{n,m}(X, I, m, E)` unchanged: there
are none (`eraseEmpty_eq_self_iff`). -/
theorem eraseEmpty_bmoSeq : (bmoSeq bo T hT).eraseEmpty = bmoSeq bo T hT :=
  (eraseEmpty_eq_self_iff _).2 (bmoSeq_noEmptyCenters bo T hT)

/-- **The functor `BMO_{n,m}`** of [Kol07, Theorem 107] on the class `BMOClass n m`: the sequence
`bmoSeq`, of order `≥ m` for its marked triple, without empty blow-ups (`OrderGeSeqFunctor`).
Clauses (1)–(3) are the theorems `BMO.maxOrd_lt`, `BMO.commutesWithSmooth`,
`BMO.commutesWithBaseChange`, `BMO.indifferentToEmptyMembers` and `BMO.eq_BO_of_maxOrd`. The mark
`m` is explicit, since it is not determined by the input `bo`: `BMO.functor m bo`. -/
noncomputable def functor (m : ℕ) : OrderGeSeqAssignment k (MarkedTriple.BMOClass n m) where
  seq T hT := bmoSeq bo T hT
  isOrderGeSeq T hT := bmoSeq_isOrderGeSeq bo T hT
  noEmptyCenters T hT := bmoSeq_noEmptyCenters bo T hT

/-- The value of the functor `BMO_{n,m}` is the assembled sequence. -/
theorem functor_seq : (functor bo m).seq T hT = bmoSeq bo T hT := rfl

end Hironaka.BMO
