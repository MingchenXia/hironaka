/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Theorem107
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.InducedClass
import Hironaka.Resolution.Algebraic.Monomial.Geometric.RealizeDim
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Congruence of Theorem 107 in the dimension bound

The assembly of [Kol07, Theorem 107]
(`Hironaka.Resolution.Algebraic.MarkedOrderReduction.Theorem107`) reads the dimension bound `n`
through the class proofs, through which input `BO_{n,d}` it applies — and, in Step 3, through the
phase count of the monomial run `realize` (`Hironaka.Monomial`). So two instances of the assembly,
at stages `n` and `n' ≤ n`, fed inputs `bo`, `bo'` that agree at EVERY order `d` on the triples of
both classes, take the same value at every marked triple of the smaller class:

* Step 1 (`step1_congr`) and Step 2 (`step2_congr`) of [Kol07, 111]: the rounds are the inputs'
  values at the round triples `(X, N(I), E)` and `(X, N(I)^m + I^s, E)` — equal by the agreement —
  and the loops are followed in lockstep by induction on a bound for the loop variable, the induced
  marked triple after a round transported along the equality of the rounds;
* Step 3 (`step3Seq_congr`): the input family `step3Family T` is the triple's, and the realized run
  does not depend on the bound (`PieceFamily.realize_eq_of_le`);
* the assembly (`bmoSeq_congr`, `functor_congr`, `data_congr`): the three steps concatenated, the
  triples after Steps 1 and 2 transported along the equalities of the steps.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Hironaka Scheme BlowUpSequence Hironaka.Sequence

namespace Hironaka.BMO

variable {k : Type u} [Field k] [CharZero k] {n n' m : ℕ} (bo : ∀ d : ℕ, BOData.{u} n d)
  (bo' : ∀ d : ℕ, BOData.{u} n' d)
  (hagree : ∀ (d : ℕ) (T : Triple k) (h₁ : Triple.BOClass n d T) (h₂ : Triple.BOClass n' d T),
    ((bo d).functor k).seq T h₁ = ((bo' d).functor k).seq T h₂)

section Step1

include hagree in
/-- A round of Step 1 of [Kol07, 111] at stages `n` and `n' ≤ n` is the same sequence — the inputs
agree at `(X, N(I), E)`. -/
theorem step1Round_congr (T : MarkedTriple k) (hT : T.BMOClass n m) (hT' : T.BMOClass n' m)
    (hd : m ≤ roundOrder T) : step1Round bo T hT hd = step1Round bo' T hT' hd :=
  hagree (roundOrder T) (nonmonomialTriple T) _ _

include hagree in
/-- The induction behind `step1_congr`: on a bound `l` for the loop variable, following the
recursion of `step1`. -/
theorem step1_congr_aux (l : ℕ) :
    ∀ (T : MarkedTriple k) (hT : T.BMOClass n m) (hT' : T.BMOClass n' m), roundOrder T ≤ l →
      (step1 bo T hT).1 = (step1 bo' T hT').1 := by
  induction l with
  | zero =>
    intro T hT hT' hl
    have hlt : roundOrder T < m := lt_of_le_of_lt hl hT.1
    rw [step1_of_lt bo T hT hlt, step1_of_lt bo' T hT' hlt]
  | succ l ih =>
    intro T hT hT' hl
    by_cases hd : m ≤ roundOrder T
    · rw [step1_of_le bo T hT hd, step1_of_le bo' T hT' hd]
      have e : step1Round bo' T hT' hd = step1Round bo T hT hd :=
        (step1Round_congr bo bo' hagree T hT hT' hd).symm
      have key : ∀ (S : BlowUpSequence T.X.left) (hS : S.IsOrderGeSeq
          (T.X.left ↘ Spec (.of k)) T.I T.m T.E) (_ : S = step1Round bo T hT hd)
          (c : (T.induced S hS (Fin.last _)).BMOClass n' m),
          S.concat (step1 bo' (T.induced S hS (Fin.last _)) c).1 =
            (step1Round bo T hT hd).concat
              (step1 bo (roundTriple bo T hT hd) (bmoClass_roundTriple bo T hT hd)).1 := by
        intro S hS e c
        subst e
        exact congrArg _ (ih (roundTriple bo T hT hd) (bmoClass_roundTriple bo T hT hd) c
          (Nat.lt_succ_iff.mp (lt_of_lt_of_le (roundOrder_roundTriple_lt bo T hT hd) hl))).symm
      exact (key _ (step1Round_isOrderGeSeq bo' T hT' hd) e
        (bmoClass_roundTriple bo' T hT' hd)).symm
    · have hlt : roundOrder T < m := not_le.mp hd
      rw [step1_of_lt bo T hT hlt, step1_of_lt bo' T hT' hlt]

include hagree in
/-- Congruence of Step 1 of [Kol07, 111] in the dimension bound: Step 1 at stages `n` and `n' ≤ n`,
from inputs agreeing at every order, coincides on a marked triple of both classes. -/
theorem step1_congr (T : MarkedTriple k) (hT : T.BMOClass n m) (hT' : T.BMOClass n' m) :
    (step1 bo T hT).1 = (step1 bo' T hT').1 :=
  step1_congr_aux bo bo' hagree (roundOrder T) T hT hT' le_rfl

end Step1

section Step2

include hagree in
/-- A round of Step 2 of [Kol07, 111] at stages `n` and `n' ≤ n` is the same sequence — the inputs
agree at `(X, N(I)^m + I^s, E)`. -/
theorem step2Round_congr (T : MarkedTriple k) (hT : T.BMOClass n m) (hT' : T.BMOClass n' m)
    (hs : 0 < sepOrder T) : step2Round bo T hT hs = step2Round bo' T hT' hs :=
  hagree (T.m * sepOrder T) (sepTriple T) _ _

include hagree in
/-- The induction behind `step2_congr`: on a bound `l` for the separation order, following the
recursion of `step2`. -/
theorem step2_congr_aux (l : ℕ) :
    ∀ (T : MarkedTriple k) (hT : T.BMOClass n m) (hT' : T.BMOClass n' m), sepOrder T ≤ l →
      (step2 bo T hT).1 = (step2 bo' T hT').1 := by
  induction l with
  | zero =>
    intro T hT hT' hl
    have h0 : sepOrder T = 0 := Nat.le_zero.mp hl
    rw [step2_of_eq_zero bo T hT h0, step2_of_eq_zero bo' T hT' h0]
  | succ l ih =>
    intro T hT hT' hl
    by_cases hs : 0 < sepOrder T
    · rw [step2_of_pos bo T hT hs, step2_of_pos bo' T hT' hs]
      have e : step2Round bo' T hT' hs = step2Round bo T hT hs :=
        (step2Round_congr bo bo' hagree T hT hT' hs).symm
      have key : ∀ (S : BlowUpSequence T.X.left) (hS : S.IsOrderGeSeq
          (T.X.left ↘ Spec (.of k)) T.I T.m T.E) (_ : S = step2Round bo T hT hs)
          (c : (T.induced S hS (Fin.last _)).BMOClass n' m),
          S.concat (step2 bo' (T.induced S hS (Fin.last _)) c).1 =
            (step2Round bo T hT hs).concat
              (step2 bo (step2Triple bo T hT hs) (bmoClass_step2Triple bo T hT hs)).1 := by
        intro S hS e c
        subst e
        exact congrArg _ (ih (step2Triple bo T hT hs) (bmoClass_step2Triple bo T hT hs) c
          (Nat.lt_succ_iff.mp (lt_of_lt_of_le (sepOrder_step2Triple_lt bo T hT hs) hl))).symm
      exact (key _ (step2Round_isOrderGeSeq bo' T hT' hs) e
        (bmoClass_step2Triple bo' T hT' hs)).symm
    · have h0 : sepOrder T = 0 := Nat.eq_zero_of_not_pos hs
      rw [step2_of_eq_zero bo T hT h0, step2_of_eq_zero bo' T hT' h0]

include hagree in
/-- Congruence of Step 2 of [Kol07, 111] in the dimension bound: Step 2 at stages `n` and `n' ≤ n`,
from inputs agreeing at every order, coincides on a marked triple of both classes. -/
theorem step2_congr (T : MarkedTriple k) (hT : T.BMOClass n m) (hT' : T.BMOClass n' m) :
    (step2 bo T hT).1 = (step2 bo' T hT').1 :=
  step2_congr_aux bo bo' hagree (sepOrder T) T hT hT' le_rfl

end Step2

section Step3

/-- Step 3 of [Kol07, 111] (order reduction for the monomial part) of a marked triple does not
depend on the dimension bound — `PieceFamily.realize_eq_of_le` on the triple's input family. -/
theorem step3Seq_congr (hle : n' ≤ n) (T : MarkedTriple k) (hT : T.BMOClass n m)
    (hT' : T.BMOClass n' m) : step3Seq T hT = step3Seq T hT' :=
  Hironaka.Monomial.PieceFamily.realize_eq_of_le (step3Family T) _ _ hle

end Step3

section Assembly

include hagree in
/-- Congruence of the assembled sequence `BMO_{n,m}(X, I, m, E)` of [Kol07, Theorem 107; 111] in the
dimension bound: at stages `n` and `n' ≤ n`, from inputs agreeing at every order, it coincides on a
marked triple of both classes — Step 1 by `step1_congr`, Step 2 on the (then equal) induced triple
by `step2_congr`, Step 3 by `step3Seq_congr`. -/
theorem bmoSeq_congr (hle : n' ≤ n) (T : MarkedTriple k) (hT : T.BMOClass n m)
    (hT' : T.BMOClass n' m) : bmoSeq bo T hT = bmoSeq bo' T hT' := by
  have keyB : ∀ (S₂ : BlowUpSequence (afterStep1 bo T hT).X.left)
      (hS₂ : S₂.IsOrderGeSeq ((afterStep1 bo T hT).X.left ↘ Spec (.of k)) (afterStep1 bo T hT).I
        (afterStep1 bo T hT).m (afterStep1 bo T hT).E)
      (_ : S₂ = (step2 bo (afterStep1 bo T hT) (bmoClass_afterStep1 bo T hT)).1)
      (c₂ : ((afterStep1 bo T hT).induced S₂ hS₂ (Fin.last _)).BMOClass n' m),
      S₂.concat (step3Seq ((afterStep1 bo T hT).induced S₂ hS₂ (Fin.last _)) c₂) =
        (step2 bo (afterStep1 bo T hT) (bmoClass_afterStep1 bo T hT)).1.concat
          (step3Seq (afterStep2 bo T hT) (bmoClass_afterStep2 bo T hT)) := by
    intro S₂ hS₂ e₂ c₂
    subst e₂
    exact congrArg _ (step3Seq_congr hle (afterStep2 bo T hT) (bmoClass_afterStep2 bo T hT) c₂).symm
  have keyA : ∀ (S₁ : BlowUpSequence T.X.left) (hS₁ : S₁.IsOrderGeSeq
    (T.X.left ↘ Spec (.of k)) T.I T.m T.E)
      (_ : S₁ = (step1 bo T hT).1) (c₁ : (T.induced S₁ hS₁ (Fin.last _)).BMOClass n' m),
      S₁.concat ((step2 bo' (T.induced S₁ hS₁ (Fin.last _)) c₁).1.concat
        (step3Seq ((T.induced S₁ hS₁ (Fin.last _)).induced
          (step2 bo' (T.induced S₁ hS₁ (Fin.last _)) c₁).1
          (step2_isOrderGeSeq bo' (T.induced S₁ hS₁ (Fin.last _)) c₁) (Fin.last _))
          (MarkedTriple.bmoClass_induced _ c₁ (step2_isOrderGeSeq bo' _ c₁) (Fin.last _)))) =
        bmoSeq bo T hT := by
    intro S₁ hS₁ e₁ c₁
    subst e₁
    exact congrArg _ (keyB _ (step2_isOrderGeSeq bo' (afterStep1 bo T hT) c₁)
      (step2_congr bo bo' hagree (afterStep1 bo T hT) (bmoClass_afterStep1 bo T hT) c₁).symm
      (MarkedTriple.bmoClass_induced _ c₁ (step2_isOrderGeSeq bo' _ c₁) (Fin.last _)))
  exact (keyA _ (step1_isOrderGeSeq bo' T hT') (step1_congr bo bo' hagree T hT hT').symm
    (bmoClass_afterStep1 bo' T hT')).symm

include hagree in
/-- Congruence of the functor of [Kol07, Theorem 107] in the dimension bound: `BMO_{n,m}` and
`BMO_{n',m}` (`n' ≤ n`), from inputs agreeing at every order, take the same value at a marked triple
of the smaller class. -/
theorem functor_congr (hle : n' ≤ n) (T : MarkedTriple k) (hT : T.BMOClass n m)
    (hT' : T.BMOClass n' m) : (functor bo m).seq T hT = (functor bo' m).seq T hT' :=
  bmoSeq_congr bo bo' hagree hle T hT hT'

end Assembly

/-- Congruence of [Kol07, Theorem 107] as data (`BMO.data`) in the dimension bound: at stages `n`
and `n' ≤ n`, from inputs agreeing at every order `d` on the triples of both classes, it takes the
same value at a marked triple of both classes. -/
theorem data_congr {n n' m : ℕ} (hle : n' ≤ n) (bo : ∀ d : ℕ, BOData.{u} n d)
    (bo' : ∀ d : ℕ, BOData.{u} n' d)
    (hboind : ∀ (d : ℕ) (k : Type u) [Field k] [CharZero k],
      ((bo d).functor k).IndifferentToEmptyMembers)
    (hboind' : ∀ (d : ℕ) (k : Type u) [Field k] [CharZero k],
      ((bo' d).functor k).IndifferentToEmptyMembers)
    (hagree : ∀ (d : ℕ) (k : Type u) [Field k] [CharZero k] (T : Triple k) (h₁ : T.BOClass n d)
      (h₂ : T.BOClass n' d), ((bo d).functor k).seq T h₁ = ((bo' d).functor k).seq T h₂)
    (k : Type u) [Field k] [CharZero k] (T : MarkedTriple k) (hT : T.BMOClass n m)
    (hT' : T.BMOClass n' m) :
    ((data bo hboind).functor k).seq T hT = ((data bo' hboind').functor k).seq T hT' :=
  bmoSeq_congr bo bo' (fun d T h₁ h₂ => hagree d k T h₁ h₂) hle T hT hT'

end Hironaka.BMO
