/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
import Hironaka.Resolution.Algebraic.Order.SupPow
import Hironaka.Scheme.BlowUp.Transform.StrictTransform
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.OrderAlongCenter
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.Snc.DictionaryOrder
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The marked transform of a sum of powers along a sequence of its own order

In the proof of Theorem 107 [Kol07, 111, Step 2], order reduction is applied to the ideal
`N(I)^m + I^s`, of order `≥ ms`, and every smooth blow-up sequence of order `ms` for it "is also a
smooth blow-up sequence of order `s`" for `N(I)` and one of order `m` for `I`. For
`J := A^m + B^s` and a blow-up of order exactly
`ms` for `J` with center `Z`: `ord_Z A ≥ s` and `ord_Z B ≥ m` (Kollár's observation
`ord_Z J_1 ≥ s ∧ ord_Z J_2 ≥ m ⇔ ord_Z (J_1^m + J_2^s) ≥ ms`,
`Hironaka/Resolution/Algebraic/Order/SupPow.lean`), so `F^s ∣ π^* A` and `F^m ∣ π^* B`, and
`π^{-1}_*(J, ms) = π^{-1}_*(A, s)^m + π^{-1}_*(B, m)^s`: both sides, multiplied by `F^{ms}`, are
`π^* J = (F^s π^{-1}_*(A, s))^m + (F^m π^{-1}_*(B, m))^s`, and the quotient by the invertible
`F^{ms}` is unique. Along the sequence the identity propagates (the birational transform at the
exact order is the marked transform, `weakTransform_eq_markedTransform_of_smooth`), and the order
clause of [Kol07, Definition 66] for `J` at each center gives the clauses for `(A, s)` and `(B, m)`
by the same observation, with the same centers and the same boundaries.

* `markedTransform_pow_sup_pow`: one blow-up.
* `weakTransformSeq_pow_sup_pow`: the identity at every stage of a smooth blow-up sequence of
  order `ms` for `A^m + B^s`.
* `isOrderGeSeq_of_isOrderSeq_pow_sup_pow_left`/`_right`: the sequence is of order `≥ s` for
  `(A, s)` and of order `≥ m` for `(B, m)`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme.IdealSheafData
  Scheme BlowUpSequence

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {X : Scheme.{u}}

/-- When `F^s ∣ π^* A` and `F^m ∣ π^* B` (Kollár's `ord_Z A ≥ s`, `ord_Z B ≥ m`), the marked
transform of `A^m + B^s` at the mark `ms` is `π^{-1}_*(A, s)^m + π^{-1}_*(B, m)^s`: both are the
unique `K` with `F^{ms} · K = π^*(A^m + B^s)` [Kol07, 111, Step 2]. This is an identity of ideal
sheaves on the blow-up of any scheme along `D`, given the two divisibilities; no smoothness
enters. -/
theorem markedTransform_pow_sup_pow (D A B : X.IdealSheafData) (m s : ℕ)
    (hA : D.exceptionalDivisor ^ s ∣ A.comap D.blowUpπ)
    (hB : D.exceptionalDivisor ^ m ∣ B.comap D.blowUpπ) :
    (A ^ m ⊔ B ^ s).markedTransform D (m * s) =
      A.markedTransform D s ^ m ⊔ B.markedTransform D m ^ s := by
  symm
  refine eq_markedTransform_of_pow_mul_eq D (A ^ m ⊔ B ^ s) (m * s) _ ?_
  rw [comap_sup, comap_pow, comap_pow, ← pow_mul_markedTransform D A s hA,
    ← pow_mul_markedTransform D B m hB, mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm s m]
  exact mul_add _ _ _

section Sequence

variable {k : Type u} [Field k] [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ)
  [SmoothOfRelativeDimension n f]

include n in
/-- Along a smooth blow-up sequence of order `ms` for `A^m + B^s` (`m, s ≥ 1`), at every stage
the induced birational transform of `A^m + B^s` is `π^{-1}_*(A, s)_i^m + π^{-1}_*(B, m)_i^s`
[Kol07, 111, Step 2]. By recursion on the sequence: at each center the order clause gives
`ord_Z A_i ≥ s` and `ord_Z B_i ≥ m`, the birational transform at the exact order `ms` is the
marked transform, and `markedTransform_pow_sup_pow` applies. -/
theorem weakTransformSeq_pow_sup_pow {A B : X.IdealSheafData} {E : DivisorFamily X} {m s : ℕ}
    (hm : 1 ≤ m) (hs : 1 ≤ s) {S : BlowUpSequence X}
    (hS : S.IsOrderSeq f (A ^ m ⊔ B ^ s) E (m * s)) (i : Fin (S.length + 1)) :
    S.weakTransformSeq (A ^ m ⊔ B ^ s) i =
      S.markedTransformSeq A s i ^ m ⊔ S.markedTransformSeq B m i ^ s := by
  induction S with
  | nil Y => rfl
  | cons Y D rest ih =>
    obtain ⟨⟨hD, -, hord⟩, ht⟩ := (isOrderSeq_cons_iff f (A ^ m ⊔ B ^ s) E (m * s) D rest).1 hS
    have hsm : Smooth f := SmoothOfRelativeDimension.smooth n f
    have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) := by
      have := hD
      exact smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
    have hAB := (leOrdAlong_pow_sup_pow_iff f n A B D.support hm hs).mp
      fun η hη => (hord η hη).ge
    have := hD
    have hdA : D.exceptionalDivisor ^ s ∣ A.comap D.blowUpπ :=
      pow_dvd_comap_of_leOrdAlong f n D A hAB.1
    have hdB : D.exceptionalDivisor ^ m ∣ B.comap D.blowUpπ :=
      pow_dvd_comap_of_leOrdAlong f n D B hAB.2
    have hw : (A ^ m ⊔ B ^ s).weakTransform D =
        A.markedTransform D s ^ m ⊔ B.markedTransform D m ^ s := by
      rw [weakTransform_eq_markedTransform_of_smooth f n D (A ^ m ⊔ B ^ s) hord]
      exact markedTransform_pow_sup_pow D A B m s hdA hdB
    rcases i with ⟨_ | j, hi⟩
    · rfl
    · have ht' := ht
      rw [hw] at ht'
      change rest.weakTransformSeq ((A ^ m ⊔ B ^ s).weakTransform D)
          ⟨j, Nat.lt_of_succ_lt_succ hi⟩ =
        rest.markedTransformSeq (A.markedTransform D s) s ⟨j, Nat.lt_of_succ_lt_succ hi⟩ ^ m ⊔
          rest.markedTransformSeq (B.markedTransform D m) m ⟨j, Nat.lt_of_succ_lt_succ hi⟩ ^ s
      rw [hw]
      exact ih (D.blowUpπ ≫ f) ht' ⟨j, Nat.lt_of_succ_lt_succ hi⟩

include n in
/-- "Also a smooth blow-up sequence of order `s` starting with `N(I)`" [Kol07, 111, Step 2]: a
smooth blow-up sequence of order `ms` for `A^m + B^s` is a smooth blow-up sequence of order `≥ s`
for the marked ideal `(A, s)`; same centers, same boundaries, and the order clause at every stage
from `ord_Z (A^m + B^s) ≥ ms`. -/
theorem isOrderGeSeq_of_isOrderSeq_pow_sup_pow_left {A B : X.IdealSheafData} {E : DivisorFamily X}
    {m s : ℕ} (hm : 1 ≤ m) (hs : 1 ≤ s) {S : BlowUpSequence X}
    (hS : S.IsOrderSeq f (A ^ m ⊔ B ^ s) E (m * s)) : S.IsOrderGeSeq f A s E :=
  ⟨hS.1, fun i => ⟨(hS.2 i).1, by
    have hsm : SmoothOfRelativeDimension n (S.stageMap i.castSucc ≫ f) :=
      IsSmooth.stageMap_smoothOfRelativeDimension hS.1 i.castSucc
    have h := (hS.2 i).2
    rw [weakTransformSeq_pow_sup_pow f n hm hs hS i.castSucc] at h
    exact ((leOrdAlong_pow_sup_pow_iff (S.stageMap i.castSucc ≫ f) n _ _ _ hm hs).mp
      fun η hη => (h η hη).ge).1⟩⟩

include n in
/-- "And a smooth blow-up sequence of order `m` starting with `I`" [Kol07, 111, Step 2]: a smooth
blow-up sequence of order `ms` for `A^m + B^s` is a smooth blow-up sequence of order `≥ m` for the
marked ideal `(B, m)`. -/
theorem isOrderGeSeq_of_isOrderSeq_pow_sup_pow_right {A B : X.IdealSheafData} {E : DivisorFamily X}
    {m s : ℕ} (hm : 1 ≤ m) (hs : 1 ≤ s) {S : BlowUpSequence X}
    (hS : S.IsOrderSeq f (A ^ m ⊔ B ^ s) E (m * s)) : S.IsOrderGeSeq f B m E :=
  ⟨hS.1, fun i => ⟨(hS.2 i).1, by
    have hsm : SmoothOfRelativeDimension n (S.stageMap i.castSucc ≫ f) :=
      IsSmooth.stageMap_smoothOfRelativeDimension hS.1 i.castSucc
    have h := (hS.2 i).2
    rw [weakTransformSeq_pow_sup_pow f n hm hs hS i.castSucc] at h
    exact ((leOrdAlong_pow_sup_pow_iff (S.stageMap i.castSucc ≫ f) n _ _ _ hm hs).mp
      fun η hη => (h η hη).ge).2⟩⟩

end Sequence

end Hironaka.Sequence
