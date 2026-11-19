/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
public import Hironaka.Scheme.IdealSheaf.Order.Constructible
import Hironaka.Algebra.Local.Regular
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.OrderAlongCenter
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.IdealSheaf.Order.Lemma61
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
/-!
# Remark 67: passing between the marked and the unmarked versions

[Kol07, Remark 67]: if `max-ord I = m`, then in any blow-up sequence of order `≥ m` starting with
`(X, I, m, E)` one has `max-ord I_i ≤ m` by Lemma 61, so every blow-up has order exactly `m`;
deleting the mark therefore gives a blow-up sequence of order `m` starting with `(X, I, E)`, "and
the converse also holds".

**One step.** Along a smooth center `D` with `ord_D I ≥ m` at every generic point and
`max-ord I ≤ m`, the order along `D` is exactly `m` (`ord_η I ≤ max-ord I ≤ m`), so the marked
transform is the weak transform (`weakTransform_eq_markedTransform_of_smooth`), and its `max-ord` is
again `≤ m`: by [Kol07, Lemma 61] for a smooth center of any shape when `D` is nonempty (then some
generic point exists and `max-ord I = m` exactly), and trivially when `D = ∅` (the blow-up is an
isomorphism and no point lies over the center, `ord_controlledTransform_le_of_notMem`).

**Along the sequence.** The invariant `max-ord I_i ≤ m` propagates by induction on the sequence with
the one-step lemma; it gives `ord_{Z_i} I_i = m` at every stage, the stagewise equality of the
marked and the unmarked induced ideals, and the equivalence of the two notions of a sequence for
`(X, I, E)` with `max-ord I = m`. The converse direction needs no bound on `max-ord`: `ord_{Z_i} I_i
= m` already makes the marked and unmarked transforms agree at every stage.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme.IdealSheafData
  Scheme BlowUpSequence IdealSheafData AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The order along a closed subscheme is exactly `m` when it is `≥ m` and `max-ord I ≤ m`. -/
theorem ordAlongEq_of_leOrdAlong_of_maxOrd_le (D I : X.IdealSheafData) {m : ℕ} (hI : I.maxOrd ≤ m)
    (hord : I.LeOrdAlong D.support (m : ℕ∞)) : I.OrdAlongEq D.support (m : ℕ∞) :=
  fun η hη => le_antisymm ((I.le_maxOrd η).trans hI) (hord η hη)

variable {k : Type u} [Field k] [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ)
  [SmoothOfRelativeDimension n f]

include f n

section OneStep

variable (D I : X.IdealSheafData) {m : ℕ}

/-- One step of [Kol07, Remark 67] ("`max-ord I_i ≤ m` by (61)"): along a smooth center of any
shape with `ord_D I ≥ m` and `max-ord I ≤ m`, the marked transform has `max-ord ≤ m`. -/
theorem maxOrd_markedTransform_le (hD : Smooth (D.subschemeι ≫ f)) (hI : I.maxOrd ≤ m)
    (hord : I.LeOrdAlong D.support (m : ℕ∞)) : (I.markedTransform D m).maxOrd ≤ m := by
  have := hD
  have hs : Smooth f := SmoothOfRelativeDimension.smooth n f
  by_cases hne : ∃ z, z ∈ D.support
  · obtain ⟨z, hz⟩ := hne
    have hP := isPrime_stalkIdeal_of_smooth f n D hz
    have hreg := isRegularLocalRing_stalk f z
    obtain ⟨η, hη, -, -, -, -⟩ := exists_genericPoint_of_isPrime_stalkIdeal D z
    have hmax : I.maxOrd = m := le_antisymm hI ((hord η hη).trans (I.le_maxOrd η))
    exact maxOrd_controlledTransform_le_of_smooth f n D I
      (ordAlongEq_of_leOrdAlong_of_maxOrd_le D I hI hord) hmax
  · have hne' : ∀ z, z ∉ D.support := fun z hz => hne ⟨z, hz⟩
    refine (maxOrd_le_iff _).mpr fun q => ?_
    have h2 : (I.controlledTransformAlong D.blowUpπ D.exceptionalDivisor m).ord q ≤
        I.ord (D.blowUpπ q) :=
      ord_controlledTransform_le_of_notMem D I m q (hne' _)
    exact h2.trans ((I.le_maxOrd _).trans hI)

end OneStep

section Sequence

variable {I : X.IdealSheafData} {E : DivisorFamily X} {m : ℕ} {S : BlowUpSequence X}

/-- The invariant of [Kol07, Remark 67] along the sequence: with `max-ord I ≤ m`, every induced
marked ideal has `max-ord ≤ m`. -/
theorem maxOrd_markedTransformSeq_le (hI : I.maxOrd ≤ m) (h : S.IsOrderGeSeq f I m E)
    (i : Fin (S.length + 1)) : (S.markedTransformSeq I m i).maxOrd ≤ m := by
  induction S with
  | nil Y => exact hI
  | cons Y D rest ih =>
    obtain ⟨⟨hD, -, hord⟩, ht⟩ := (isOrderGeSeq_cons_iff f I E m D rest).1 h
    have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) := by
      have := hD
      exact smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
    rcases i with ⟨_ | j, hi⟩
    · exact hI
    · exact ih (D.blowUpπ ≫ f) (maxOrd_markedTransform_le f n D I hD hI hord) ht
        ⟨j, Nat.lt_of_succ_lt_succ hi⟩

/-- [Kol07, Remark 67] along the sequence: with `max-ord I ≤ m`, the marked and the unmarked
induced ideals coincide at every stage. -/
theorem markedTransformSeq_eq_weakTransformSeq_of_maxOrd_le (hI : I.maxOrd ≤ m)
    (h : S.IsOrderGeSeq f I m E) (i : Fin (S.length + 1)) :
    S.markedTransformSeq I m i = S.weakTransformSeq I i := by
  induction S with
  | nil Y => rfl
  | cons Y D rest ih =>
    obtain ⟨⟨hD, -, hord⟩, ht⟩ := (isOrderGeSeq_cons_iff f I E m D rest).1 h
    have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) := by
      have := hD
      exact smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
    have heq : I.markedTransform D m = I.weakTransform D := by
      have := hD
      exact (weakTransform_eq_markedTransform_of_smooth f n D I
        (ordAlongEq_of_leOrdAlong_of_maxOrd_le D I hI hord)).symm
    have hmax := maxOrd_markedTransform_le f n D I hD hI hord
    rw [heq] at ht hmax
    rcases i with ⟨_ | j, hi⟩
    · rfl
    · change rest.markedTransformSeq (I.markedTransform D m) m ⟨j, Nat.lt_of_succ_lt_succ hi⟩ =
        rest.weakTransformSeq (I.weakTransform D) ⟨j, Nat.lt_of_succ_lt_succ hi⟩
      rw [heq]
      exact ih (D.blowUpπ ≫ f) hmax ht ⟨j, Nat.lt_of_succ_lt_succ hi⟩

/-- "`max-ord I_i ≤ m` by (61)" [Kol07, Remark 67]: along a sequence of order `≥ m` for
`(X, I, m, E)` with `max-ord I = m`, every induced marked ideal has `max-ord ≤ m`. -/
theorem IsOrderGeSeq.maxOrd_le (hI : I.maxOrd = m) (h : S.IsOrderGeSeq f I m E)
    (i : Fin (S.length + 1)) : (S.markedTransformSeq I m i).maxOrd ≤ m :=
  maxOrd_markedTransformSeq_le f n hI.le h i

/-- "And so every blow-up has order `= m`" [Kol07, Remark 67]: along a sequence of order `≥ m`
for `(X, I, m, E)` with `max-ord I = m`, the order of `I_i` along every center is exactly `m`. -/
theorem IsOrderGeSeq.ordAlongEq (hI : I.maxOrd = m) (h : S.IsOrderGeSeq f I m E)
    (i : Fin S.length) :
    (S.markedTransformSeq I m i.castSucc).OrdAlongEq (S.center i).support (m : ℕ∞) :=
  ordAlongEq_of_leOrdAlong_of_maxOrd_le (S.center i) _
    (maxOrd_markedTransformSeq_le f n hI.le h i.castSucc) (IsOrderGeSeq.leOrdAlong h i)

/-- The marked and the unmarked transforms coincide at every stage of a sequence of order `≥ m`
for `(X, I, m, E)` with `max-ord I = m` [Kol07, Remark 67]. -/
theorem IsOrderGeSeq.markedTransformSeq_eq_weakTransformSeq (hI : I.maxOrd = m)
    (h : S.IsOrderGeSeq f I m E) (i : Fin (S.length + 1)) :
    S.markedTransformSeq I m i = S.weakTransformSeq I i :=
  markedTransformSeq_eq_weakTransformSeq_of_maxOrd_le f n hI.le h i

/-- "The converse also holds" [Kol07, Remark 67]: along a sequence of order `m` for `(X, I, E)`
the marked transforms with mark `m` coincide with the unmarked ones. -/
theorem IsOrderSeq.markedTransformSeq_eq_weakTransformSeq (h : S.IsOrderSeq f I E m)
    (i : Fin (S.length + 1)) : S.markedTransformSeq I m i = S.weakTransformSeq I i := by
  induction S with
  | nil Y => rfl
  | cons Y D rest ih =>
    obtain ⟨⟨hD, -, hord⟩, ht⟩ := (isOrderSeq_cons_iff f I E m D rest).1 h
    have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) := by
      have := hD
      exact smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
    have heq : I.markedTransform D m = I.weakTransform D := by
      have := hD
      exact (weakTransform_eq_markedTransform_of_smooth f n D I hord).symm
    rcases i with ⟨_ | j, hi⟩
    · rfl
    · change rest.markedTransformSeq (I.markedTransform D m) m ⟨j, Nat.lt_of_succ_lt_succ hi⟩ =
        rest.weakTransformSeq (I.weakTransform D) ⟨j, Nat.lt_of_succ_lt_succ hi⟩
      rw [heq]
      exact ih (D.blowUpπ ≫ f) ht ⟨j, Nat.lt_of_succ_lt_succ hi⟩

/-- For `max-ord I = m`, a smooth blow-up sequence is of order `≥ m` for `(X, I, m, E)` iff it is
of order `m` for `(X, I, E)` [Kol07, Remark 67]. -/
theorem isOrderGeSeq_iff_isOrderSeq (hI : I.maxOrd = m) :
    S.IsOrderGeSeq f I m E ↔ S.IsOrderSeq f I E m := by
  constructor
  · intro h
    refine ⟨IsOrderGeSeq.isSmooth h, fun i => ⟨IsOrderGeSeq.hasSncWith h i, ?_⟩⟩
    have := IsOrderGeSeq.ordAlongEq f n hI h i
    rwa [IsOrderGeSeq.markedTransformSeq_eq_weakTransformSeq f n hI h i.castSucc] at this
  · intro h
    refine ⟨IsOrderSeq.isSmooth h, fun i => ⟨IsOrderSeq.hasSncWith h i, ?_⟩⟩
    have := IsOrderSeq.ordAlongEq h i
    rw [← IsOrderSeq.markedTransformSeq_eq_weakTransformSeq f n h i.castSucc] at this
    exact fun η hη => (this η hη).ge

end Sequence

end AlgebraicGeometry
