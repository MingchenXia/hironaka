/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Pushforward
import Hironaka.Scheme.BlowUpSequence.InducedData
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Truncation of a blow-up sequence

The proof of the going-up theorem for D-balanced ideals [Kol07, 90, the proof of Theorem 84]
proceeds "by induction, assum[ing] that this already holds for blow-up sequences of length
`< r`", and applies the hypothesis to the prefix `Π_{r−1} : X_{r−1} → X` of the pushed-forward
sequence. `BlowUpSequence` is a list of centers built from the front, so the prefix has to be
built: `S.take k` keeps the first `k` blow-ups (all of them if `k ≥ S.length`). This module
records its bookkeeping:

* `take`, with `length_take` and `pushforward_take`
  (`(T.take k).pushforward j = (T.pushforward j).take k`);
* the prefix has the same stages, centers, structure maps and induced data as the sequence at
  every index it has: `stage_take_mk` (an equality of schemes), and `HEq` transports of
  `markedTransformSeq`, `weakTransformSeq`, `totalTransformSeq`, `strictTransformSeq`, `center`,
  `stageMap` and of the stage inclusions `pushforwardStageHom` of
  `Hironaka/Scheme/BlowUpSequence/Pushforward.lean`; heterogeneous because the stage types differ
  syntactically; stated on explicit indices `⟨j, hj⟩`;
* the prefix of a smooth sequence is smooth, the prefix of a sequence of order `≥ m` is of order
  `≥ m`, and, in the form the induction of the going-up theorem uses, the prefix of length `k` is
  of order `≥ m` as soon as the smoothness, normal-crossing and order clauses hold at the stages
  `< k` (`isOrderGeSeq_take_of_forall_lt`);
* two transport helpers for points and orders along an equality of schemes (`ord_cast_of_heq`,
  `apply_cast_of_heq`).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme IdealSheafData
  Scheme.Hom BlowUpSequence Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.BlowUpSequence


variable {X : Scheme.{u}}

/-- The first `k` blow-ups of a sequence (all of them if `k ≥ length`): the prefix `Π_{r−1}` of
[Kol07, 90, the proof of Theorem 84]. -/
noncomputable def take : {X : Scheme.{u}} → BlowUpSequence X → ℕ → BlowUpSequence X
  | X, nil _, _ => nil X
  | X, cons _ _ _, 0 => nil X
  | _, cons X D rest, k + 1 => cons X D (rest.take k)

@[simp] theorem take_nil (k : ℕ) : (nil X).take k = nil X := rfl

@[simp] theorem take_cons_zero (D : X.IdealSheafData) (rest : BlowUpSequence
    D.blowUp) :
    (cons X D rest).take 0 = nil X := rfl

@[simp] theorem take_cons_succ (D : X.IdealSheafData) (rest : BlowUpSequence
    D.blowUp)
    (k : ℕ) : (cons X D rest).take (k + 1) = cons X D (rest.take k) := rfl

end AlgebraicGeometry.Scheme.BlowUpSequence

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-! ### Length and pushforward -/

theorem length_take (S : BlowUpSequence X) (k : ℕ) : (S.take k).length = min k S.length := by
  induction S generalizing k with
  | nil _ => simp [length]
  | cons X D rest ih =>
    cases k with
    | zero => simp [length]
    | succ k =>
      change (rest.take k).length + 1 = min (k + 1) (rest.length + 1)
      rw [ih k]
      omega

theorem length_take_of_le (S : BlowUpSequence X) {k : ℕ} (hk : k ≤ S.length) :
    (S.take k).length = k := by
  rw [length_take, Nat.min_eq_left hk]

theorem take_of_length_le (S : BlowUpSequence X) {k : ℕ} (hk : S.length ≤ k) : S.take k = S := by
  induction S generalizing k with
  | nil _ => rfl
  | cons X D rest ih =>
    cases k with
    | zero => exact absurd hk (Nat.not_succ_le_zero _)
    | succ k => exact congrArg (cons X D) (ih (Nat.le_of_succ_le_succ hk))

/-- Truncation commutes with the pushforward along a closed immersion. -/
theorem pushforward_take (T : BlowUpSequence Y) (j : Y ⟶ X) [IsClosedImmersion j] (k : ℕ) :
    (T.take k).pushforward j = (T.pushforward j).take k := by
  induction T generalizing X k with
  | nil _ => rfl
  | cons Y Z rest ih =>
    cases k with
    | zero => rfl
    | succ k => exact congrArg (cons X (Z.map j)) (ih (pushforwardBlowUp j Z) k)

/-! ### The prefix has the same stages and induced data -/

theorem stage_take_mk (S : BlowUpSequence X) (k j : ℕ) (hj : j < (S.take k).length + 1)
    (hj' : j < S.length + 1) : (S.take k).stage ⟨j, hj⟩ = S.stage ⟨j, hj'⟩ := by
  induction S generalizing k j with
  | nil _ => rfl
  | cons X D rest ih =>
    cases k with
    | zero =>
      cases j with
      | zero => rfl
      | succ j => exact absurd hj (by simp [length])
    | succ k =>
      cases j with
      | zero => rfl
      | succ j => exact ih k j (Nat.lt_of_succ_lt_succ hj) (Nat.lt_of_succ_lt_succ hj')

theorem markedTransformSeq_take_heq_mk (S : BlowUpSequence X) (J : X.IdealSheafData) (c k j : ℕ)
    (hj : j < (S.take k).length + 1) (hj' : j < S.length + 1) :
    HEq ((S.take k).markedTransformSeq J c ⟨j, hj⟩) (S.markedTransformSeq J c ⟨j, hj'⟩) := by
  induction S generalizing k j with
  | nil _ => rfl
  | cons X D rest ih =>
    cases k with
    | zero =>
      cases j with
      | zero => rfl
      | succ j => exact absurd hj (by simp [length])
    | succ k =>
      cases j with
      | zero => rfl
      | succ j =>
        exact ih (J.markedTransform D c) k j (Nat.lt_of_succ_lt_succ hj)
          (Nat.lt_of_succ_lt_succ hj')

theorem weakTransformSeq_take_heq_mk (S : BlowUpSequence X) (J : X.IdealSheafData) (k j : ℕ)
    (hj : j < (S.take k).length + 1) (hj' : j < S.length + 1) :
    HEq ((S.take k).weakTransformSeq J ⟨j, hj⟩) (S.weakTransformSeq J ⟨j, hj'⟩) := by
  induction S generalizing k j with
  | nil _ => rfl
  | cons X D rest ih =>
    cases k with
    | zero =>
      cases j with
      | zero => rfl
      | succ j => exact absurd hj (by simp [length])
    | succ k =>
      cases j with
      | zero => rfl
      | succ j =>
        exact ih (J.weakTransform D) k j (Nat.lt_of_succ_lt_succ hj) (Nat.lt_of_succ_lt_succ hj')

theorem totalTransformSeq_take_heq_mk (S : BlowUpSequence X) (E : DivisorFamily X) (k j : ℕ)
    (hj : j < (S.take k).length + 1) (hj' : j < S.length + 1) :
    HEq ((S.take k).totalTransformSeq E ⟨j, hj⟩) (S.totalTransformSeq E ⟨j, hj'⟩) := by
  induction S generalizing k j with
  | nil _ => rfl
  | cons X D rest ih =>
    cases k with
    | zero =>
      cases j with
      | zero => rfl
      | succ j => exact absurd hj (by simp [length])
    | succ k =>
      cases j with
      | zero => rfl
      | succ j =>
        exact ih (E.totalTransform D) k j (Nat.lt_of_succ_lt_succ hj) (Nat.lt_of_succ_lt_succ hj')

theorem strictTransformSeq_take_heq_mk (S : BlowUpSequence X) (J : X.IdealSheafData) (k j : ℕ)
    (hj : j < (S.take k).length + 1) (hj' : j < S.length + 1) :
    HEq ((S.take k).strictTransformSeq J ⟨j, hj⟩) (S.strictTransformSeq J ⟨j, hj'⟩) := by
  induction S generalizing k j with
  | nil _ => rfl
  | cons X D rest ih =>
    cases k with
    | zero =>
      cases j with
      | zero => rfl
      | succ j => exact absurd hj (by simp [length])
    | succ k =>
      cases j with
      | zero => rfl
      | succ j =>
        exact ih (J.strictTransform D) k j (Nat.lt_of_succ_lt_succ hj)
          (Nat.lt_of_succ_lt_succ hj')

theorem center_take_heq_mk (S : BlowUpSequence X) (k j : ℕ) (hj : j < (S.take k).length)
    (hj' : j < S.length) : HEq ((S.take k).center ⟨j, hj⟩) (S.center ⟨j, hj'⟩) := by
  induction S generalizing k j with
  | nil _ => exact absurd hj (Nat.not_lt_zero _)
  | cons X D rest ih =>
    cases k with
    | zero => exact absurd hj (by simp [length])
    | succ k =>
      cases j with
      | zero => rfl
      | succ j => exact ih k j (Nat.lt_of_succ_lt_succ hj) (Nat.lt_of_succ_lt_succ hj')

/-- Heterogeneously equal morphisms stay heterogeneously equal after composing with a fixed
morphism (the sources are equal schemes). -/
theorem heq_comp_right {A B Y Z : Scheme.{u}} (e : A = B) {a : A ⟶ Y} {b : B ⟶ Y} (h : HEq a b)
    (g : Y ⟶ Z) : HEq (a ≫ g) (b ≫ g) := by
  subst e
  cases h
  rfl

theorem stageMap_take_heq_mk (S : BlowUpSequence X) (k j : ℕ) (hj : j < (S.take k).length + 1)
    (hj' : j < S.length + 1) : HEq ((S.take k).stageMap ⟨j, hj⟩) (S.stageMap ⟨j, hj'⟩) := by
  induction S generalizing k j with
  | nil _ => rfl
  | cons X D rest ih =>
    cases k with
    | zero =>
      cases j with
      | zero => rfl
      | succ j => exact absurd hj (by simp [length])
    | succ k =>
      cases j with
      | zero => rfl
      | succ j =>
        change HEq ((rest.take k).stageMap ⟨j, _⟩ ≫ D.blowUpπ)
          (rest.stageMap ⟨j, _⟩ ≫ D.blowUpπ)
        exact heq_comp_right (stage_take_mk rest k j (Nat.lt_of_succ_lt_succ hj)
          (Nat.lt_of_succ_lt_succ hj')) (ih k j _ _) D.blowUpπ

/-- The stage inclusions of the prefix into the pushed-forward stages are those of the sequence. -/
theorem pushforwardStageHom_take_heq_mk (T : BlowUpSequence Y) (j : Y ⟶ X) [IsClosedImmersion j]
    (k n : ℕ) (hn : n < (T.take k).length + 1) (hn' : n < T.length + 1) :
    HEq ((T.take k).pushforwardStageHom j ⟨n, hn⟩) (T.pushforwardStageHom j ⟨n, hn'⟩) := by
  induction T generalizing X k n with
  | nil _ => rfl
  | cons Y Z rest ih =>
    cases k with
    | zero =>
      cases n with
      | zero => rfl
      | succ n => exact absurd hn (by simp [length])
    | succ k =>
      cases n with
      | zero => rfl
      | succ n =>
        exact ih (pushforwardBlowUp j Z) k n (Nat.lt_of_succ_lt_succ hn)
          (Nat.lt_of_succ_lt_succ hn')

/-! ### Smoothness and order pass to the prefix -/

section Order

variable {k : Type u} [Field k] (f : X ⟶ Spec (.of k))

theorem isSmooth_take {S : BlowUpSequence X} (h : S.IsSmooth f) (l : ℕ) :
    (S.take l).IsSmooth f := by
  induction S generalizing l with
  | nil _ => exact isSmooth_nil f
  | cons X D rest ih =>
    cases l with
    | zero => exact isSmooth_nil f
    | succ l =>
      rw [isSmooth_cons_iff] at h
      change (cons X D (rest.take l)).IsSmooth f
      rw [isSmooth_cons_iff]
      exact ⟨h.1, ih _ h.2 l⟩

variable (I : X.IdealSheafData) (m : ℕ) (E : DivisorFamily X)

/-- The prefix of length `l` is a smooth blow-up sequence of order `≥ m` for `(X, I, m, E)` as soon
as the sequence is smooth and its normal-crossing and order clauses hold at the stages `< l`; the
form in which the induction hypothesis of [Kol07, 90] is applied. -/
theorem isOrderGeSeq_take_of_forall_lt (S : BlowUpSequence X) (hsm : S.IsSmooth f) (l : ℕ)
    (hlt : ∀ i : Fin S.length, i.val < l →
      (S.totalTransformSeq E i.castSucc).HasSncWith (S.center i) ∧
        (S.markedTransformSeq I m i.castSucc).LeOrdAlong (S.center i).support (m : ℕ∞)) :
    (S.take l).IsOrderGeSeq f I m E := by
  induction S generalizing l with
  | nil _ =>
    change (nil _).IsOrderGeSeq f I m E
    exact isOrderGeSeq_nil f I E m
  | cons X D rest ih =>
    cases l with
    | zero =>
      change (nil _).IsOrderGeSeq f I m E
      exact isOrderGeSeq_nil f I E m
    | succ l =>
      rw [isSmooth_cons_iff] at hsm
      change (cons X D (rest.take l)).IsOrderGeSeq f I m E
      rw [isOrderGeSeq_cons_iff]
      have h0 := hlt ⟨0, Nat.succ_pos _⟩ (Nat.succ_pos _)
      refine ⟨⟨hsm.1, h0.1, h0.2⟩, ?_⟩
      refine ih (D.blowUpπ ≫ f) (I.markedTransform D m)
          (E.totalTransform D) hsm.2 l ?_
      intro i hi
      exact hlt ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ (Nat.succ_lt_succ hi)

/-- The prefix of a sequence of order `≥ m` is of order `≥ m`. -/
theorem isOrderGeSeq_take {S : BlowUpSequence X} (h : S.IsOrderGeSeq f I m E) (l : ℕ) :
    (S.take l).IsOrderGeSeq f I m E :=
  isOrderGeSeq_take_of_forall_lt f I m E S h.1 l fun i _ => h.2 i

end Order

/-! ### Transport along an equality of schemes -/

/-- The order of heterogeneously equal ideal sheaves at corresponding points. -/
theorem ord_cast_of_heq {X X' : Scheme.{u}} (e : X = X') {J : X.IdealSheafData}
    {J' : X'.IdealSheafData} (h : HEq J J') (x : X) :
    J'.ord (cast (congrArg (fun S : Scheme.{u} => (S : Type u)) e) x) = J.ord x := by
  subst e
  cases h
  rfl

/-- Heterogeneously equal morphisms agree at corresponding points. -/
theorem apply_cast_of_heq {X X' Y Y' : Scheme.{u}} (eX : X = X') (eY : Y = Y') {φ : X ⟶ Y}
    {φ' : X' ⟶ Y'} (h : HEq φ φ') (x : X) :
    φ' (cast (congrArg (fun S : Scheme.{u} => (S : Type u)) eX) x) =
      cast (congrArg (fun S : Scheme.{u} => (S : Type u)) eY) (φ x) := by
  subst eX
  subst eY
  cases h
  rfl

end AlgebraicGeometry
