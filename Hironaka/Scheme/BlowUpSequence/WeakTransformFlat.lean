/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
public import Hironaka.Scheme.BlowUpSequence.Pullback
import Hironaka.Scheme.BlowUpSequence.EraseEmptyTransport
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.OrderAlongCenter
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The weak transform along a flat pull-back of order sequences

Along a change of fields [Kol07, 34.2] the induced ideals of the base-changed sequence of order
`m` [Kol07, Definition 66] are the pull-backs of the induced ideals.
`Hironaka/Scheme/BlowUpSequence/Pullback.lean` proves this for a smooth `h`
(`IsOrderSeq.weakTransformSeq_pullback`) and `Hironaka/Scheme/BlowUpSequence/BaseChange.lean` for
the base-change square with `Spec.map σ` (`weakTransformSeq_pullback_of_isPullback_specMap`). This
module states the common core for a flat
`p : Y ⟶ X` between two smooth equidimensional bases, both sequences being sequences of order `m`:
at every step the weak transform is the marked transform with mark `m`
(`weakTransform_eq_markedTransform_of_smooth`, on both sides; the order condition on the
pulled-back side is a hypothesis, not derived), and the marked transform commutes with flat
pull-back where it is defined [Kol07, Definition 60]
(`markedTransform_comap_blowUpMap_of_pow_dvd`). The main
statement is `weakTransformSeq_pullback_of_isOrderSeq`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme IdealSheafData BlowUpSequence
  Scheme.IdealSheafData

namespace AlgebraicGeometry

variable {k : Type u} [Field k] [CharZero k] {L : Type u} [Field L] [CharZero L]
  {X Y : Scheme.{u}}

/-- One step of the flat transport: for a smooth center `D` of order `m` on both sides, the weak
transform of the pulled-back ideal along the pulled-back center is the pull-back of the weak
transform along the morphism of blow-ups (both are marked transforms with mark `m`). -/
theorem weakTransform_comap_of_orderAlong_of_flat (f : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (f' : Y ⟶ Spec (.of L)) (n' : ℕ)
    [SmoothOfRelativeDimension n' f'] (p : Y ⟶ X) (D I : X.IdealSheafData)
    [Smooth (D.subschemeι ≫ f)] [Smooth ((D.comap p).subschemeι ≫ f')] {m : ℕ}
    (hm : I.OrdAlongEq D.support (m : ℕ∞))
    (hm' : (I.comap p).OrdAlongEq (D.comap p).support (m : ℕ∞)) :
    (I.comap p).weakTransform (D.comap p) = (I.weakTransform D).comap (Scheme.Hom.blowUpMap p
        D) := by
  rw [weakTransform_eq_markedTransform_of_smooth f n D I hm,
    weakTransform_eq_markedTransform_of_smooth f' n' (D.comap p) (I.comap p) hm']
  exact markedTransform_comap_blowUpMap_of_pow_dvd p D I m
    (pow_dvd_comap_of_leOrdAlong f n D I fun η hη => (hm η hη).ge)

/-- The `⟨j, hj⟩` form of `weakTransformSeq_pullback_of_isOrderSeq`, by induction on the sequence
peeling one blow-up on each side with `isOrderSeq_cons_iff`. -/
theorem IsOrderSeq.weakTransformSeq_pullback_mk_of_flat (f : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (f' : Y ⟶ Spec (.of L)) (n' : ℕ)
    [SmoothOfRelativeDimension n' f'] (p : Y ⟶ X) [Flat p] {S : BlowUpSequence X}
    {I : X.IdealSheafData} {E : DivisorFamily X} {m : ℕ} (hS : S.IsOrderSeq f I E m)
    (hS' : (S.pullback p).IsOrderSeq f' (I.comap p) (E.comap p) m) (j : ℕ) (hj : j < S.length + 1) :
    (S.pullback p).weakTransformSeq (I.comap p) (S.pullbackStageIdx p ⟨j, hj⟩) =
      (S.weakTransformSeq I ⟨j, hj⟩).comap (S.pullbackStageHom p ⟨j, hj⟩) := by
  induction S generalizing Y j with
  | nil X => rfl
  | cons X D rest ih =>
    cases j with
    | zero => rfl
    | succ j =>
      obtain ⟨⟨hD, -, hm⟩, ht⟩ := (isOrderSeq_cons_iff f I E m D rest).1 hS
      obtain ⟨⟨hD', -, hm'⟩, ht'⟩ :=
        (isOrderSeq_cons_iff f' (I.comap p) (E.comap p) m (D.comap p)
          (rest.pullback (Scheme.Hom.blowUpMap p D))).1 hS'
      have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) :=
        smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
      have hπ' : SmoothOfRelativeDimension n' ((D.comap p).blowUpπ ≫ f') :=
        smoothOfRelativeDimension_blowUpπ_comp_of_smooth f' n' (D.comap p)
      have hflat : Flat (Scheme.Hom.blowUpMap p D) := flat_blowUpMap p D
      have hw : (I.comap p).weakTransform (D.comap p) = (I.weakTransform
          D).comap (Scheme.Hom.blowUpMap p D) :=
        weakTransform_comap_of_orderAlong_of_flat f n f' n' p D I hm hm'
      rw [hw, totalTransform_comap_of_flat] at ht'
      have := ih (D.blowUpπ ≫ f) ((D.comap p).blowUpπ ≫ f')
          (Scheme.Hom.blowUpMap p D) ht ht' j
        (Nat.lt_of_succ_lt_succ hj)
      rw [← hw] at this
      exact this

end AlgebraicGeometry

namespace AlgebraicGeometry

/-- Along a flat pull-back of a smooth blow-up sequence of order `m` whose pull-back is again one
of order `m`, the induced ideals of the pull-back are the pull-backs of the induced ideals under
the stage lifts ([Kol07, 34.2] with [Kol07, Definition 66]; the marked transform commutes with
flat pull-back, `markedTransform_comap_blowUpMap_of_pow_dvd`). -/
theorem weakTransformSeq_pullback_of_isOrderSeq {k : Type u} [Field k] [CharZero k] {m : ℕ}
    {L : Type u} [Field L] [CharZero L] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (f' : Y ⟶ Spec (.of L)) (n' : ℕ)
    [SmoothOfRelativeDimension n' f'] (p : Y ⟶ X) [Flat p] {S : BlowUpSequence X}
    {I : X.IdealSheafData} {E : DivisorFamily X} (hS : S.IsOrderSeq f I E m)
    (hS' : (S.pullback p).IsOrderSeq f' (I.comap p) (E.comap p) m) (i : Fin (S.length + 1)) :
    (S.pullback p).weakTransformSeq (I.comap p) (S.pullbackStageIdx p i) =
      (S.weakTransformSeq I i).comap (S.pullbackStageHom p i) := by
  obtain ⟨j, hj⟩ := i
  exact IsOrderSeq.weakTransformSeq_pullback_mk_of_flat f n f' n' p hS hS' j hj

end AlgebraicGeometry
