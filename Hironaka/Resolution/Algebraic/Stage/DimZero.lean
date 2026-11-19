/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.BoundaryClearing.Data
import Hironaka.Resolution.Algebraic.OrderReduction.Functorial
import Hironaka.Scheme.BlowUpSequence.EqNilMarked
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.Smooth.EtaleStalk
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Dimension `0`: the base of the induction on the dimension

[Kol07, 70] starts the induction with the case `dim X = 0`, where `I = 𝒪_X` since `I` is nonzero on
every irreducible component and "everything is resolved without blow-ups". A triple of dimension
`≤ 0` (`HasDimLE 0`) has an étale structure morphism, its stalks are fields
(`AlgebraicGeometry.isField_stalk_of_smoothOfRelativeDimension_zero`), so the stalk ideal of `I` —
nonzero by [Kol07, Notation 64 (2)], the field `Triple.isNonzeroEverywhere` — is the unit ideal at
every point: `I = ⊤`. The unit ideal has maximal order `0`, and a smooth blow-up sequence of order
`m ≥ 1` (or `≥ m` for a marked triple with mark `≥ 1`) without empty blow-ups is then the empty
sequence (`Hironaka.BO.eq_nil_of_isOrderSeq_of_maxOrd_lt`,
`AlgebraicGeometry.eq_nil_of_isOrderGeSeq_of_maxOrd_lt`). Hence EVERY functor of the two types takes
the value `nil` on a triple of dimension `≤ 0` — the base of the coherence induction
(`Hironaka.Resolution.Algebraic.Stage.Coherence`): at stage `n' = 0` both stage functors agree
because both are empty. The lemmas hold unconditionally, over ANY field. -/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme.BlowUpSequence Scheme.IdealSheafData

namespace Hironaka

open Scheme

variable {k : Type u} [Field k]

/-- The base case of [Kol07, 70]: on a triple of dimension `≤ 0` the stalks are fields, so an ideal
nonzero on every component ([Kol07, Notation 64 (2)]) is the unit ideal. -/
theorem _root_.AlgebraicGeometry.Triple.I_eq_top_of_hasDimLE_zero (T : Triple k)
    (h : T.HasDimLE 0) : T.I = ⊤ := by
  obtain ⟨d, hd, hdim⟩ := h
  obtain rfl : d = 0 := Nat.le_zero.mp hd
  have : SmoothOfRelativeDimension 0 (T.X.left ↘ Spec (.of k)) := hdim
  rw [← Scheme.IdealSheafData.support_eq_bot_iff]
  by_contra hne
  obtain ⟨x, hx⟩ : ∃ x, x ∈ T.I.support := by
    by_contra h
    exact hne (le_antisymm (fun y hy => (h ⟨y, hy⟩).elim) bot_le)
  have hle := (IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal T.I x).mp hx
  have hfield : IsField (T.X.left.presheaf.stalk x) :=
    isField_stalk_of_smoothOfRelativeDimension_zero (T.X.left ↘ Spec (.of k)) x
  have hmax : IsLocalRing.maximalIdeal (T.X.left.presheaf.stalk x) = ⊥ :=
    (IsLocalRing.isField_iff_maximalIdeal_eq).mp hfield
  rw [hmax] at hle
  have hne0 : T.I.stalkIdeal x ≠ ⊥ := T.isNonzeroEverywhere x
  exact hne0 (le_bot_iff.mp hle)

/-- The base case of [Kol07, 70]: on a triple of dimension `≤ 0` every blow-up sequence functor of
order `m ≥ 1` takes the value `nil` — "everything is resolved without blow-ups": the ideal is the
unit ideal, of maximal order `0 < m`, and a sequence of order `m` without empty blow-ups for it is
empty. -/
theorem OrderSeqAssignment.seq_eq_nil_of_hasDimLE_zero {m : ℕ} {Dom : Triple k → Prop}
    (B : OrderSeqAssignment k m Dom) (T : Triple k) (hT : Dom T) (h0 : T.HasDimLE 0) (hm : 1 ≤ m) :
    B.seq T hT = BlowUpSequence.nil T.X.left := by
  have hI := T.I_eq_top_of_hasDimLE_zero h0
  have hlt : T.I.maxOrd < (m : ℕ∞) := by
    rw [hI]
    refine lt_of_le_of_lt ((IdealSheafData.maxOrd_le_iff _).mpr fun x => ?_)
      (lt_of_lt_of_le zero_lt_one (by exact_mod_cast hm))
    simp
  exact Hironaka.BO.eq_nil_of_isOrderSeq_of_maxOrd_lt (T.X.left ↘ Spec (.of k)) (B.isOrderSeq T hT)
    (B.noEmptyCenters T hT) hlt

/-- The base case of [Kol07, 70] for marked functors: on a marked triple of dimension `≤ 0` with
mark `≥ 1` every marked blow-up sequence functor takes the value `nil`
(`eq_nil_of_isOrderGeSeq_of_maxOrd_lt`). -/
theorem OrderGeSeqAssignment.seq_eq_nil_of_hasDimLE_zero {Dom : MarkedTriple k → Prop}
    (B : OrderGeSeqAssignment k Dom) (T : MarkedTriple k) (hT : Dom T) (h0 : T.toTriple.HasDimLE 0)
    (hm : 1 ≤ T.m) : B.seq T hT = BlowUpSequence.nil T.X.left := by
  have hI : T.I = ⊤ := T.toTriple.I_eq_top_of_hasDimLE_zero h0
  have hlt : T.I.maxOrd < (T.m : ℕ∞) := by
    rw [hI]
    refine lt_of_le_of_lt ((IdealSheafData.maxOrd_le_iff _).mpr fun x => ?_)
      (lt_of_lt_of_le zero_lt_one (by exact_mod_cast hm))
    simp
  exact eq_nil_of_isOrderGeSeq_of_maxOrd_lt (T.X.left ↘ Spec (.of k))
    (B.isOrderGeSeq T hT) (B.noEmptyCenters T hT) hlt

end Hironaka
