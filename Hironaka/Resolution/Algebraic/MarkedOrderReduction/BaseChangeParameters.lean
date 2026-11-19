/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Step2Separation
public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Step1NonmonomialPart
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.SplitTriple
import Hironaka.Resolution.Algebraic.OrderReduction.Functorial
import Hironaka.Scheme.BlowUpSequence.BaseChange
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The round parameters of Steps 1 and 2 under a change of fields

[Kol07, 34.2]: the change of fields `σ : k → L` replaces `(X, I, m, E)` by `(X_L, I_L, m, E_L)`
along the projection `p : X_L → X`, which is flat and surjective on points. The round parameter of
Step 1, `d = max-ord N(I)`, and that of Step 2, `s = max-ord_{cosupp(I, m)} N(I)`, are preserved:
the split pulls back (`nonmonomialPart_baseChange`), the maximal order is preserved by a change of
fields (`maxOrd_comap_of_isPullback_specMap`, through the derivative), and the order at every point
of `X_L` is the order at its image (`ord_comap_of_isPullback_specMap`: the support of a marked
ideal is the support of an iterated derivative, [Wlo05, Lemma 2.6.2], and the derivative commutes
with the base-change square). These are the change-of-fields forms of
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Parameters.lean`, used in
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/BaseChangeLoop.lean`. Not in the sources as
such.
-/

public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Hironaka
  Scheme.IdealSheafData Hironaka.Sequence

namespace Hironaka.BMO

section Ord

variable {k : Type u} [Field k] [CharZero k] {L : Type u} [Field L]

variable {T : Triple k} {T' : Triple L} {σ : k →+* L} {p : T'.X.left ⟶ T.X.left}

/-- The order at a point of the base-changed triple is the order at its image ([Kol07, 34.2]). -/
theorem ord_comap_of_isBaseChangeOf (hbc : T'.IsBaseChangeOf T σ p) (I : T.X.left.IdealSheafData)
    (y : T'.X.left) : (I.comap p).ord y = I.ord (p y) := by
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  obtain ⟨n', hn'⟩ := T'.smoothOfRelativeDimension
  exact ord_comap_of_isPullback_specMap hbc.1 n n' I y

/-- The maximal order is preserved by a change of fields ([Kol07, 34.2];
`maxOrd_comap_of_isPullback_specMap` at the triple). -/
theorem maxOrd_comap_of_isBaseChangeOf (hbc : T'.IsBaseChangeOf T σ p)
    (J : T.X.left.IdealSheafData) : (J.comap p).maxOrd = J.maxOrd := by
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  obtain ⟨n', hn'⟩ := T'.smoothOfRelativeDimension
  exact Hironaka.BO.maxOrd_comap_of_isPullback_specMap hbc.1 n n' J

/-- The maximal order of the base-changed ideal along the preimage of a set is the maximal order
along the set: the order is preserved pointwise and the projection is surjective. -/
theorem maxOrdAlong_comap_preimage_of_isBaseChangeOf (hbc : T'.IsBaseChangeOf T σ p)
    (J : T.X.left.IdealSheafData) (Z : Set T.X.left) :
    (J.comap p).maxOrdAlong (p ⁻¹' Z) = J.maxOrdAlong Z := by
  apply le_antisymm
  · rw [Scheme.IdealSheafData.maxOrdAlong_le_iff]
    intro y hy
    rw [ord_comap_of_isBaseChangeOf hbc]
    exact Scheme.IdealSheafData.le_maxOrdAlong (I := J) hy
  · rw [Scheme.IdealSheafData.maxOrdAlong_le_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := hbc.surjective x
    rw [← ord_comap_of_isBaseChangeOf hbc J y]
    exact Scheme.IdealSheafData.le_maxOrdAlong (I := J.comap p) (show y ∈ p ⁻¹' Z from hx)

end Ord

section Parameters

variable {k : Type u} [Field k] [CharZero k]

/-- The round parameter of Step 1 is preserved by change of fields ([Kol07, 34.2]):
`nonmonomialPart_baseChange`, and the base change preserves the maximal order. -/
theorem roundOrder_of_isBaseChangeOf {L : Type u} [Field L] [CharZero L] (T : MarkedTriple k)
    (T' : MarkedTriple L) {σ : k →+* L} {p : T'.X.left ⟶ T.X.left} (hbc : T'.IsBaseChangeOf T σ p) :
    roundOrder T' = roundOrder T := by
  unfold roundOrder
  rw [nonmonomialPart_baseChange T.toTriple σ p hbc.1, maxOrd_comap_of_isBaseChangeOf hbc.1]

/-- The separation parameter of Step 2 is preserved by change of fields ([Kol07, 34.2]). -/
theorem sepOrder_of_isBaseChangeOf {L : Type u} [Field L] [CharZero L] (T : MarkedTriple k)
    (T' : MarkedTriple L) {σ : k →+* L} {p : T'.X.left ⟶ T.X.left} (hbc : T'.IsBaseChangeOf T σ p) :
    sepOrder T' = sepOrder T := by
  obtain ⟨hbc0, hm⟩ := hbc
  have hN : nonmonomialPart T'.I T'.E = (nonmonomialPart T.I T.E).comap p :=
    nonmonomialPart_baseChange T.toTriple σ p hbc0
  have hset : {y | (T'.m : ℕ∞) ≤ T'.I.ord y} = p ⁻¹' {x | (T.m : ℕ∞) ≤ T.I.ord x} := by
    ext y
    change ((T'.m : ℕ∞) ≤ T'.I.ord y) ↔ ((T.m : ℕ∞) ≤ T.I.ord (p y))
    rw [hm, hbc0.2.1, ord_comap_of_isBaseChangeOf hbc0]
  unfold sepOrder
  rw [hN, hset, maxOrdAlong_comap_preimage_of_isBaseChangeOf hbc0]

end Parameters

end Hironaka.BMO
