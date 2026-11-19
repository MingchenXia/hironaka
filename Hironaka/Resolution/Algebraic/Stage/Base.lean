/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Stage.Tower
import Hironaka.Resolution.Algebraic.Stage.DimZero
import Hironaka.Scheme.BlowUpSequence.InducedData
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The base stage: dimension zero

[Kol07, 70] starts the induction with the case `dim X = 0`, where `I = 𝒪_X` since `I` is nonzero on
every irreducible component and "everything is resolved without blow-ups". A triple of dimension
`≤ 0` has `I = ⊤` (`Triple.I_eq_top_of_hasDimLE_zero`,
`Hironaka.Resolution.Algebraic.Stage.DimZero`), so the functors `BO_{0,m}` and `BMO_{0,m}` are the
empty sequence `nil` on their classes: clause (1) of Theorems 68 and 69 holds since `max-ord 𝒪_X = 0
< m` for a mark `m ≥ 1`, and functoriality (both bullets of [Kol07, 34.1]), change of fields [Kol07,
34.2] and the indifference to empty boundary members are the identities `nil = nil` (`pullback_nil`,
`eraseEmpty_nil`, both `rfl`). `stage0` packages these data; it is the base of the tower of stages
(`Hironaka.Stage.tower`, whose base is a parameter), and `HironakaExamples.Stage.BaseCases` shows
that it is the ONLY stage-`0` package. -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Hironaka Scheme BlowUpSequence Scheme.IdealSheafData

namespace Hironaka.Stage

open AlgebraicGeometry

/-- The functor `BO_{0,m}`: the empty blow-up sequence on every triple of dimension `≤ 0`
("everything is resolved without blow-ups", [Kol07, 70]). -/
noncomputable def boZeroFunctor (m : ℕ) (k : Type u) [Field k] :
    OrderSeqAssignment k m (Triple.BOClass 0 m) where
  seq T _ := BlowUpSequence.nil T.X.left
  isOrderSeq _ _ := isOrderSeq_nil _ _ _ _
  noEmptyCenters _ _ := fun i => (Nat.not_lt_zero _ i.isLt).elim

/-- **The data of `BO_{0,m}`** ([Kol07, Theorem 68] at dimension `0`, [Kol07, 70]): the `nil`
functor on the triples of dimension `≤ 0`; clause (1) because such a triple has `I = 𝒪_X`
(`Triple.I_eq_top_of_hasDimLE_zero`) of maximal order `0 < m`, and the two functoriality clauses
because `nil` pulls back to `nil`. -/
noncomputable def boZero (m : ℕ) : BOData.{u} 0 m where
  functor k _ _ := boZeroFunctor m k
  maxOrd_lt k _ _ T hT := by
    have hI : T.I = ⊤ := Triple.I_eq_top_of_hasDimLE_zero T hT.2.1
    have hm : (0 : ℕ∞) < m := by exact_mod_cast (hT.1 : 0 < m)
    -- `weakTransformSeq_nil` is `rfl`: the last weak transform along `nil` is `I` itself
    change T.I.maxOrd < (m : ℕ∞)
    rw [hI, maxOrd_top]
    exact hm
  commutesWithSmooth k _ _ :=
    ⟨by intro _ _ _ _ _ _ _ _; rfl, by intro _ _ _ _ _ _ _; rfl⟩
  commutesWithBaseChange k L _ _ _ _ σ := by intro _ _ _ _ _ _; rfl

/-- The functor `BMO_{0,m}`: the empty blow-up sequence on every marked triple of dimension `≤ 0`
([Kol07, 70]). -/
noncomputable def bmoZeroFunctor (m : ℕ) (k : Type u) [Field k] :
    OrderGeSeqAssignment k (MarkedTriple.BMOClass 0 m) where
  seq T _ := BlowUpSequence.nil T.X.left
  isOrderGeSeq _ _ := isOrderGeSeq_nil _ _ _ _
  noEmptyCenters _ _ := fun i => (Nat.not_lt_zero _ i.isLt).elim

/-- **The data of `BMO_{0,m}`** ([Kol07, Theorem 69] at dimension `0`, [Kol07, 70]): the `nil`
functor on the marked triples of dimension `≤ 0` and mark `m`; clause (1) because `I = 𝒪_X` there,
the functoriality clauses and the indifference to empty boundary members because `nil` pulls back to
`nil` and does not see the boundary. -/
noncomputable def bmoZero (m : ℕ) : BMOData.{u} 0 m where
  functor k _ _ := bmoZeroFunctor m k
  maxOrd_lt k _ _ T hT := by
    have hI : T.I = ⊤ := Triple.I_eq_top_of_hasDimLE_zero T.toTriple hT.2.1
    have hm : (0 : ℕ∞) < m := by exact_mod_cast (hT.1 : 0 < m)
    -- `markedTransformSeq_nil` is `rfl`: the last marked transform along `nil` is `I` itself
    change T.I.maxOrd < (m : ℕ∞)
    rw [hI, maxOrd_top]
    exact hm
  commutesWithSmooth k _ _ :=
    ⟨by intro _ _ _ _ _ _ _ _; rfl, by intro _ _ _ _ _ _ _; rfl⟩
  commutesWithBaseChange k L _ _ _ _ σ := by intro _ _ _ _ _ _; rfl
  indifferentToEmptyMembers k _ _ := by intro _ _ _ _ _ _ _ _; rfl

/-- **The base stage** `stage0 : OrderReductionStage 0` ([Kol07, 70]): `BO_{0,m}` and `BMO_{0,m}`
for every mark `m`, both the empty sequence; the base of the tower `Hironaka.Stage.tower stage0`
from which the functors of Theorems 68 and 69 are built
(`Hironaka.Resolution.Algebraic.Stage.Theorem68`). -/
noncomputable def stage0 : OrderReductionStage.{u} 0 where
  bo := boZero
  bmo := bmoZero

theorem stage0_bo (m : ℕ) : stage0.{u}.bo m = boZero m := rfl

theorem stage0_bmo (m : ℕ) : stage0.{u}.bmo m = bmoZero m := rfl

/-- The unmarked functor of the base stage is `nil`. -/
theorem stage0_bo_seq (m : ℕ) (k : Type u) [Field k] [CharZero k] (T : Triple k)
    (hT : T.BOClass 0 m) :
    ((stage0.{u}.bo m).functor k).seq T hT = BlowUpSequence.nil T.X.left := rfl

/-- The marked functor of the base stage is `nil`. -/
theorem stage0_bmo_seq (m : ℕ) (k : Type u) [Field k] [CharZero k] (T : MarkedTriple k)
    (hT : T.BMOClass 0 m) :
    ((stage0.{u}.bmo m).functor k).seq T hT = BlowUpSequence.nil T.X.left := rfl

end Hironaka.Stage
