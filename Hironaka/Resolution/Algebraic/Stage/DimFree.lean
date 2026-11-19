/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Stage.Tower
public import Hironaka.Resolution.Algebraic.Stage.Dim
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The dimension-free functors of Theorems 68 and 69

[Kol07, Theorem 68]: for every `m` there is a smooth blow-up sequence functor `BO_m` of order `m`,
"defined on triples `(X, I, E)` with `max-ord I ≤ m`"; [Kol07, Theorem 69] is the marked
counterpart, "defined on triples `(X, I, m, E)`". Kollár's Theorems 103 and 107 carry a dimension
bound: `BOData n m` and `BMOData n m` live on triples of dimension `≤ n`, and the tower
`Hironaka.Stage.tower base n` produces both for every `n` from a base stage. The bound is removed by
`BO_m(X, I, E) := BO_{dim X, m}(X, I, E)`, the stage of the triple's own dimension; by the coherence
of the tower any `n ≥ dim X` gives the same sequence.

This module holds that construction over an arbitrary base stage `base : OrderReductionStage 0` (the
tower's parameter); `Hironaka.Resolution.Algebraic.Stage.Theorem68` instantiates it at `stage0` to
define `BO_m` and `BMO_m`.

* the dimension of a triple is `AlgebraicGeometry.Triple.dim T`
  (`Hironaka.Resolution.Algebraic.Stage.Dim`), the relative dimension read off the triple's own
  equidimensionality field `T.smoothOfRelativeDimension` ([Kol07, Notation 64 (1)]), with
  `T.HasDimLE T.dim`. For `X = ∅` every `n` qualifies and the choice is arbitrary; coherence makes
  the functors' values independent of it.
* `Triple.BOClassFree m`, `MarkedTriple.BMOClassFree m` — the domains of Theorems 68 and 69: the
  stage classes `BOClass n m`, `BMOClass n m` without the dimension bound.
* `dimFreeBO base m k : OrderSeqFunctor k m (Triple.BOClassFree m)` — the value at `T` is the value
  of the tower's `BO_{T.dim, m}` at `T`; `dimFreeBMO base m k` likewise.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Hironaka

namespace Hironaka

variable {k : Type u} [Field k]

end Hironaka

namespace AlgebraicGeometry.Triple

open Hironaka

variable {k : Type u} [Field k]

/-- **The domain of `BO_m`** ([Kol07, Theorem 68]: "triples `(X, I, E)` with `max-ord I ≤ m`"): the
stage class `BOClass n m` without its dimension bound (`1 ≤ m`: Kollár's marks are `≥ 1`).
Reducible, as `BOClass` is. -/
abbrev BOClassFree (m : ℕ) (T : Triple k) : Prop := 1 ≤ m ∧ T.I.maxOrd ≤ (m : ℕ∞)

/-- A triple of Theorem 68's domain lies in the stage class of its own dimension. -/
theorem boClass_of_boClassFree {m : ℕ} {T : Triple k} (hT : T.BOClassFree m) :
    T.BOClass T.dim m :=
  ⟨hT.1, T.hasDimLE_dim, hT.2⟩

end AlgebraicGeometry.Triple

namespace Hironaka

variable {k : Type u} [Field k]

namespace MarkedTriple

/-- **The domain of `BMO_m`** ([Kol07, Theorem 69]: "defined on triples `(X, I, m, E)`"): the stage
class `BMOClass n m` without its dimension bound: the marked triples of mark `m ≥ 1`. Reducible, as
`BMOClass` is. -/
abbrev BMOClassFree (m : ℕ) (T : MarkedTriple k) : Prop := 1 ≤ m ∧ T.m = m

/-- A marked triple of Theorem 69's domain lies in the stage class of its own dimension. -/
theorem bmoClass_of_bmoClassFree {m : ℕ} {T : MarkedTriple k} (hT : T.BMOClassFree m) :
    T.BMOClass T.toTriple.dim m :=
  ⟨hT.1, T.toTriple.hasDimLE_dim, hT.2⟩

end MarkedTriple

end Hironaka

namespace Hironaka.Stage

variable (base : OrderReductionStage.{u} 0) (m : ℕ) (k : Type u) [Field k] [CharZero k]

/-- **The dimension-free functor of [Kol07, Theorem 68]** over a base stage: its value at a triple
`T` with `max-ord I ≤ m` is the value of the tower's `BO_{T.dim, m}` at `T`
(`BO_m(X, I, E) := BO_{dim X, m}(X, I, E)`); the order-`m` and no-empty-blow-up clauses are the
stage functor's. -/
noncomputable def dimFreeBO : OrderSeqAssignment k m (Triple.BOClassFree m) where
  seq T hT := (((tower base T.dim).bo m).functor k).seq T (Triple.boClass_of_boClassFree hT)
  isOrderSeq T hT := (((tower base T.dim).bo m).functor k).isOrderSeq T
      (Triple.boClass_of_boClassFree hT)
  noEmptyCenters T hT :=
    (((tower base T.dim).bo m).functor k).noEmptyCenters T (Triple.boClass_of_boClassFree hT)

/-- **The dimension-free functor of [Kol07, Theorem 69]** over a base stage, on the marked triples
of mark `m` (`BMO_m := BMO_{dim X, m}`). -/
noncomputable def dimFreeBMO : OrderGeSeqAssignment k (MarkedTriple.BMOClassFree m) where
  seq T hT :=
    (((tower base T.toTriple.dim).bmo m).functor k).seq T (MarkedTriple.bmoClass_of_bmoClassFree hT)
  isOrderGeSeq T hT :=
    (((tower base T.toTriple.dim).bmo m).functor k).isOrderGeSeq T
        (MarkedTriple.bmoClass_of_bmoClassFree hT)
  noEmptyCenters T hT :=
    (((tower base T.toTriple.dim).bmo m).functor k).noEmptyCenters T
      (MarkedTriple.bmoClass_of_bmoClassFree hT)

/-- The value of `dimFreeBO` unfolded: the stage-`T.dim` value (by `rfl`). -/
theorem dimFreeBO_seq (T : Triple k) (hT : T.BOClassFree m) :
    (dimFreeBO base m k).seq T hT =
      (((tower base T.dim).bo m).functor k).seq T (Triple.boClass_of_boClassFree hT) :=
  rfl

/-- The value of `dimFreeBMO` unfolded: the stage-`T.dim` value. -/
theorem dimFreeBMO_seq (T : MarkedTriple k) (hT : T.BMOClassFree m) :
    (dimFreeBMO base m k).seq T hT =
      (((tower base T.toTriple.dim).bmo m).functor k).seq T
          (MarkedTriple.bmoClass_of_bmoClassFree hT) :=
  rfl

end Hironaka.Stage
