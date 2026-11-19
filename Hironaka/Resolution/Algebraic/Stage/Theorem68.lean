/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Stage.DimFree
public import Hironaka.Resolution.Algebraic.Stage.Base
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Theorems 68 and 69: the functors `BO_m` and `BMO_m`

Kollár's Theorem 68 and Theorem 69 [Kol07, Theorems 68 and 69], the main technical theorems of the
order-reduction part, as OBJECTS: for every mark `m` the smooth blow-up sequence functor `BO_m` of
order `m` on the triples `(X, I, E)` with `max-ord I ≤ m`, and the marked functor `BMO_m` of order
`≥ m` on the marked triples `(X, I, m, E)`. Both are the dimension-free functors of
`Hironaka.Resolution.Algebraic.Stage.DimFree` over the canonical base of the tower, `stage0`
(`Hironaka.Resolution.Algebraic.Stage.Base`): `BO_m(X, I, E) := BO_{dim X, m}(X, I, E)` and likewise
`BMO_m`, using the stage of the triple's own dimension. Their clauses (68.1)–(68.2), (69.1)–(69.2),
Claim 71.1 and Claim 71.2 are proved in `Hironaka.Resolution.Algebraic.Stage.DimFreeTheorems` and
`Hironaka.Resolution.Algebraic.Stage.ClosedEmbeddingGeneral`. These are the functors on which the
principalization `Hironaka.Sequence.BP` (Theorem 35), the order reduction of Main Theorems II and
II(N) and the embedded desingularization (`Hironaka.Resolution.Algebraic.Wlo05.Embedded`) are built.
-/

@[expose] public section

universe u

open AlgebraicGeometry Hironaka

namespace Hironaka.Stage

/-- **`BO_m`, the functor of [Kol07, Theorem 68]**: the dimension-free functor of the tower over the
base stage `stage0`. -/
noncomputable def BO_m (m : ℕ) (k : Type u) [Field k] [CharZero k] :
    OrderSeqAssignment k m (Triple.BOClassFree m) :=
  dimFreeBO stage0 m k

/-- **`BMO_m`, the functor of [Kol07, Theorem 69]**: the dimension-free marked functor of the tower
over `stage0`. -/
noncomputable def BMO_m (m : ℕ) (k : Type u) [Field k] [CharZero k] :
    OrderGeSeqAssignment k (MarkedTriple.BMOClassFree m) :=
  dimFreeBMO stage0 m k

end Hironaka.Stage
