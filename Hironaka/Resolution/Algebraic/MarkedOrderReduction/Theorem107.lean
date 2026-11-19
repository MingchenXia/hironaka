/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Smooth
public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.BaseChangeLoop
public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Clause1
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Marked order reduction as data

[Kol07, Theorem 107] as the structure `BMOData n m`: the functor `BMO_{n,m}` over every
field of characteristic zero (`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Assembly.lean`),
clause (1), `max-ord I_r < m` (`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Clause1.lean`),
clause (2) for smooth morphisms (`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Smooth.lean`,
both clauses of [Kol07, 34.1]) and for change of fields
(`Hironaka/Resolution/Algebraic/MarkedOrderReduction/BaseChangeLoop.lean`), and the indifference to
empty boundary members, all under the hypothesis `hboind` that every input functor `bo d`, order
reduction for ideals in dimension `n` at the order `d`, is indifferent to empty boundary members;
that hypothesis is discharged for the order-reduction data in
`Hironaka/Resolution/Algebraic/OrderReduction/EmptyIndifferentGlobal.lean`. The existence statement
`exists_data` records that such data exist with the assembled functor as their functor. Clause (3)
of Theorem 107 is `Hironaka/Resolution/Algebraic/MarkedOrderReduction/Clause3.lean`; the readings of
the fields are in `Hironaka/Resolution/Algebraic/MarkedOrderReduction/Data.lean`. The data feed the
induction on the dimension in `Hironaka/Resolution/Algebraic/Stage/`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Hironaka

namespace Hironaka.BMO

variable {n : ℕ} (bo : ∀ d : ℕ, BOData.{u} n d) {m : ℕ}

/-- **[Kol07, Theorem 107] as data**: `BMO_{n,m}` as a `BMOData n m`, the functor of the assembly
over every field of characteristic zero, clause (1) (`maxOrd_lt`), clause (2)
(`commutesWithSmooth` under `hboind`, and `commutesWithBaseChange`), and the indifference to
empty boundary members (under `hboind`). -/
noncomputable def data (hboind : ∀ (d : ℕ) (k : Type u) [Field k] [CharZero k],
    ((bo d).functor k).IndifferentToEmptyMembers) : BMOData.{u} n m where
  functor k _ _ := Hironaka.BMO.functor (k := k) bo m
  maxOrd_lt _ _ _ T hT := maxOrd_lt bo T hT
  commutesWithSmooth _ _ _ := commutesWithSmooth bo hboind
  commutesWithBaseChange _ _ _ _ _ _ σ := commutesWithBaseChange bo σ
  indifferentToEmptyMembers _ _ _ := indifferentToEmptyMembers bo hboind

/-- There are marked order-reduction data `BMOData n m` whose functor over every field of
characteristic zero is the assembled `BMO_{n,m}`, under the indifference `hboind` of every input
functor `bo d` to empty boundary members: `BMO.data bo hboind`. -/
theorem exists_data (hboind : ∀ (d : ℕ) (k : Type u) [Field k] [CharZero k],
    ((bo d).functor k).IndifferentToEmptyMembers) :
    ∃ D : BMOData.{u} n m, ∀ (k : Type u) [Field k] [CharZero k],
      D.functor k = Hironaka.BMO.functor (k := k) bo m :=
  ⟨data bo hboind, fun _ _ _ => rfl⟩

end Hironaka.BMO
