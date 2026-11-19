/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.OrderReduction.Step3Clauses
public import Hironaka.Resolution.Algebraic.BoundaryClearing.Indifference
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Order reduction as data: `BO.dataOfBD` and `BO.data`

[Kol07, Theorem 103] assumes order reduction for marked ideals ([Kol07, Theorem 69]) in
dimensions `< n` and produces, for every mark `m`, the functor `BO_{n,m}` with its clauses
(1)–(2). The structure `BOData n m`
bundles the functor over every field of characteristic zero with those two clauses; this module
assembles it twice:

* `BO.dataOfBD bd hind`, from boundary-clearing data `bd : ∀ m j, BDData n m j` of
  [Kol07, Lemma 102] at every mark and position, indifferent to empty boundary members (`hind`):
  its functor is `BO.functor n m bd` and its clause fields are the theorems of
  `Hironaka/Resolution/Algebraic/OrderReduction/Step3Clauses.lean`. This is the form used by the
  recursion on the dimension in `Hironaka/Resolution/Algebraic/Stage/`.
* `BO.data Dom B hDom hB hsm hbc hBind`, from Theorem 103's own hypothesis, the marked
  order-reduction functor `B` in dimensions `≤ n − 1` with its clauses: the boundary-clearing data
  are `Hironaka.BD.bdData` at every mark and position, and their indifference is
  `Hironaka.BD.bdData_indifferentToEmptyMembers`, from the indifference `hBind` of the input.

The existence statements `exists_dataOfBD` and `exists_data` hold by `rfl` on these definitions.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Hironaka IsLocalRing

namespace Hironaka.BO

/-- **Clauses (1)–(2) of [Kol07, Theorem 103] as data**, from boundary-clearing data at every mark
and position: the functor is `BO.functor n m bd` over each field of characteristic zero, clause (1)
is `functor_maxOrd_lt`, and clause (2) is `functor_commutesWithSmooth` (under the indifference
`hind`) together with `functor_commutesWithBaseChange`. -/
noncomputable def dataOfBD (n m : ℕ) (bd : ∀ m j : ℕ, BDData.{u} n m j)
    (hind : ∀ m, BDFamily.IndifferentToEmptyMembers (bd m)) : BOData.{u} n m where
  functor k _ _ := functor (k := k) n m bd
  maxOrd_lt _ _ _ T hT := functor_maxOrd_lt n m bd T hT
  commutesWithSmooth _ _ _ := functor_commutesWithSmooth n m bd hind
  commutesWithBaseChange _ _ _ _ _ _ σ := functor_commutesWithBaseChange n m bd σ

/-- There are order-reduction data whose functor is `BO.functor n m bd`: `dataOfBD`. -/
theorem exists_dataOfBD (n m : ℕ) (bd : ∀ m j : ℕ, BDData.{u} n m j)
    (hind : ∀ m, BDFamily.IndifferentToEmptyMembers (bd m)) :
    ∃ D : BOData.{u} n m, ∀ (k : Type u) [Field k] [CharZero k], D.functor k = functor n m bd :=
  ⟨dataOfBD n m bd hind, fun _ _ _ => rfl⟩

/-- **Clauses (1)–(2) of [Kol07, Theorem 103] as data from the inductive hypothesis** ("assume that
(69) holds in dimensions `< n`"): `dataOfBD` at the boundary-clearing data `Hironaka.BD.bdData`
built from the marked functor `B`, with the indifference discharged by
`Hironaka.BD.bdData_indifferentToEmptyMembers` from `hBind`. -/
noncomputable def data (n m : ℕ)
    (Dom : ∀ (k : Type u) [Field k] [CharZero k], MarkedTriple k → Prop)
    (B : ∀ (k : Type u) [Field k] [CharZero k], OrderGeSeqAssignment k (Dom k))
    (hDom : ∀ (m : ℕ) (k : Type u) [Field k] [CharZero k] (T' : MarkedTriple k),
      T'.toTriple.HasDimLE (n - 1) → T'.m = tuningParam m → Dom k T')
    (hB : ∀ (k : Type u) [Field k] [CharZero k] (T' : MarkedTriple k) (hT' : Dom k T'),
      ((B k).endTriple T' hT').I.maxOrd < (T'.m : ℕ∞))
    (hsm : ∀ (k : Type u) [Field k] [CharZero k], (B k).CommutesWithSmooth)
    (hbc : ∀ (k L : Type u) [Field k] [CharZero k] [Field L] [CharZero L] (σ : k →+* L),
      (B k).CommutesWithBaseChange (B L) σ)
    (hBind : ∀ (k : Type u) [Field k] [CharZero k], (B k).IndifferentToEmptyMembers) :
    BOData.{u} n m :=
  dataOfBD n m (fun m j => Hironaka.BD.bdData n m j Dom B (hDom m) hB hsm hbc)
    (fun m => Hironaka.BD.bdData_indifferentToEmptyMembers Dom B hDom hB hsm hbc hBind m)

/-- There are order-reduction data whose functor is `BO.functor` at the boundary-clearing data
built from `B`: `data`. -/
theorem exists_data (n m : ℕ)
    (Dom : ∀ (k : Type u) [Field k] [CharZero k], MarkedTriple k → Prop)
    (B : ∀ (k : Type u) [Field k] [CharZero k], OrderGeSeqAssignment k (Dom k))
    (hDom : ∀ (m : ℕ) (k : Type u) [Field k] [CharZero k] (T' : MarkedTriple k),
      T'.toTriple.HasDimLE (n - 1) → T'.m = tuningParam m → Dom k T')
    (hB : ∀ (k : Type u) [Field k] [CharZero k] (T' : MarkedTriple k) (hT' : Dom k T'),
      ((B k).endTriple T' hT').I.maxOrd < (T'.m : ℕ∞))
    (hsm : ∀ (k : Type u) [Field k] [CharZero k], (B k).CommutesWithSmooth)
    (hbc : ∀ (k L : Type u) [Field k] [CharZero k] [Field L] [CharZero L] (σ : k →+* L),
      (B k).CommutesWithBaseChange (B L) σ)
    (hBind : ∀ (k : Type u) [Field k] [CharZero k], (B k).IndifferentToEmptyMembers) :
    ∃ D : BOData.{u} n m, ∀ (k : Type u) [Field k] [CharZero k],
      D.functor k = functor n m (fun m j => Hironaka.BD.bdData n m j Dom B (hDom m) hB hsm hbc) :=
  ⟨data n m Dom B hDom hB hsm hbc hBind, fun _ _ _ => rfl⟩

end Hironaka.BO
