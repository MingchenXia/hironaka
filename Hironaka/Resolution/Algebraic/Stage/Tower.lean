/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Stage.Amalgam
public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Theorem107
public import Hironaka.Resolution.Algebraic.OrderReduction.Step3Data
import Hironaka.Resolution.Algebraic.OrderReduction.EmptyIndifferentGlobal
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The stage package and the recursion on the dimension bound

[Kol07, 70]: "(69) in dimensions `≤ n − 1` ⇒ (68) in dimension `n` ⇒ (69) in dimension `n`", a
spiralling induction (the diagram of [Kol07, 49]). In the library the two theorems are data —
`BOData n m` (Theorem 68 in dimension `≤ n`, proved as Theorem 103) and `BMOData n m` (Theorem 69,
proved as Theorem 107) — for EVERY mark `m` at once, the marks needed being data-dependent, and the
induction is a plain recursion on the dimension bound `n`:

* `OrderReductionStage n` — the stage package: a `BOData n m` and a `BMOData n m` for every `m`,
  both on triples of dimension `≤ n` (every irreducible component of dimension `≤ n`, the reading of
  Kollár's "`dim X = n`" under which disjoint unions and restriction to `E^j` stay in the class);
* `succ S` — the step `n → n + 1`: `BO.data (n+1) m` (Theorem 103) fed with the AMALGAM of `S.bmo`
  (`Hironaka.Resolution.Algebraic.Stage.Amalgam`: the inductive hypothesis is exactly the stage-`n`
  marked family), then `BMO.data` (Theorem 107) fed with the stage-`(n+1)` `bo` — its hypothesis
  `hboind` (indifference to empty boundary members) discharged by
  `BO.data_indifferentToEmptyMembers`;
* `tower base n` — the recursion from a base stage `base : OrderReductionStage 0` (`stage0` of
  `Hironaka.Resolution.Algebraic.Stage.Base`), by `Nat.rec`.

The family produced is indexed by `(n, m)`; the single functors of Theorems 68 and 69 are those of
`Hironaka.Resolution.Algebraic.Stage.DimFree` and `Hironaka.Resolution.Algebraic.Stage.Theorem68`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Hironaka

namespace Hironaka

/-- **The stage-`n` package** of the induction of [Kol07, 70]: the data `BO_{n,m}` of Theorem 103
and `BMO_{n,m}` of Theorem 107 for every mark `m`, on triples of dimension `≤ n`. -/
structure OrderReductionStage (n : ℕ) : Type (u + 1) where
/-- Theorem 103 (`BOData`) at every mark. -/
  bo : ∀ m : ℕ, BOData.{u} n m
/-- Theorem 107 (`BMOData`) at every mark. -/
  bmo : ∀ m : ℕ, BMOData.{u} n m

end Hironaka

namespace Hironaka.Stage

variable {n : ℕ}

/-- The amalgam's class as a domain `Dom : ∀ k, MarkedTriple k → Prop` over every field, the shape
of the inductive input of `bdData`. -/
def amalgamDom (n : ℕ) : ∀ (k : Type u) [Field k] [CharZero k], MarkedTriple k → Prop :=
  fun _ _ _ T => T.AmalgamClass n

/-- **`BO_{n+1,m}` from the stage-`n` marked family** ([Kol07, 70.1]: "(69) in dimensions `≤ n − 1`
⇒ (68) in dimension `n`", Theorem 103): `BO.data` at the amalgam of `bmo`, with the transports of
`Hironaka.Resolution.Algebraic.Stage.Amalgam` as the hypotheses on the inductive input. -/
noncomputable def boOfBMO (bmo : ∀ m : ℕ, BMOData.{u} n m) (m : ℕ) : BOData.{u} (n + 1) m :=
  Hironaka.BO.data (n + 1) m (amalgamDom n) (fun k _ _ => amalgam bmo k)
    (fun m k _ _ T' hd hm => amalgamClass_of_tuningParam k m T' hd hm)
    (fun k _ _ T' hT' => amalgam_maxOrd_endTriple_lt bmo k T' hT')
    (fun k _ _ => amalgam_commutesWithSmooth bmo k)
    (fun k _ _ _ _ _ σ => amalgam_commutesWithBaseChange bmo k σ)
    (fun k _ _ => amalgam_indifferentToEmptyMembers bmo k)

/-- Every `BO_{n+1,d}` of the step is indifferent to empty boundary members
(`BO.data_indifferentToEmptyMembers`). -/
theorem boOfBMO_indifferentToEmptyMembers (bmo : ∀ m : ℕ, BMOData.{u} n m) (d : ℕ) (k : Type u)
    [Field k] [CharZero k] : ((boOfBMO bmo d).functor k).IndifferentToEmptyMembers :=
  Hironaka.BO.data_indifferentToEmptyMembers (n + 1) d (amalgamDom n) (fun k _ _ => amalgam bmo k)
    (fun m k _ _ T' hd hm => amalgamClass_of_tuningParam k m T' hd hm)
    (fun k _ _ T' hT' => amalgam_maxOrd_endTriple_lt bmo k T' hT')
    (fun k _ _ => amalgam_commutesWithSmooth bmo k)
    (fun k _ _ _ _ _ σ => amalgam_commutesWithBaseChange bmo k σ)
    (fun k _ _ => amalgam_indifferentToEmptyMembers bmo k) k

/-- **The stage `n + 1` from a stage-`n` marked family** ([Kol07, 70.1–70.2]): `bo` is `BO_{n+1,·}`
from the family (`boOfBMO`), `bmo` is Theorem 107's `BMO.data` from that `bo`, its hypothesis
`hboind` discharged by `boOfBMO_indifferentToEmptyMembers`. Its TYPE says that the inductive
hypothesis used is the marked family and nothing else. -/
noncomputable def succOfBMO (bmo : ∀ m : ℕ, BMOData.{u} n m) : OrderReductionStage.{u} (n + 1) where
  bo := boOfBMO bmo
  bmo m := Hironaka.BMO.data (boOfBMO bmo)
    (fun d k _ _ => boOfBMO_indifferentToEmptyMembers bmo d k) (m := m)

/-- **The step `n → n + 1` of the recursion** ([Kol07, 70.1–70.2]): `succOfBMO` at the stage's
marked family; the stage's `bo` is not consulted. -/
noncomputable def succ (S : OrderReductionStage.{u} n) : OrderReductionStage.{u} (n + 1) :=
  succOfBMO S.bmo

/-- **The tower of stages** from a base stage ([Kol07, 70]: "we prove (68) and (69) together"; the
diagram of [Kol07, 49]), by recursion on the dimension bound. -/
noncomputable def tower (base : OrderReductionStage.{u} 0) : ∀ n : ℕ, OrderReductionStage.{u} n
  | 0 => base
  | n + 1 => succ (tower base n)

/-! ### Unfolding lemmas and existential forms -/

/-- The tower at stage `0` is the base. -/
theorem tower_zero (base : OrderReductionStage.{u} 0) : tower base 0 = base := rfl

/-- The tower at stage `n + 1` is the step applied to the tower at stage `n`. -/
theorem tower_succ (base : OrderReductionStage.{u} 0) (n : ℕ) :
    tower base (n + 1) = succ (tower base n) := rfl

/-- The unmarked family of the tower at stage `n + 1` is Theorem 103's data at the amalgam of the
stage-`n` marked family. -/
theorem tower_succ_bo (base : OrderReductionStage.{u} 0) (n m : ℕ) :
    (tower base (n + 1)).bo m = boOfBMO (tower base n).bmo m := rfl

/-- The marked family of the tower at stage `n + 1` is Theorem 107's functor at the stage-`(n + 1)`
unmarked family. -/
theorem tower_succ_bmo (base : OrderReductionStage.{u} 0) (n m : ℕ) (k : Type u) [Field k]
    [CharZero k] :
    ((tower base (n + 1)).bmo m).functor k = Hironaka.BMO.functor (boOfBMO (tower base n).bmo) m :=
  rfl

/-- The step is `succOfBMO` at the stage's marked family. -/
theorem succ_eq_succOfBMO (S : OrderReductionStage.{u} n) : succ S = succOfBMO S.bmo := rfl

/-- The unmarked family of the step is Theorem 103's data at the amalgam of the marked family below.
-/
theorem succ_bo (S : OrderReductionStage.{u} n) : (succ S).bo = boOfBMO S.bmo := rfl

/-- The functor of `BO_{n+1,m}` of the step is `BO.functor` at `bdData` fed with the amalgam and its
transports. -/
theorem boOfBMO_functor (bmo : ∀ m : ℕ, BMOData.{u} n m) (m : ℕ) (k : Type u) [Field k]
    [CharZero k] :
    (boOfBMO bmo m).functor k =
      Hironaka.BO.functor (n + 1) m (fun m j => Hironaka.BD.bdData (n + 1) m j (amalgamDom n)
        (fun k _ _ => amalgam bmo k)
        (fun k _ _ T' hd hm => amalgamClass_of_tuningParam k m T' hd hm)
        (fun k _ _ T' hT' => amalgam_maxOrd_endTriple_lt bmo k T' hT')
        (fun k _ _ => amalgam_commutesWithSmooth bmo k)
        (fun k _ _ _ _ _ σ => amalgam_commutesWithBaseChange bmo k σ)) := rfl

/-- The marked family of the step is Theorem 107's functor at the step's unmarked family
([Kol07, 70.2]). -/
theorem succ_bmo (S : OrderReductionStage.{u} n) (m : ℕ) (k : Type u) [Field k] [CharZero k] :
    ((succ S).bmo m).functor k = Hironaka.BMO.functor (succ S).bo m := rfl

/-- The step depends on the stage below only through its marked family (the inductive hypothesis of
[Kol07, Lemma 102 and Theorem 103]). -/
theorem succ_congr (S S' : OrderReductionStage.{u} n) (h : S.bmo = S'.bmo) : succ S = succ S' :=
  congrArg succOfBMO h

/-- The existential form of the step. -/
theorem exists_succ (S : OrderReductionStage.{u} n) :
    ∃ S' : OrderReductionStage.{u} (n + 1), S'.bo = boOfBMO S.bmo ∧
      ∀ (m : ℕ) (k : Type u) [Field k] [CharZero k],
        (S'.bmo m).functor k = Hironaka.BMO.functor (boOfBMO S.bmo) m :=
  ⟨succ S, rfl, fun _ _ _ _ => rfl⟩

/-- The existential form of the recursion ([Kol07, 70]). -/
theorem exists_tower (base : OrderReductionStage.{u} 0) :
    ∃ st : ∀ n : ℕ, OrderReductionStage.{u} n, st 0 = base ∧ ∀ n : ℕ, st (n + 1) = succ (st n) :=
  ⟨tower base, rfl, fun _ => rfl⟩

end Hironaka.Stage
