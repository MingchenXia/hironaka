/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Stage.Tower
import Hironaka.Resolution.Algebraic.Stage.Congr
import Hironaka.Resolution.Algebraic.Stage.CongrBMO
import Hironaka.Resolution.Algebraic.Stage.DimZero
import Hironaka.Resolution.Algebraic.Stage.Mono
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Coherence and cross-dimensional functoriality of the tower

Kollár's induction [Kol07, 70] produces one pair of functors per dimension bound; the tower
`tower base n : OrderReductionStage n` (`Hironaka.Resolution.Algebraic.Stage.Tower`) is that family.
**Coherence**: for `n' ≤ n`, `BO_{n,m}` and `BO_{n',m}` of the tower agree on every triple of the
stage-`n'` class, and likewise `BMO` — the fact that lets
`Hironaka.Resolution.Algebraic.Stage.DimFree` define the single functors of [Kol07, Theorems 68 and
69] without reference to `n`. It is ONE simultaneous induction on `n`, both halves together: at `n =
0` the two stages coincide; at `n + 1` with `n' ≤ n`, the `BO` half is the construction of Theorem
103 at stages `n + 1` and `n'` fed the amalgams of the stage-`n` and stage-`(n' − 1)` marked
functors, which agree on the marked triples of dimension `≤ n' − 1` by the `BMO` half of the
induction hypothesis — the congruence `Hironaka.BO.data_congr`
(`Hironaka.Resolution.Algebraic.Stage.Congr`); at `n' = 0` both values are empty (the dimension-`0`
lemmas); the `BMO` half is the construction of Theorem 107 fed the two `BO` families just shown to
agree at every order — the congruence `Hironaka.BMO.data_congr`
(`Hironaka.Resolution.Algebraic.Stage.CongrBMO`); at `n' = n + 1` there is nothing to show.
**Cross-dimensional functoriality**: the two bullets of [Kol07, 34.1] for `g : Y → X` smooth with
`dim Y ≤ n` and `dim X ≤ n' ≤ n`, the value at `Y` taken at stage `n` and the value at `X` at stage
`n'` — coherence moves the stage-`n'` value at `X` to stage `n`, and the stage-`n` field
(`commutesWithSmooth`) is 34.1 at that stage.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Hironaka

namespace Hironaka.Stage

section Coherence

variable (base : OrderReductionStage.{u} 0)

/-- **The simultaneous induction** behind the coherence of the tower: for every `n' ≤ n`, both
halves of coherence at `(n, n')` — the `BO` half from the `BMO` half at `(n − 1, n' − 1)` through
the amalgams (`BO.data_congr`; dimension `0` at `n' = 0`), the `BMO` half from the `BO` half at
`(n, n')` at every order (`BMO.data_congr`). -/
theorem tower_coherent_aux (n : ℕ) : ∀ n' ≤ n,
    (∀ (m : ℕ) (k : Type u) [Field k] [CharZero k] (T : Triple k) (hT : T.BOClass n m)
      (hT' : T.BOClass n' m),
      (((tower base n).bo m).functor k).seq T hT = (((tower base n').bo m).functor k).seq T hT') ∧
    (∀ (m : ℕ) (k : Type u) [Field k] [CharZero k] (T : MarkedTriple k) (hT : T.BMOClass n m)
      (hT' : T.BMOClass n' m),
      (((tower base n).bmo m).functor k).seq T hT =
        (((tower base n').bmo m).functor k).seq T hT') := by
  induction n with
  | zero =>
    intro n' hn'
    obtain rfl : n' = 0 := Nat.le_zero.mp hn'
    exact ⟨fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl⟩
  | succ n ih =>
    intro n' hn'
    rcases Nat.lt_or_eq_of_le hn' with hlt | rfl
    · have hn'n : n' ≤ n := Nat.lt_succ_iff.mp hlt
      have hbo : ∀ (m : ℕ) (k : Type u) [Field k] [CharZero k] (T : Triple k)
          (hT : T.BOClass (n + 1) m) (hT' : T.BOClass n' m),
          (((tower base (n + 1)).bo m).functor k).seq T hT =
            (((tower base n').bo m).functor k).seq T hT' := by
        intro m k _ _ T hT hT'
        cases n' with
        | zero =>
          rw [OrderSeqAssignment.seq_eq_nil_of_hasDimLE_zero _ T hT hT'.2.1 hT'.1,
            OrderSeqAssignment.seq_eq_nil_of_hasDimLE_zero _ T hT' hT'.2.1 hT'.1]
        | succ n'' =>
          have hn''n : n'' ≤ n := Nat.le_of_lt hn'n
          exact Hironaka.BO.data_congr (n := n + 1) (n' := n'' + 1) (by omega) (amalgamDom n)
            (amalgamDom n'') (fun k _ _ => amalgam (tower base n).bmo k)
            (fun k _ _ => amalgam (tower base n'').bmo k)
            (fun m k _ _ T' hd hm => amalgamClass_of_tuningParam k m T' hd hm)
            (fun m k _ _ T' hd hm => amalgamClass_of_tuningParam k m T' hd hm)
            (fun k _ _ T' hT' => amalgam_maxOrd_endTriple_lt _ k T' hT')
            (fun k _ _ T' hT' => amalgam_maxOrd_endTriple_lt _ k T' hT')
            (fun k _ _ => amalgam_commutesWithSmooth _ k)
            (fun k _ _ => amalgam_commutesWithSmooth _ k)
            (fun k _ _ _ _ _ σ => amalgam_commutesWithBaseChange _ k σ)
            (fun k _ _ _ _ _ σ => amalgam_commutesWithBaseChange _ k σ)
            (fun k _ _ => amalgam_indifferentToEmptyMembers _ k)
            (fun k _ _ => amalgam_indifferentToEmptyMembers _ k)
            (fun k _ _ T' h₁ h₂ _ =>
              (ih n'' hn''n).2 T'.m k T' ⟨h₁.1, h₁.2, rfl⟩ ⟨h₂.1, h₂.2, rfl⟩)
            k T hT hT'
      have hbmo : ∀ (m : ℕ) (k : Type u) [Field k] [CharZero k] (T : MarkedTriple k)
          (hT : T.BMOClass (n + 1) m) (hT' : T.BMOClass n' m),
          (((tower base (n + 1)).bmo m).functor k).seq T hT =
            (((tower base n').bmo m).functor k).seq T hT' := by
        intro m k _ _ T hT hT'
        have hm : 1 ≤ T.m := by
          rw [hT'.2.2]
          exact hT'.1
        cases n' with
        | zero =>
          rw [OrderGeSeqAssignment.seq_eq_nil_of_hasDimLE_zero _ T hT hT'.2.1 hm,
            OrderGeSeqAssignment.seq_eq_nil_of_hasDimLE_zero _ T hT' hT'.2.1 hm]
        | succ n'' =>
          exact Hironaka.BMO.data_congr (by omega) (boOfBMO (tower base n).bmo)
            (boOfBMO (tower base n'').bmo)
            (fun d k _ _ => boOfBMO_indifferentToEmptyMembers _ d k)
            (fun d k _ _ => boOfBMO_indifferentToEmptyMembers _ d k)
            (fun d k _ _ T h₁ h₂ => hbo d k T h₁ h₂) k T hT hT'
      exact ⟨hbo, hbmo⟩
    · exact ⟨fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl⟩

variable {n n' : ℕ} (m : ℕ) {k : Type u} [Field k] [CharZero k]

/-- **Coherence of the unmarked family**: for `n' ≤ n`, `BO_{n,m}` and `BO_{n',m}` of the tower
agree on every triple of the stage-`n'` class (Kollár's functors of [Kol07, Theorem 103] are indexed
by `dim X = n`; the tower's stage `n` is defined on dimension `≤ n`, and its values do not depend on
the bound). -/
theorem tower_bo_coherent (hle : n' ≤ n) (T : Triple k) (hT : T.BOClass n m)
    (hT' : T.BOClass n' m) :
    (((tower base n).bo m).functor k).seq T hT = (((tower base n').bo m).functor k).seq T hT' :=
  (tower_coherent_aux base n n' hle).1 m k T hT hT'

/-- **Coherence of the marked family**: for `n' ≤ n`, `BMO_{n,m}` and `BMO_{n',m}` of the tower
agree on every marked triple of the stage-`n'` class ([Kol07, Theorem 107]). -/
theorem tower_bmo_coherent (hle : n' ≤ n) (T : MarkedTriple k) (hT : T.BMOClass n m)
    (hT' : T.BMOClass n' m) :
    (((tower base n).bmo m).functor k).seq T hT =
      (((tower base n').bmo m).functor k).seq T hT' :=
  (tower_coherent_aux base n n' hle).2 m k T hT hT'

end Coherence

section CrossDim

variable (base : OrderReductionStage.{u} 0) {n n' : ℕ} (m : ℕ) {k : Type u} [Field k] [CharZero k]

/-- The first bullet of [Kol07, 34.1] across the stages: for a smooth SURJECTION `g : Y → X` with
`dim Y ≤ n`, `dim X ≤ n' ≤ n`, the stage-`n` value of `BO` at `Y` is the pull-back of the stage-`n'`
value at `X` — coherence moves the value at `X` to stage `n`, where it is the stage-`n` field. -/
theorem tower_bo_pullback_of_surjective (hle : n' ≤ n) (T T' : Triple k) (g : T'.X.left ⟶ T.X.left)
    [Smooth g] (hs : Function.Surjective g) (hpb : T'.IsPullbackOf T g) (hT : T.BOClass n' m)
    (hT' : T'.BOClass n m) :
    (((tower base n).bo m).functor k).seq T' hT' =
      ((((tower base n').bo m).functor k).seq T hT).pullback g := by
  rw [← tower_bo_coherent base m hle T (Triple.boClass_mono hle hT) hT]
  exact (((tower base n).bo m).commutesWithSmooth k).1 T T' g hs hpb _ _

/-- The second bullet of [Kol07, 34.1] across the stages: for a smooth `g : Y → X` with `dim Y ≤ n`,
`dim X ≤ n' ≤ n`, the stage-`n` value of `BO` at `Y` is the pull-back of the stage-`n'` value at `X`
with its empty blow-ups deleted. -/
theorem tower_bo_pullback_eraseEmpty (hle : n' ≤ n) (T T' : Triple k) (g : T'.X.left ⟶ T.X.left)
    [Smooth g] (hpb : T'.IsPullbackOf T g) (hT : T.BOClass n' m) (hT' : T'.BOClass n m) :
    (((tower base n).bo m).functor k).seq T' hT' =
      (((((tower base n').bo m).functor k).seq T hT).pullback g).eraseEmpty := by
  rw [← tower_bo_coherent base m hle T (Triple.boClass_mono hle hT) hT]
  exact (((tower base n).bo m).commutesWithSmooth k).2 T T' g hpb _ _

/-- The first bullet of [Kol07, 34.1] across the stages, marked: the surjective form for `BMO`. -/
theorem tower_bmo_pullback_of_surjective (hle : n' ≤ n) (T T' : MarkedTriple k)
    (g : T'.X.left ⟶ T.X.left)
    [Smooth g] (hs : Function.Surjective g) (hpb : T'.IsPullbackOf T g) (hT : T.BMOClass n' m)
    (hT' : T'.BMOClass n m) :
    (((tower base n).bmo m).functor k).seq T' hT' =
      ((((tower base n').bmo m).functor k).seq T hT).pullback g := by
  rw [← tower_bmo_coherent base m hle T (MarkedTriple.bmoClass_mono hle hT) hT]
  exact (((tower base n).bmo m).commutesWithSmooth k).1 T T' g hs hpb _ _

/-- The second bullet of [Kol07, 34.1] across the stages, marked: the form with the empty blow-ups
deleted, for `BMO`. -/
theorem tower_bmo_pullback_eraseEmpty (hle : n' ≤ n) (T T' : MarkedTriple k)
    (g : T'.X.left ⟶ T.X.left)
    [Smooth g] (hpb : T'.IsPullbackOf T g) (hT : T.BMOClass n' m) (hT' : T'.BMOClass n m) :
    (((tower base n).bmo m).functor k).seq T' hT' =
      (((((tower base n').bmo m).functor k).seq T hT).pullback g).eraseEmpty := by
  rw [← tower_bmo_coherent base m hle T (MarkedTriple.bmoClass_mono hle hT) hT]
  exact (((tower base n).bmo m).commutesWithSmooth k).2 T T' g hpb _ _

end CrossDim

end Hironaka.Stage
