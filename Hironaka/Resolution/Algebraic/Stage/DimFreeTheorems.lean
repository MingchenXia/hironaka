/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Stage.DimFree
public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.InducedClass
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Clause3
import Hironaka.Resolution.Algebraic.Stage.Coherence
import Hironaka.Resolution.Algebraic.Stage.DimZero
import Hironaka.Resolution.Algebraic.Stage.Mono
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Theorems 68 and 69 for the dimension-free functors over a base stage

[Kol07, Theorems 68 and 69] for `dimFreeBO base m k` and `dimFreeBMO base m k`
(`Hironaka.Resolution.Algebraic.Stage.DimFree`), over an ARBITRARY base stage `base :
OrderReductionStage 0`; `Hironaka.Resolution.Algebraic.Stage.Theorem68` instantiates them at
`stage0` for `BO_m` and `BMO_m`, and the proofs of Main Theorems II and II(N), of Theorem 35 and of
the embedded desingularization read the clauses from here. Every proof is one pattern:

* **coherence at the maximum** (`dimFreeBO_seq_eq_tower`, `dimFreeBMO_seq_eq_tower`): a triple `T`
  of the stage-`n` class and of the stage-`T.dim` class lies in the class of `N := max T.dim n`
  (`Triple.boClass_mono`), and `tower_bo_coherent` moves both values to stage `N` — so the
  dimension-free functor agrees with the tower at EVERY stage whose class contains `T`, and no
  relation between `n` and `T.dim` is needed (for `X = ∅` the chosen dimension is arbitrary);
* **a stage field**: clause (1) is the stage functor's `maxOrd_lt`; the two bullets of [Kol07, 34.1]
  (`commutesWithSmooth`, of any relative dimension), [Kol07, 34.2] (`commutesWithBaseChange`) and
  the indifference to empty boundary members compare two triples, moved to the common stage
  `max (dim T) (dim T')` and read from that stage's field (`BOData` has no indifference field:
  `tower_bo_indifferentToEmptyMembers` is `boOfBMO_indifferentToEmptyMembers` at stages `n + 1` and
  the dimension-`0` lemma at stage `0`);
* **Claim 71.1** ([Kol07, Claim 71.1]; [Kol07, 108]: "(71.1) is the same as (107.3)"): at stage
  `n + 1` the tower's marked functor IS `BMO.functor (boOfBMO …) m` and its unmarked one IS
  `boOfBMO … m` (`tower_succ_bmo`, `tower_succ_bo`, both `rfl`), so `eq_BO_of_maxOrd` (clause (3) of
  Theorem 107) applies; at stage `0` both values are `nil` (the dimension-`0` lemmas).

Claim 71.2 is `Hironaka.Resolution.Algebraic.Stage.ClosedEmbeddingGeneral`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Hironaka

namespace Hironaka.Stage

variable (base : OrderReductionStage.{u} 0) (m : ℕ) {k : Type u} [Field k] [CharZero k]

/-! ### Coherence at the maximum -/

/-- The dimension-free unmarked functor agrees with the tower's `BO_{n, m}` at every triple of the
stage-`n` class — both stages meet at `max T.dim n` through `tower_bo_coherent` (any `n ≥ dim X`
gives the same sequence). -/
theorem dimFreeBO_seq_eq_tower (n : ℕ) (T : Triple k) (hT : T.BOClassFree m)
    (hT' : T.BOClass n m) :
    (dimFreeBO base m k).seq T hT = (((tower base n).bo m).functor k).seq T hT' := by
  have hN : T.BOClass (max T.dim n) m :=
    Triple.boClass_mono (le_max_left _ _) (Triple.boClass_of_boClassFree hT)
  rw [dimFreeBO_seq,
    ← tower_bo_coherent base m (le_max_left T.dim n) T hN (Triple.boClass_of_boClassFree hT),
    tower_bo_coherent base m (le_max_right T.dim n) T hN hT']

/-- The marked form: the dimension-free marked functor agrees with the tower's `BMO_{n, m}` at every
marked triple of the stage-`n` class. -/
theorem dimFreeBMO_seq_eq_tower (n : ℕ) (T : MarkedTriple k) (hT : T.BMOClassFree m)
    (hT' : T.BMOClass n m) :
    (dimFreeBMO base m k).seq T hT = (((tower base n).bmo m).functor k).seq T hT' := by
  have hN : T.BMOClass (max T.toTriple.dim n) m :=
    MarkedTriple.bmoClass_mono (le_max_left _ _) (MarkedTriple.bmoClass_of_bmoClassFree hT)
  rw [dimFreeBMO_seq,
    ← tower_bmo_coherent base m (le_max_left T.toTriple.dim n) T hN
      (MarkedTriple.bmoClass_of_bmoClassFree hT),
    tower_bmo_coherent base m (le_max_right T.toTriple.dim n) T hN hT']

/-! ### Clause (1) of Theorems 68 and 69 -/

/-- [Kol07, Theorem 68 (1)]: `max-ord I_r < m` — the stage functor's clause (1) (Theorem 103 (1)) at
stage `T.dim`. -/
theorem dimFreeBO_maxOrd_lt (T : Triple k) (hT : T.BOClassFree m) :
    (((dimFreeBO base m k).seq T hT).weakTransformSeq T.I (Fin.last _)).maxOrd < (m : ℕ∞) :=
  ((tower base T.dim).bo m).maxOrd_lt k T (Triple.boClass_of_boClassFree hT)

/-- [Kol07, Theorem 69 (1)]: `max-ord I_r < m` for the marked functor (Theorem 107 (1)). -/
theorem dimFreeBMO_maxOrd_lt (T : MarkedTriple k) (hT : T.BMOClassFree m) :
    (((dimFreeBMO base m k).seq T hT).markedTransformSeq T.I T.m (Fin.last _)).maxOrd <
      (m : ℕ∞) :=
  ((tower base T.toTriple.dim).bmo m).maxOrd_lt k T (MarkedTriple.bmoClass_of_bmoClassFree hT)

/-! ### Clause (2) of Theorems 68 and 69 -/

/-- [Kol07, Theorem 68 (2)], functoriality for smooth morphisms [Kol07, 34.1] of ANY relative
dimension: both triples of a pull-back situation `T' → T` lie in the class of
`N := max T.dim T'.dim`; coherence moves both values to stage `N`, whose field is 34.1. -/
theorem dimFreeBO_commutesWithSmooth : (dimFreeBO base m k).CommutesWithSmooth := by
  refine ⟨fun T T' h _ hs hpb hT hT' => ?_, fun T T' h _ hpb hT hT' => ?_⟩
  · rw [dimFreeBO_seq_eq_tower base m (max T.dim T'.dim) T hT
        (Triple.boClass_mono (le_max_left _ _) (Triple.boClass_of_boClassFree hT)),
      dimFreeBO_seq_eq_tower base m (max T.dim T'.dim) T' hT'
        (Triple.boClass_mono (le_max_right _ _) (Triple.boClass_of_boClassFree hT'))]
    exact (((tower base (max T.dim T'.dim)).bo m).commutesWithSmooth k).1 T T' h hs hpb _ _
  · rw [dimFreeBO_seq_eq_tower base m (max T.dim T'.dim) T hT
        (Triple.boClass_mono (le_max_left _ _) (Triple.boClass_of_boClassFree hT)),
      dimFreeBO_seq_eq_tower base m (max T.dim T'.dim) T' hT'
        (Triple.boClass_mono (le_max_right _ _) (Triple.boClass_of_boClassFree hT'))]
    exact (((tower base (max T.dim T'.dim)).bo m).commutesWithSmooth k).2 T T' h hpb _ _

/-- [Kol07, Theorem 68 (2)], change of fields [Kol07, 34.2]: the base-change triple `T'` over `L`
and `T` over `k` lie in the class of `N := max T.dim T'.dim`; the stage-`N` field is 34.2. -/
theorem dimFreeBO_commutesWithBaseChange {L : Type u} [Field L] [CharZero L] (σ : k →+* L) :
    (dimFreeBO base m k).CommutesWithBaseChange (dimFreeBO base m L) σ := by
  intro T T' p hbc hT hT'
  rw [dimFreeBO_seq_eq_tower base m (max T.dim T'.dim) T hT
      (Triple.boClass_mono (le_max_left _ _) (Triple.boClass_of_boClassFree hT)),
    dimFreeBO_seq_eq_tower base m (max T.dim T'.dim) T' hT'
      (Triple.boClass_mono (le_max_right _ _) (Triple.boClass_of_boClassFree hT'))]
  exact ((tower base (max T.dim T'.dim)).bo m).commutesWithBaseChange k L σ T T' p hbc _ _

/-- [Kol07, Theorem 69 (2)], functoriality for smooth morphisms [Kol07, 34.1], for the marked
functor. -/
theorem dimFreeBMO_commutesWithSmooth : (dimFreeBMO base m k).CommutesWithSmooth := by
  refine ⟨fun T T' h _ hs hpb hT hT' => ?_, fun T T' h _ hpb hT hT' => ?_⟩
  · rw [dimFreeBMO_seq_eq_tower base m (max T.toTriple.dim T'.toTriple.dim) T hT
        (MarkedTriple.bmoClass_mono (le_max_left _ _) (MarkedTriple.bmoClass_of_bmoClassFree hT)),
      dimFreeBMO_seq_eq_tower base m (max T.toTriple.dim T'.toTriple.dim) T' hT'
        (MarkedTriple.bmoClass_mono (le_max_right _ _)
          (MarkedTriple.bmoClass_of_bmoClassFree hT'))]
    exact (((tower base (max T.toTriple.dim T'.toTriple.dim)).bmo m).commutesWithSmooth k).1
      T T' h hs hpb _ _
  · rw [dimFreeBMO_seq_eq_tower base m (max T.toTriple.dim T'.toTriple.dim) T hT
        (MarkedTriple.bmoClass_mono (le_max_left _ _) (MarkedTriple.bmoClass_of_bmoClassFree hT)),
      dimFreeBMO_seq_eq_tower base m (max T.toTriple.dim T'.toTriple.dim) T' hT'
        (MarkedTriple.bmoClass_mono (le_max_right _ _)
          (MarkedTriple.bmoClass_of_bmoClassFree hT'))]
    exact (((tower base (max T.toTriple.dim T'.toTriple.dim)).bmo m).commutesWithSmooth k).2
      T T' h hpb _ _

/-- [Kol07, Theorem 69 (2)], change of fields [Kol07, 34.2], for the marked functor. -/
theorem dimFreeBMO_commutesWithBaseChange {L : Type u} [Field L] [CharZero L] (σ : k →+* L) :
    (dimFreeBMO base m k).CommutesWithBaseChange (dimFreeBMO base m L) σ := by
  intro T T' p hbc hT hT'
  rw [dimFreeBMO_seq_eq_tower base m (max T.toTriple.dim T'.toTriple.dim) T hT
      (MarkedTriple.bmoClass_mono (le_max_left _ _) (MarkedTriple.bmoClass_of_bmoClassFree hT)),
    dimFreeBMO_seq_eq_tower base m (max T.toTriple.dim T'.toTriple.dim) T' hT'
      (MarkedTriple.bmoClass_mono (le_max_right _ _)
        (MarkedTriple.bmoClass_of_bmoClassFree hT'))]
  exact ((tower base (max T.toTriple.dim T'.toTriple.dim)).bmo m).commutesWithBaseChange k L σ
    T T' p hbc _ _

/-- Every stage of the tower's unmarked family is indifferent to empty boundary members —
`boOfBMO_indifferentToEmptyMembers` at stages `n + 1`, and at stage `0` both values are `nil` (the
dimension-`0` lemma; `BOData` has no indifference field, so the base contributes nothing but its
class). -/
theorem tower_bo_indifferentToEmptyMembers (n : ℕ) :
    (((tower base n).bo m).functor k).IndifferentToEmptyMembers := by
  cases n with
  | zero =>
    intro T E' hsnc' e _ _ hT hT'
    rw [OrderSeqAssignment.seq_eq_nil_of_hasDimLE_zero _ T hT hT.2.1 hT.1,
      OrderSeqAssignment.seq_eq_nil_of_hasDimLE_zero _ _ hT' hT'.2.1 hT'.1]
  | succ n' => exact boOfBMO_indifferentToEmptyMembers (tower base n').bmo m k

/-- The dimension-free marked functor is indifferent to empty boundary members — the two triples
share the ambient scheme, and both lie in the class of the common stage `max`, whose field is the
indifference. -/
theorem dimFreeBMO_indifferentToEmptyMembers :
    (dimFreeBMO base m k).IndifferentToEmptyMembers := by
  intro T E' hsnc' e h1 h2 hT hT'
  set T' : MarkedTriple k := { T with E := E', isSnc := hsnc' } with hT'def
  rw [dimFreeBMO_seq_eq_tower base m (max T.toTriple.dim T'.toTriple.dim) T hT
      (MarkedTriple.bmoClass_mono (le_max_left _ _) (MarkedTriple.bmoClass_of_bmoClassFree hT)),
    dimFreeBMO_seq_eq_tower base m (max T.toTriple.dim T'.toTriple.dim) T' hT'
      (MarkedTriple.bmoClass_mono (le_max_right _ _)
        (MarkedTriple.bmoClass_of_bmoClassFree hT'))]
  exact ((tower base (max T.toTriple.dim T'.toTriple.dim)).bmo m).indifferentToEmptyMembers k
    T E' hsnc' e h1 h2 _ _

/-- The dimension-free unmarked functor is indifferent to empty boundary members, from
`tower_bo_indifferentToEmptyMembers` at the common stage. -/
theorem dimFreeBO_indifferentToEmptyMembers : (dimFreeBO base m k).IndifferentToEmptyMembers := by
  intro T E' hsnc' e h1 h2 hT hT'
  set T' : Triple k := { T with E := E', isSnc := hsnc' } with hT'def
  rw [dimFreeBO_seq_eq_tower base m (max T.dim T'.dim) T hT
      (Triple.boClass_mono (le_max_left _ _) (Triple.boClass_of_boClassFree hT)),
    dimFreeBO_seq_eq_tower base m (max T.dim T'.dim) T' hT'
      (Triple.boClass_mono (le_max_right _ _) (Triple.boClass_of_boClassFree hT'))]
  exact tower_bo_indifferentToEmptyMembers base m (max T.dim T'.dim) T E' hsnc' e h1 h2 _ _

/-! ### Claim 71.1 -/

/-- [Kol07, Claim 71.1] at every stage of the tower ([Kol07, 108]: "(71.1) is the same as (107.3)"):
for `E = ∅` and `max-ord I = m`, the marked functor at `(X, I, m, ∅)` equals the unmarked one at
`(X, I, ∅)` — `eq_BO_of_maxOrd` at stages `n + 1` (where the tower's functors ARE those of the
assembly of Theorem 107, `tower_succ_bmo`/`tower_succ_bo` by `rfl`), and both `nil` at stage `0`. -/
theorem tower_bmo_eq_bo_of_maxOrd (n : ℕ) (T : Triple k) (hT : T.BOClass n m)
    (hE : IsEmpty T.E.ι) (hmax : T.I.maxOrd = (m : ℕ∞)) :
    (((tower base n).bmo m).functor k).seq ⟨T, m⟩ (Hironaka.BMO.bmoClass_of_boClass T hT) =
      (((tower base n).bo m).functor k).seq T hT := by
  cases n with
  | zero =>
    rw [OrderGeSeqAssignment.seq_eq_nil_of_hasDimLE_zero _ ⟨T, m⟩
        (Hironaka.BMO.bmoClass_of_boClass T hT) hT.2.1 hT.1,
      OrderSeqAssignment.seq_eq_nil_of_hasDimLE_zero _ T hT hT.2.1 hT.1]
  | succ n' => exact Hironaka.BMO.eq_BO_of_maxOrd (boOfBMO (tower base n').bmo) T hT hE hmax

/-- [Kol07, Claim 71.1], dimension-free: `BMO_m(X, I, m, ∅) = BO_m(X, I, ∅)` when `max-ord I = m` —
`tower_bmo_eq_bo_of_maxOrd` at the stage `T.dim` both functors read. -/
theorem dimFree_claim71_1 (T : Triple k) (hE : IsEmpty T.E.ι) (hm : 1 ≤ m)
    (hmax : T.I.maxOrd = (m : ℕ∞)) :
    (dimFreeBMO base m k).seq ⟨T, m⟩ ⟨hm, rfl⟩ = (dimFreeBO base m k).seq T ⟨hm, hmax.le⟩ :=
  tower_bmo_eq_bo_of_maxOrd base m T.dim T (Triple.boClass_of_boClassFree ⟨hm, hmax.le⟩) hE hmax

end Hironaka.Stage
