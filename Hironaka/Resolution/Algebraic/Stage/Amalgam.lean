/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.TuningParam
public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Basic
public import Hironaka.Scheme.BlowUpSequence.Functor
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Data
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The amalgam of a stage's marked functors

Kollár's induction [Kol07, 70] ("(69) in dimensions `≤ n − 1` ⇒ (68) in dimension `n`"; Lemma 102
and Theorem 103 "assume (69) holds in dimensions `< n`") feeds the marked order-reduction functors
of the lower dimension into Lemma 102 and Theorem 103 — one functor `BMO_{n−1,m'}` for EVERY mark
`m'`, since the marks needed depend on the data. The library's Lemma 102 (`Hironaka.BD.bdData`) and
Theorem 103 (`Hironaka.BO.data`) take that hypothesis as ONE marked functor
`B k : OrderGeSeqFunctor k (Dom k)` over every field, defined on a class `Dom k` that contains every
marked triple of dimension `≤ n − 1` and mark `tuningParam m` (`hDom`), together with clause (1) of
Theorem 69 (`hB`), functoriality for smooth morphisms [Kol07, 34.1] (`hsm`), change of fields
[Kol07, 34.2] (`hbc`) and the indifference to empty boundary members (`hBind`). The stage package
`OrderReductionStage n` (`Hironaka.Resolution.Algebraic.Stage.Tower`) holds the family `bmo : ∀ m,
BMOData n m` instead. This module is the bridge: the **amalgam** of the family — the marked functor
on the class of marked triples of dimension `≤ n` with mark `≥ 1` whose value at `T` is the value of
`bmo T.m` — and the transports of the family's fields to the hypotheses of `bdData` and `data`. The
two triples of a pull-back pair (`MarkedTriple.IsPullbackOf`), of a base-change pair
(`MarkedTriple.IsBaseChangeOf`) and of an indifference pair carry the SAME mark, so each transport
is the corresponding field of `bmo T.m` read through the mark congruence `seq_congr_mark`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Hironaka

namespace Hironaka

/-- **The class of the amalgam**: the marked triples of dimension `≤ n` (every irreducible component
of dimension `≤ n`, `Triple.HasDimLE`) with mark `≥ 1` (Kollár's marks are `≥ 1`), all marks at once
— the class "in dimensions `≤ n`" of the inductive hypothesis of [Kol07, Lemma 102 and Theorem 103],
where the theorems assume (69) "in dimensions `< n`". -/
def MarkedTriple.AmalgamClass (n : ℕ) {k : Type u} [Field k] (T : MarkedTriple k) : Prop :=
  1 ≤ T.m ∧ T.toTriple.HasDimLE n

end Hironaka

namespace Hironaka.Stage

variable {n : ℕ} (bmo : ∀ m : ℕ, BMOData.{u} n m) (k : Type u) [Field k] [CharZero k]

omit [CharZero k] in
/-- A marked triple lies in `MarkedTriple.AmalgamClass n` iff its mark is `≥ 1` and its dimension is
`≤ n`. -/
theorem amalgamClass_iff (T : MarkedTriple k) :
    T.AmalgamClass n ↔ 1 ≤ T.m ∧ T.toTriple.HasDimLE n :=
  Iff.rfl

omit [CharZero k] in
/-- A marked triple of the amalgam's class lies in the class of `BMO_{n, T.m}`. -/
theorem bmoClass_of_amalgamClass {T : MarkedTriple k} (hT : T.AmalgamClass n) :
    T.BMOClass n T.m :=
  ⟨hT.1, hT.2, rfl⟩

/-- **The amalgam of the stage's marked functors** (the inductive hypothesis of [Kol07, 70] in one
functor): the marked functor on the marked triples of dimension `≤ n` with mark `≥ 1` whose value at
`(X, I, m, E)` is `BMO_{n,m}(X, I, m, E)`, the value of the family member at the triple's own mark;
the sequence is of order `≥ m` for the marked triple and has no empty blow-ups by the fields of
`bmo T.m`. -/
noncomputable def amalgam : OrderGeSeqAssignment k (MarkedTriple.AmalgamClass n) where
  seq T hT := ((bmo T.m).functor k).seq T (bmoClass_of_amalgamClass k hT)
  isOrderGeSeq T hT := ((bmo T.m).functor k).isOrderGeSeq T (bmoClass_of_amalgamClass k hT)
  noEmptyCenters T hT := ((bmo T.m).functor k).noEmptyCenters T (bmoClass_of_amalgamClass k hT)

/-- The value of the amalgam is the value of the family member at the triple's mark. -/
theorem amalgam_seq (T : MarkedTriple k) (hT : T.AmalgamClass n) :
    (amalgam bmo k).seq T hT = ((bmo T.m).functor k).seq T (bmoClass_of_amalgamClass k hT) :=
  rfl

/-- Two members of the family at equal marks take the same value (the class proofs are
irrelevant). -/
theorem seq_congr_mark {m₁ m₂ : ℕ} (h : m₁ = m₂) (T : MarkedTriple k) (h₁ : T.BMOClass n m₁)
    (h₂ : T.BMOClass n m₂) :
    ((bmo m₁).functor k).seq T h₁ = ((bmo m₂).functor k).seq T h₂ := by
  subst h
  rfl

omit [CharZero k] in
/-- A marked triple of dimension `≤ n` and mark `tuningParam m` lies in the amalgam's class (the
tuning parameter is `≥ 1`, `one_le_tuningParam`); this is the hypothesis `hDom` of `bdData`. -/
theorem amalgamClass_of_tuningParam (m : ℕ) (T : MarkedTriple k) (hd : T.toTriple.HasDimLE n)
    (hm : T.m = IsLocalRing.tuningParam m) : T.AmalgamClass n :=
  ⟨hm ▸ IsLocalRing.one_le_tuningParam m, hd⟩

/-- [Kol07, Theorem 69 (1)] for the amalgam: its value ends below its mark — the field `maxOrd_lt`
of `bmo T.m` (`BMOData.maxOrd_endTriple_lt`); the hypothesis `hB` of `bdData`. -/
theorem amalgam_maxOrd_endTriple_lt (T : MarkedTriple k) (hT : T.AmalgamClass n) :
    ((amalgam bmo k).endTriple T hT).I.maxOrd < (T.m : ℕ∞) :=
  (bmo T.m).maxOrd_endTriple_lt T (bmoClass_of_amalgamClass k hT)

/-- The amalgam commutes with smooth morphisms, both bullets of [Kol07, 34.1], from the field of
`bmo T.m` (a pull-back pair has equal marks); the hypothesis `hsm` of `bdData`. -/
theorem amalgam_commutesWithSmooth : (amalgam bmo k).CommutesWithSmooth := by
  refine ⟨fun T T' h _ hs hpb hT hT' => ?_, fun T T' h _ hpb hT hT' => ?_⟩
  · have key := ((bmo T.m).commutesWithSmooth k).1 T T' h hs hpb (bmoClass_of_amalgamClass k hT)
      ⟨hT.1, hT'.2, hpb.2⟩
    exact (seq_congr_mark bmo k hpb.2 T' _ _).trans key
  · have key := ((bmo T.m).commutesWithSmooth k).2 T T' h hpb (bmoClass_of_amalgamClass k hT)
      ⟨hT.1, hT'.2, hpb.2⟩
    exact (seq_congr_mark bmo k hpb.2 T' _ _).trans key

/-- The amalgams over `k` and `L` commute with change of fields along `σ` [Kol07, 34.2], from the
field of `bmo T.m` (a base-change pair has equal marks); the hypothesis `hbc` of `bdData`. -/
theorem amalgam_commutesWithBaseChange {L : Type u} [Field L] [CharZero L] (σ : k →+* L) :
    (amalgam bmo k).CommutesWithBaseChange (amalgam bmo L) σ := by
  intro T T' p hbc hT hT'
  have key := (bmo T.m).commutesWithBaseChange k L σ T T' p hbc (bmoClass_of_amalgamClass k hT)
    ⟨hT.1, hT'.2, hbc.2⟩
  exact (seq_congr_mark bmo L hbc.2 T' _ _).trans key

/-- The amalgam is indifferent to empty boundary members (deleting `⊤` members of the boundary does
not change its value, Kollár's reindexing of [Kol07, 34.1] and the convention of [Kol07, 32]), from
the field of `bmo T.m` (deleting members keeps the mark); the hypothesis `hBind` of `data`. -/
theorem amalgam_indifferentToEmptyMembers : (amalgam bmo k).IndifferentToEmptyMembers := by
  intro T E' hsnc' e hmem htop hT hT'
  exact (bmo T.m).indifferentToEmptyMembers k T E' hsnc' e hmem htop
    (bmoClass_of_amalgamClass k hT) ⟨hT'.1, hT'.2, rfl⟩

end Hironaka.Stage
