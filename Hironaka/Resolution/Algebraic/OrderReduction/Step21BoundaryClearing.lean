/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.ConcatTransforms
public import Hironaka.Scheme.BlowUpSequence.Triple
public import Hironaka.Resolution.Algebraic.BoundaryClearing.Data
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.Triple
import Hironaka.Resolution.Algebraic.OrderReduction.Functorial
import Hironaka.Scheme.Snc.DictionaryOrder
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Step 2.1 of order reduction: the boundary-clearing sequence

Step 2.1 of the proof of [Kol07, Theorem 103] ([Kol07, 104, Step 2.1]) clears the boundary
`E = E^1 + ⋯ + E^s` from the cosupport one member at a time. Starting from
`(X_0, I_0, E_0) = (X, I, E)`, the `j`-th round applies the boundary-clearing functor of
[Kol07, Lemma 102] to the triple `(X_{r(j−1)}, I_{r(j−1)}, E_{r(j−1)})` induced at the end of the
sequence built so far and to the birational transform `E^j_{r(j−1)}` of the `j`-th member,
extending the sequence to `Π_{r(j)} : X_{r(j)} → ⋯ → X_0`.

This module defines that construction and proves the two facts the recursion itself needs.

* `BO.step21Seq T hn hmax bd j` is the Step 2.1 sequence after `j` rounds, for the
  boundary-clearing data `bd : ∀ j, BDData n m j` of [Kol07, Lemma 102] (over every field of
  characteristic zero, taken as data) and a triple with `dim X ≤ n` and `max-ord I ≤ m`: the empty
  sequence at `j = 0`, and at `j + 1` the concatenation of the sequence after `j` rounds with the
  value of `BD_{n,m,j}` on the triple `(X_{r(j)}, I_{r(j)}, E_{r(j)})` induced at its last stage
  (`Triple.induced`). Kollár's `E^j_{r(j−1)}` is the `j`-th member by position of the total
  transform, the member `nth` of `BDClass n m j` (Kollár's `j = 1, …, s` is the position `j − 1`);
  beyond `s = card E.ι` the sequence is unchanged, so the construction is total in `j`. The
  subtype carries the two facts the recursion consumes: the concatenation is a smooth blow-up
  sequence of order `m` for `(X, I, E)` (`isOrderSeq_concat` with the functor's order field,
  through the definitional fields of `Triple.induced`) and has no empty blow-up
  (`noEmptyCenters_concat` with the functor's field). The disjointness achieved by Step 2.1 is a
  theorem about the construction
  (`Hironaka/Resolution/Algebraic/OrderReduction/Step21Disjoint.lean`), not a field.
* `BO.bdClass_induced_last`: the triple induced at the last stage of a smooth blow-up sequence of
  order `m` without empty blow-ups, starting from a triple of dimension `≤ n` and maximal order
  `≤ m`, lies in the boundary-clearing class `BDClass n m j` for every position `j < card E.ι`.
  The stages are smooth of the same relative dimension
  (`IsSmooth.stageMap_smoothOfRelativeDimension`); `max-ord I_r ≤ m` holds along a sequence of
  order `m` when `max-ord I = m` (`maxOrd_weakTransformSeq_le`), and below the mark the sequence
  is empty (`eq_nil_of_isOrderSeq_of_maxOrd_lt`); the total transform has at least as many members
  as `E` (`card_ι_totalTransformSeq`).

Kollár's standing hypotheses of Step 2, that `I` is D-balanced and MC-invariant and that a
hypersurface of maximal contact exists, are not used by the construction (his Warning before
Step 2.1: nothing beyond the order clause is assumed of the transforms); they enter the theorems
about it in `Hironaka/Resolution/Algebraic/OrderReduction/Step21MaximalContact.lean`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme Hironaka BlowUpSequence
  Scheme.IdealSheafData Hironaka.Sequence

namespace Hironaka.BO

variable {k : Type u} [Field k] [CharZero k] {n m : ℕ} (T : Triple k) (hn : T.HasDimLE n)
  (hmax : T.I.maxOrd ≤ m)

/-- The total transform has at least the members of the original family
(`card_ι_totalTransformSeq` read as an inequality). -/
theorem card_le_card_ι_totalTransformSeq {X : Scheme.{u}} (S : BlowUpSequence X)
    (E : DivisorFamily X) (i : Fin (S.length + 1)) :
    Fintype.card E.ι ≤ Fintype.card (S.totalTransformSeq E i).ι := by
  rw [card_ι_totalTransformSeq]
  exact Nat.le_add_right _ _

include hn hmax in
/-- The triple induced at the last stage of a smooth blow-up sequence of order `m` without empty
blow-ups, from a triple with `dim X ≤ n` and `max-ord I ≤ m`, lies in the boundary-clearing class
`BDClass n m j` of [Kol07, Lemma 102] for every position `j < card E.ι`. This is what allows
[Kol07, 104, Step 2.1] to "apply (102) to `X_{r(j−1)}, I_{r(j−1)}, E_{r(j−1)}`". -/
theorem bdClass_induced_last {S : BlowUpSequence T.X.left}
    (hS : S.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m) (hne : S.NoEmptyCenters) {j : ℕ}
    (hj : j < Fintype.card T.E.ι) : Triple.BDClass n m j (T.induced S hS (Fin.last _)) := by
  obtain ⟨n', hn'n, hn'⟩ := hn
  have : SmoothOfRelativeDimension n' (T.X.left ↘ Spec (.of k)) := hn'
  refine ⟨⟨n', hn'n, ?_⟩, ?_, ?_⟩
  · exact IsSmooth.stageMap_smoothOfRelativeDimension hS.1 (Fin.last _)
  · by_cases h : T.I.maxOrd = m
    · exact IsOrderSeq.maxOrd_weakTransformSeq_le (T.X.left ↘ Spec (.of k)) n' hS h (Fin.last _)
    · have hl : T.I.maxOrd < m := lt_of_le_of_ne hmax h
      have hnil := Hironaka.BO.eq_nil_of_isOrderSeq_of_maxOrd_lt (T.X.left ↘ Spec (.of k)) hS hne hl
      subst hnil
      exact hmax
  · change j < Fintype.card (S.totalTransformSeq T.E (Fin.last _)).ι
    exact lt_of_lt_of_le hj (card_le_card_ι_totalTransformSeq S T.E _)

variable (bd : ∀ j : ℕ, BDData.{u} n m j)

/-- **The Step 2.1 sequence after `j` rounds** ([Kol07, 104, Step 2.1]): empty at `j = 0`; at
`j + 1`, for a position `j < card E.ι`, the sequence after `j` rounds followed by `BD_{n,m,j}`
applied to the induced triple `(X_{r(j)}, I_{r(j)}, E_{r(j)})`, whose `j`-th member is
`E^j_{r(j)}`; unchanged beyond `card E.ι`. Carried with it: it is a smooth blow-up sequence of order
`m` starting with `(X, I, E)` without empty blow-ups. -/
noncomputable def step21Seq : (j : ℕ) →
    {S : BlowUpSequence T.X.left // S.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m ∧
      S.NoEmptyCenters}
  | 0 => ⟨BlowUpSequence.nil T.X.left, ⟨isSmooth_nil _, fun i => i.elim0⟩, fun i => i.elim0⟩
  | j + 1 =>
    if hj : j < Fintype.card T.E.ι then
      ⟨(step21Seq j).1.concat
          (((bd j).functor k).seq (T.induced (step21Seq j).1 (step21Seq j).2.1 (Fin.last _))
            (bdClass_induced_last T hn hmax (step21Seq j).2.1 (step21Seq j).2.2 hj)),
        isOrderSeq_concat (T.X.left ↘ Spec (.of k)) _ _ (step21Seq j).2.1
          (((bd j).functor k).isOrderSeq _ _),
        noEmptyCenters_concat _ _ (step21Seq j).2.2 (((bd j).functor k).noEmptyCenters _ _)⟩
    else step21Seq j

end Hironaka.BO
