/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.Embedded
import Hironaka.Scheme.BlowUpSequence.EqNilMarked
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# A smooth `Y` gives the empty succession: the tools

For a smooth reduced `Y` the embedded desingularization sequence `BED(X, I_Y, ∅)`
(`Hironaka.Resolution.Algebraic.Wlo05.Embedded`) is the empty succession — [Wlo05, 4.6]: at a smooth
point of `Y` the invariant is already terminal. The theorem is `bed_eq_nil_of_smooth`
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedNilCore`); this module holds the tools of its proof:

* the run of `BMO_1` on the unit ideal is empty (`bmoOneRun_eq_nil_of_maxOrd_lt_one`,
  `bmoOneRun_eq_nil_of_eq_top`): a smooth blow-up sequence of order `≥ 1` without empty blow-ups
  for an ideal of maximal order `< 1` is `nil` (`eq_nil_of_isOrderGeSeq_of_maxOrd_lt`), and
  [Kol07, Theorem 69 (1)] with the convention [Kol07, 32] gives both for the run;
* the stage-`0` shapes of the loop: the truncation at `0` is the empty sequence (`take_zero`), and
  on a sequence written as `cons X D rest` the stop rule at stage `0` fires for the component
  `vanishingIdeal (closure {η})` of a point `η` of the first centre `D`
  (`centerContains_zero_of_mem_support`): `D ≤ vanishingIdeal (closure {η})` is
  `closure {η} ⊆ supp D` (the Galois connection `le_support_iff_le_vanishingIdeal`), so no
  reducedness of the centre is used;
* the loop through a round with an absorption at stage `0`: the found index is `0`
  (`find_eq_zero_of_hasAbsorptionAt_zero`) and the loop's length is the length of the loop from the
  isolated triple (`length_bedAux_of_hasAbsorptionAt_zero`); at a round without an absorption on
  the unit ideal the loop is empty (`length_bedAux_eq_zero_of_eq_top`).

The invariant of the induction is in `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedNilInvariant`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme Hironaka
  BlowUpSequence Scheme.IdealSheafData Hironaka.Stage

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

/-! ### The run on the unit ideal -/

/-- The run of `BMO_1` on a marked triple whose ideal has maximal order `< 1` is empty
([Kol07, Theorem 69 (1)] with the convention [Kol07, 32]): a smooth blow-up sequence of order
`≥ 1` without empty blow-ups for such an ideal is `nil` (`eq_nil_of_isOrderGeSeq_of_maxOrd_lt`). -/
theorem bmoOneRun_eq_nil_of_maxOrd_lt_one (T : MarkedTriple k) (hm : T.m = 1)
    (hI : T.I.maxOrd < 1) : bmoOneRun T hm = BlowUpSequence.nil T.X.left :=
  eq_nil_of_isOrderGeSeq_of_maxOrd_lt (T.X.left ↘ Spec (.of k))
    (isOrderGeSeq_bmoOneRun T hm) ((BMO_m 1 k).noEmptyCenters T ⟨le_rfl, hm⟩)
    (by rw [hm, Nat.cast_one]; exact hI)

/-- The run of `BMO_1` on the unit ideal is empty (the terminal round of the loop, when nothing is
left). -/
theorem bmoOneRun_eq_nil_of_eq_top (T : MarkedTriple k) (hm : T.m = 1) (hI : T.I = ⊤) :
    bmoOneRun T hm = BlowUpSequence.nil T.X.left :=
  bmoOneRun_eq_nil_of_maxOrd_lt_one T hm (by rw [hI, maxOrd_top]; exact zero_lt_one)

/-! ### Stage `0` of a sequence -/

/-- The truncation of a sequence at `0` is the empty sequence. -/
theorem take_zero {X : Scheme.{u}} (S : BlowUpSequence X) : S.take 0 = BlowUpSequence.nil X := by
  cases S <;> rfl

/-- On a sequence starting with the blow-up of `D`, if a point `η` lies in the support of `D`, the
first centre contains the closure of `η` — as ideals, `D ≤ vanishingIdeal (closure {η})` — so the
stop rule fires at stage `0` for the component `vanishingIdeal (closure {η})` (`CenterContains`;
the strict transform at stage `0` is the ideal itself). -/
theorem centerContains_zero_of_mem_support {X : Scheme.{u}} (D : X.IdealSheafData)
    (rest : BlowUpSequence D.blowUp) {η : X} (hη : η ∈ D.support) :
    CenterContains (BlowUpSequence.cons X D rest) (IdealSheafData.vanishingIdeal (Closeds.closure
        {η})) 0 :=
  ⟨Nat.succ_pos _, IdealSheafData.le_support_iff_le_vanishingIdeal.mp
    (Closeds.closure_le.mpr (Set.singleton_subset_iff.mpr hη))⟩

/-- The stop rule at stage `0` for the loop's component set, when the run starts with the blow-up
of `D`, from a point `η ∈ D` whose component ideal is in the set. -/
theorem hasAbsorptionAt_zero_of_mem_support (T : MarkedTriple k) (hm : T.m = 1)
    (C : Finset T.X.left.IdealSheafData) {D : T.X.left.IdealSheafData}
    {rest : BlowUpSequence D.blowUp} (hrun : bmoOneRun T hm = BlowUpSequence.cons T.X.left D rest)
    {η : T.X.left} (hη : η ∈ D.support)
    (hC : IdealSheafData.vanishingIdeal (Closeds.closure {η}) ∈ C) :
    HasAbsorptionAt T hm C 0 :=
  ⟨_, hC, hrun ▸ centerContains_zero_of_mem_support D rest hη⟩

open Classical in
/-- With an absorption at stage `0`, the loop's first index is `0`. -/
theorem find_eq_zero_of_hasAbsorptionAt_zero (T : MarkedTriple k) (hm : T.m = 1)
    (C : Finset T.X.left.IdealSheafData) (h0 : HasAbsorptionAt T hm C 0) :
    Nat.find (⟨0, h0⟩ : ∃ n, HasAbsorptionAt T hm C n) = 0 :=
  Nat.eq_zero_of_le_zero (Nat.find_min' _ h0)

/-- The isolated triple keeps the mark `1`. -/
theorem isolatedTriple_m (T : MarkedTriple k) (hm : T.m = 1) (C : Finset T.X.left.IdealSheafData)
    (n : ℕ) : (isolatedTriple T hm C n).m = 1 :=
  hm

/-! ### The length of the loop through a round -/

/-- At a round with an absorption at stage `0` the loop's length is the length of the loop from
the isolated triple at stage `0` (the truncation at `0` is empty). -/
theorem length_bedAux_of_hasAbsorptionAt_zero (T : MarkedTriple k) (hm : T.m = 1)
    (C : Finset T.X.left.IdealSheafData) (h0 : HasAbsorptionAt T hm C 0) :
    (bedAux T hm C).length =
      (bedAux (isolatedTriple T hm C 0) (isolatedTriple_m T hm C 0)
        (remainingComponents T hm C 0)).length := by
  classical
  have h := bedAux_of_exists T hm C ⟨0, h0⟩
  have hf := find_eq_zero_of_hasAbsorptionAt_zero T hm C h0
  generalize Nat.find (⟨0, h0⟩ : ∃ n, HasAbsorptionAt T hm C n) = n₀ at h hf
  subst hf
  rw [h]
  refine (length_concat _ _).trans ?_
  rw [length_take, Nat.zero_min, Nat.zero_add]
  rfl

/-- At a round without an absorption the loop is the run, whose length is `0` when the ideal is
the unit ideal. -/
theorem length_bedAux_eq_zero_of_eq_top (T : MarkedTriple k) (hm : T.m = 1)
    (C : Finset T.X.left.IdealSheafData) (h : ¬ ∃ n, HasAbsorptionAt T hm C n) (hI : T.I = ⊤) :
    (bedAux T hm C).length = 0 := by
  rw [bedAux_of_not_exists T hm C h, bmoOneRun_eq_nil_of_eq_top T hm hI]
  rfl

end Hironaka.Resolution
