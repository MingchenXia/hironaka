/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.OrderReduction.Step21BoundaryClearing
public import Hironaka.Scheme.Snc.Basic
import Hironaka.Resolution.Algebraic.MaximalContact.Sequence
import Hironaka.Resolution.Algebraic.OrderReduction.Step21Disjoint
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Step 2.1 of order reduction: the hypersurfaces of maximal contact and normal crossings

[Kol07, 104, Step 2.1] observes that every centre of the sequence lies in every hypersurface of
maximal contact, so that the birational transform `H_{r(j)}` of such a hypersurface `H` stays a
smooth hypersurface of maximal contact and the new exceptional divisors are transversal to it; at
the end of Step 2.1, for any hypersurface of maximal contact `H`, the divisor `H_{r(s)} + E_{r(s)}`
"has simple normal crossing along `cosupp(I_{r(s)}, m)`".

The first three results apply the general theory of maximal contact along a blow-up sequence
(`Hironaka/Resolution/Algebraic/MaximalContact/Sequence.lean`) to the Step 2.1 sequence `step21Seq`,
a sequence of order `m` by `isOrderSeq_step21Seq`, with the original hypothesis that `H` is a smooth
divisor whose ideal is contained in the maximal-contact ideal `MC(I)`, so that `H` is defined by a
section of `MC(I)` as in [Kol07, Theorem 80]: every centre lies in the birational transform of
`H`, the transforms are smooth divisors, and the last one is of maximal contact for the final
ideal `I_{r(j)}`. Kollár's warning before Step 2.1 is respected: the maximal contact of the
transforms is a conclusion, not a hypothesis used along the way.

The normal crossings of `H_r` with the exceptional members of `E_r` are proved everywhere, not only
along the cosupport, in `Hironaka/Resolution/Algebraic/Kol07/SncGlobalSubfamily.lean`
(`isSnc_exceptionalFamily_append`). The regularity clause of [Kol07, Definition 24] holds for the
members of `E_r` by clause (3) of [Kol07, Definition 66] along the sequence and for `H_r` as a
smooth divisor (`isRegular_component_append_step21`).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme.BlowUpSequence
  Scheme.IdealSheafData Hironaka.Sequence

namespace Hironaka.BO

variable {k : Type u} [Field k] [CharZero k] {n m : ℕ} (T : Triple k) (hn : T.HasDimLE n)
  (hmax : T.I.maxOrd ≤ m) (bd : ∀ j : ℕ, BDData.{u} n m j)

section MaximalContact

variable (hm : 1 ≤ m) {H : T.X.left.IdealSheafData} (hH : IsSmoothDivisor H)
  (hle : Scheme.IdealSheafData.IsMaximalContact (T.X.left ↘ Spec (.of k)) T.I m H)

include hm hH hle in
/-- Along the Step 2.1 sequence every centre lies in the birational transform of `H`
([Kol07, 104, Step 2.1]: "the center of every blow-up is contained in every hypersurface of
maximal contact"), by `IsOrderSeq.strictTransformSeq_le_center_of_le_MC` with the original
inclusion of the ideal of `H` in the maximal-contact ideal `MC(I)`. -/
theorem strictTransformSeq_le_center_step21 (j : ℕ)
    (i : Fin (step21Seq T hn hmax bd j).1.length) :
    (step21Seq T hn hmax bd j).1.strictTransformSeq H i.castSucc ≤
      (step21Seq T hn hmax bd j).1.center i := by
  obtain ⟨n', hn'⟩ := T.smoothOfRelativeDimension
  exact IsOrderSeq.strictTransformSeq_le_center_of_le_MC (T.X.left ↘ Spec (.of k)) n' hm
    (isOrderSeq_step21Seq T hn hmax bd j) hH hle i

include hm hH hle in
/-- The birational transform of `H` at the end of the Step 2.1 sequence is a smooth divisor
([Kol07, 104, Step 2.1]: "`H_{r(j)}` is a smooth hypersurface"). -/
theorem isSmoothDivisor_step21_H (j : ℕ) :
    IsSmoothDivisor ((step21Seq T hn hmax bd j).1.strictTransformSeq H (Fin.last _)) := by
  obtain ⟨n', hn'⟩ := T.smoothOfRelativeDimension
  exact IsOrderSeq.isSmoothDivisor_strictTransformSeq (T.X.left ↘ Spec (.of k)) n' hm
    (isOrderSeq_step21Seq T hn hmax bd j) hH hle _

include hm hH hle in
/-- The birational transform of `H` at the end of the Step 2.1 sequence is of maximal contact for
the final ideal `I_{r(j)}` ([Kol07, 104, Step 2.1]: "`H_{r(j)}` is a smooth hypersurface of maximal
contact"). -/
theorem isMaximalContact_step21_H (j : ℕ) :
    Scheme.IdealSheafData.IsMaximalContact ((step21Seq T hn hmax bd j).1.stageMap (Fin.last _) ≫
        (T.X.left ↘ Spec (.of k)))
      ((step21Seq T hn hmax bd j).1.weakTransformSeq T.I (Fin.last _)) m
      ((step21Seq T hn hmax bd j).1.strictTransformSeq H (Fin.last _)) := by
  obtain ⟨n', hn'⟩ := T.smoothOfRelativeDimension
  exact IsOrderSeq.isMaximalContact_strictTransformSeq (T.X.left ↘ Spec (.of k)) n' hm
    (isOrderSeq_step21Seq T hn hmax bd j) hH hle _

include hm hH hle in
/-- Every member of `H_{r(s)} + E_{r(s)}` is regular (clause (1) of [Kol07, Definition 24], "each
`E^i` is smooth"): the members of `E_{r(s)}` by the normal-crossings clause of [Kol07, Definition
66] along the sequence (`IsOrderSeq.isSnc_totalTransformSeq`), `H_{r(s)}` as a smooth divisor
(`isSmoothDivisor_step21_H`). -/
theorem isRegular_component_append_step21
    (i : (((step21Seq T hn hmax bd (Fintype.card T.E.ι)).1.totalTransformSeq T.E
      (Fin.last _)).append
      ((step21Seq T hn hmax bd (Fintype.card T.E.ι)).1.strictTransformSeq H (Fin.last _))).ι) :
    IsRegular ((((step21Seq T hn hmax bd (Fintype.card T.E.ι)).1.totalTransformSeq T.E
        (Fin.last _)).append ((step21Seq T hn hmax bd
        (Fintype.card T.E.ι)).1.strictTransformSeq H (Fin.last _))).component i).subscheme := by
  obtain ⟨n', hn'⟩ := T.smoothOfRelativeDimension
  rcases i with a | u
  · exact (IsOrderSeq.isSnc_totalTransformSeq (T.X.left ↘ Spec (.of k)) n'
      (isOrderSeq_step21Seq T hn hmax bd (Fintype.card T.E.ι)) T.isSnc (Fin.last _)).1 a
  · exact (isSmoothDivisor_step21_H T hn hmax bd hm hH hle (Fintype.card T.E.ι)).1

end MaximalContact

end Hironaka.BO
