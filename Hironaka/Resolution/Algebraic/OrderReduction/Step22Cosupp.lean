/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.OrderReduction.Step22RestrictToHypersurface
import Hironaka.Resolution.Algebraic.BoundaryClearing.Tuned
import Hironaka.Resolution.Algebraic.Kol07.AppendLast
import Hironaka.Resolution.Algebraic.MaximalContact.Sequence
import Hironaka.Resolution.Algebraic.OrderReduction.Step21MaximalContact
import Hironaka.Resolution.Algebraic.OrderReduction.Step22Basic
import Hironaka.Resolution.Algebraic.OrderReduction.Tuned
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUpSequence.TrivialCenter
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.Snc.DictionaryOrder
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Step 2.2 of order reduction: the cosupport is emptied

Step 2.2 of the proof of [Kol07, Theorem 103] ([Kol07, 104, Step 2.2]) ends with a sequence
`Π : X_r → X` whose cosupport `cosupp Π⁻¹_*(I, m)` is disjoint from `Π⁻¹_* H`; as `H` is a smooth
hypersurface of maximal contact, the cosupport lies in `Π⁻¹_* H`, hence is empty.

* **Clause (1) of [Kol07, Lemma 102] at the position of `H_r`** (`disjoint_cosupp_step22`): at the
  mark, the disjointness field of the boundary-clearing data for the tuned input triple at `s(m)`,
  with `H_r` the last member (`nth_append_last`), read back to the mark `m` for `I_r` by
  `Hironaka.BD.le_ord_weakTransformSeq_iff_tuned` (the cosupports agree stage by stage); below the
  mark the sequence is empty and `cosupp(I_r, m)` is already empty.
* **The containment** (`isMaximalContact_step22_H`, `cosupp_step22_subset_H`): Kollár's "by
  definition" is the maximal contact of the final transform of `H_r`
  (`IsOrderSeq.isMaximalContact_strictTransformSeq` along Step 2.2, from the maximal contact of
  `H_r` for `I_r` established in
  `Hironaka/Resolution/Algebraic/OrderReduction/Step21MaximalContact.lean`), read through [Kol07,
  Definition 79] (`mem_support_MC_iff`: `cosupp MC(I) = cosupp(I, m)`) and the antitonicity of
  supports in the ideal at the stalks.
* **The conclusion** (`cosupp_step22_eq_empty`, `maxOrd_step22_lt`): a set disjoint from a set
  containing it is empty, and `max-ord < m` is `maxOrd_lt_iff_forall_ord_lt`. This is clause (1)
  of [Kol07, Theorem 103] for Step 2.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing Hironaka Scheme.BlowUpSequence
  Scheme.IdealSheafData Hironaka.Sequence

namespace Hironaka.BO

variable {k : Type u} [Field k] [CharZero k] {n m : ℕ} (T : Triple k) (hn : T.HasDimLE n)
  (hmax : T.I.maxOrd ≤ m) (bd : ∀ m j : ℕ, BDData.{u} n m j) (hm : 1 ≤ m)
  {H : T.X.left.IdealSheafData}
  (hH : IsSmoothDivisor H) (hle : Scheme.IdealSheafData.IsMaximalContact (T.X.left ↘ Spec
      (.of k)) T.I m H)

/-- Clause (1) of [Kol07, Lemma 102] at the position of `H_r`, read back to the mark `m`
([Kol07, 104, Step 2.2]: "`cosupp Π⁻¹_*(I, m)` is disjoint from `Π⁻¹_* H`"). -/
theorem disjoint_cosupp_step22 :
    Disjoint
      {x | (m : ℕ∞) ≤
        ((step22 T hn hmax bd hm hH hle).weakTransformSeq
          (step22Triple T hn hmax bd hm hH hle).I (Fin.last _)).ord x}
      (((step22 T hn hmax bd hm hH hle).strictTransformSeq
        ((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.strictTransformSeq H
          (Fin.last _)) (Fin.last _)).support : Set _) := by
  have hT₂ := bdClass_step22Triple T hn hmax bd hm hH hle
  by_cases h : (step22Triple T hn hmax bd hm hH hle).I.maxOrd = m
  · refine (disjoint_cosupp_congr (step22_of_maxOrd_eq T hn hmax bd hm hH hle h) _ _ m).mpr ?_
    have hT₂' := bdClass_tuned hT₂ h hm
    set Q := ((bd (tuningParam m) _).functor k).seq
      ((step22Triple T hn hmax bd hm hH hle).tuned m hm) hT₂' with hQ
    have hd := (bd (tuningParam m) _).disjoint_cosupp k
      ((step22Triple T hn hmax bd hm hH hle).tuned m hm) hT₂'
    have hnth : ((step22Triple T hn hmax bd hm hH hle).tuned m hm).E.nth ⟨_, hT₂'.2.2⟩ =
        (step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.strictTransformSeq H (Fin.last _) :=
      nth_append_last _ _ _
    rw [hnth] at hd
    have hW : Q.IsOrderSeq ((step22Triple T hn hmax bd hm hH hle).X.left ↘ Spec (.of k))
        (step22Triple T hn hmax bd hm hH hle).I (step22Triple T hn hmax bd hm hH hle).E m := by
      have := isOrderSeq_step22 T hn hmax bd hm hH hle
      rwa [step22_of_maxOrd_eq T hn hmax bd hm hH hle h] at this
    obtain ⟨n', -, hn'⟩ :=
      hasDimLE_induced_last T hn (isOrderSeq_step21Seq T hn hmax (bd m) (Fintype.card T.E.ι))
    have : SmoothOfRelativeDimension n'
        ((step22Triple T hn hmax bd hm hH hle).X.left ↘ Spec (.of k)) := hn'
    have hset : {x | (m : ℕ∞) ≤
          (Q.weakTransformSeq (step22Triple T hn hmax bd hm hH hle).I (Fin.last _)).ord x} =
        {x | (tuningParam m : ℕ∞) ≤
          (Q.weakTransformSeq ((step22Triple T hn hmax bd hm hH hle).tuned m hm).I
            (Fin.last _)).ord x} :=
      Set.ext fun x => Hironaka.BD.le_ord_weakTransformSeq_iff_tuned _ n' Q _ _ m h hm hW
        (Fin.last _) x
    rw [hset]
    exact hd
  · have hlt : (step22Triple T hn hmax bd hm hH hle).I.maxOrd < m := lt_of_le_of_ne hT₂.2.1 h
    refine (disjoint_cosupp_congr (step22_of_maxOrd_lt T hn hmax bd hm hH hle hlt) _ _ m).mpr ?_
    refine Set.disjoint_left.mpr fun x hx _ => ?_
    have hord := (maxOrd_lt_iff_forall_ord_lt _ hm).mp hlt x
    exact absurd hx (not_le.mpr hord)

/-- The transform of `H_r` at the end of Step 2.2 is of maximal contact for the final ideal
([Kol07, 104, Step 2.2]: "`H` is a smooth hypersurface of maximal contact"), by
`IsOrderSeq.isMaximalContact_strictTransformSeq` from the maximal contact of `H_r` for `I_r`. -/
theorem isMaximalContact_step22_H :
    Scheme.IdealSheafData.IsMaximalContact
      ((step22 T hn hmax bd hm hH hle).stageMap (Fin.last _) ≫
        ((step22Triple T hn hmax bd hm hH hle).X.left ↘ Spec (.of k)))
      ((step22 T hn hmax bd hm hH hle).weakTransformSeq
        (step22Triple T hn hmax bd hm hH hle).I (Fin.last _)) m
      ((step22 T hn hmax bd hm hH hle).strictTransformSeq
        ((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.strictTransformSeq H
          (Fin.last _)) (Fin.last _)) := by
  obtain ⟨n', -, hn'⟩ :=
    hasDimLE_induced_last T hn (isOrderSeq_step21Seq T hn hmax (bd m) (Fintype.card T.E.ι))
  have : SmoothOfRelativeDimension n' ((step22Triple T hn hmax bd hm hH hle).X.left ↘
    Spec (.of k)) :=
    hn'
  exact IsOrderSeq.isMaximalContact_strictTransformSeq _ n' hm
    (isOrderSeq_step22 T hn hmax bd hm hH hle)
    (isSmoothDivisor_step21_H T hn hmax (bd m) hm hH hle (Fintype.card T.E.ι))
    (isMaximalContact_step21_H T hn hmax (bd m) hm hH hle (Fintype.card T.E.ι)) (Fin.last _)

/-- The cosupport of the final ideal lies in the transform of `H_r` ([Kol07, 104, Step 2.2]:
"hence, by definition, `cosupp Π⁻¹_*(I, m) ⊂ Π⁻¹_* H`"; [Kol07, Definition 79]). -/
theorem cosupp_step22_subset_H :
    {x | (m : ℕ∞) ≤
        ((step22 T hn hmax bd hm hH hle).weakTransformSeq
          (step22Triple T hn hmax bd hm hH hle).I (Fin.last _)).ord x} ⊆
      (((step22 T hn hmax bd hm hH hle).strictTransformSeq
        ((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.strictTransformSeq H
          (Fin.last _)) (Fin.last _)).support : Set _) := by
  obtain ⟨n', -, hn'⟩ :=
    hasDimLE_induced_last T hn (isOrderSeq_step21Seq T hn hmax (bd m) (Fintype.card T.E.ι))
  have : SmoothOfRelativeDimension n' ((step22Triple T hn hmax bd hm hH hle).X.left ↘
    Spec (.of k)) :=
    hn'
  have hfin : SmoothOfRelativeDimension n' ((step22 T hn hmax bd hm hH hle).stageMap (Fin.last _) ≫
      ((step22Triple T hn hmax bd hm hH hle).X.left ↘ Spec (.of k))) :=
    IsSmooth.stageMap_smoothOfRelativeDimension (isOrderSeq_step22 T hn hmax bd hm hH hle).1
      (Fin.last _)
  have hle_fin := isMaximalContact_step22_H T hn hmax bd hm hH hle
  intro x hx
  have hx' := (Scheme.IdealSheafData.mem_support_MC_iff ((step22 T hn hmax bd hm hH hle).stageMap
      (Fin.last _) ≫
    ((step22Triple T hn hmax bd hm hH hle).X.left ↘ Spec (.of k))) n'
    ((step22 T hn hmax bd hm hH hle).weakTransformSeq (step22Triple T hn hmax bd hm hH hle).I
      (Fin.last _)) hm x).mpr hx
  exact (Scheme.IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal _ x).mpr
    ((Scheme.IdealSheafData.stalkIdeal_mono hle_fin x).trans
        ((Scheme.IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal _ x).mp hx'))

/-- The cosupport of the final ideal of Step 2.2 is empty ([Kol07, 104, Step 2.2]: "thus
`cosupp Π⁻¹_*(I, m) = ∅`"). -/
theorem cosupp_step22_eq_empty :
    {x | (m : ℕ∞) ≤
        ((step22 T hn hmax bd hm hH hle).weakTransformSeq
          (step22Triple T hn hmax bd hm hH hle).I (Fin.last _)).ord x} = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr fun _ hx =>
    Set.disjoint_left.mp (disjoint_cosupp_step22 T hn hmax bd hm hH hle) hx
      (cosupp_step22_subset_H T hn hmax bd hm hH hle hx)

/-- The final ideal of Step 2.2 has `max-ord < m`: clause (1) of [Kol07, Theorem 103] after
Step 2.2 ("as we wanted"). -/
theorem maxOrd_step22_lt :
    ((step22 T hn hmax bd hm hH hle).weakTransformSeq
      (step22Triple T hn hmax bd hm hH hle).I (Fin.last _)).maxOrd < (m : ℕ∞) :=
  (maxOrd_lt_iff_forall_ord_lt _ hm).mpr fun x => lt_of_not_ge fun hx =>
    Set.eq_empty_iff_forall_notMem.mp (cosupp_step22_eq_empty T hn hmax bd hm hH hle) x hx

end Hironaka.BO
