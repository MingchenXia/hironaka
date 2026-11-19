/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin
public import Hironaka.Scheme.BlowUpSequence.Basic
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.Center
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.MeetLocus
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.Step
import Hironaka.Scheme.BlowUpSequence.RestrictDivisors
import Hironaka.Scheme.Snc.TotalTransformSmoothBlowUp
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The disjoining sequence: smooth snc centers and a disjoint end result

The one-step facts of `Center.lean` and `Step.lean` are threaded along the steps of
`disjoinSeqAux m G` by induction on `m`, generalising the ambient scheme `X`, the snc family `F`
(Kollár's running total transform, `totalTransformSeq`) and the members `G` (the transforms of the
original components), with the invariant "no `(m+1)`-fold intersections among the members". At
each step the center `disjoinCenter G (m+2)` has snc with `F` and is smooth over `k`
(`Center.lean`), the total transform `F.totalTransform Z` is snc, the strict transforms of the
members are components of it (`totalTransform_component_inl`), and they have no `(m+2)`-fold
intersections (`Step.lean`); the induction continues on `B_Z X` with the smooth structure
morphism `Z.blowUpπ ≫ f`.

* `disjoinSeqAux_isSmooth`, `disjoinSeqAux_hasSncWith`: clause (1) of [Kol07, Theorem 35] for the
  disjoining part, in the forms `IsSmooth` and
  `(S.totalTransformSeq E i.castSucc).HasSncWith (S.center i)`.
* `isSnc_totalTransformSeq_disjoinSeqAux`: the total transform of [Kol07, Definition 25] is snc at
  every stage.
* `meetLocus_strictTransformSeq_disjoinSeqAux`: "after `(k − 1)`-steps we get rid of all pairwise
  intersections" [Kol07, 72].
* The `disjoinSeq` forms of all of these.
-/

public section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme IdealSheafData
  BlowUpSequence Scheme.IdealSheafData

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {k : Type u} [Field k] [PerfectField k]

/-- The strict transforms of members of `F` are members of the total transform. -/
theorem strictTransform_mem_range_totalTransform {ι : Type*} {X : Scheme.{u}} {F : DivisorFamily X}
    {G : ι → X.IdealSheafData} (hG : ∀ i, G i ∈ Set.range F.component) (Z : X.IdealSheafData)
    (i : ι) : (G i).strictTransform Z ∈ Set.range (F.totalTransform Z).component := by
  obtain ⟨a, ha⟩ := hG i
  exact ⟨toLex (Sum.inl a), by rw [← ha]; rfl⟩

/-- The invariant at the start: no `(k+1)`-fold intersections among `k` components. -/
theorem meetLocus_component_card_succ {X : Scheme.{u}} (E : DivisorFamily X) :
    meetLocus E.component (Fintype.card E.ι + 1) = ⊥ :=
  meetLocus_eq_bot_of_card_lt _ (Nat.lt_succ_self _)

section Steps

variable {ι : Type*} [Fintype ι]

/-- The total transform of `F` under a disjoining step is snc. -/
theorem isSnc_totalTransform_disjoinCenter {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f]
    {F : DivisorFamily X} (hF : F.IsSnc) (G : ι → X.IdealSheafData)
    (hG : ∀ i, G i ∈ Set.range F.component) (m : ℕ) (hm : meetLocus G (m + 2) = ⊥) :
    (F.totalTransform (disjoinCenter G (m + 1))).IsSnc :=
  totalTransform_isSnc f F _ hF (hasSncWith_disjoinCenter hF G hG m hm)

/-- Every center of the disjoining steps is smooth over `k` [Kol07, 72]; the first half of clause
(1) of [Kol07, Theorem 35] for the disjoining part. -/
theorem disjoinSeqAux_isSmooth : ∀ (m : ℕ) {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f]
    {F : DivisorFamily X} (_ : F.IsSnc) (G : ι → X.IdealSheafData)
    (_ : ∀ i, G i ∈ Set.range F.component) (_ : meetLocus G (m + 1) = ⊥),
    (disjoinSeqAux m G).IsSmooth f
  | 0, _, f, _, _, _, _, _, _ => isSmooth_nil f
  | 1, _, f, _, _, _, _, _, _ => isSmooth_nil f
  | m + 2, X, f, _, F, hF, G, hG, hm => by
    rw [disjoinSeqAux_succ_succ, isSmooth_cons_iff]
    have hsm := smooth_disjoinCenter f hF G hG (m + 1) hm
    refine ⟨hsm, ?_⟩
    have : Smooth ((disjoinCenter G (m + 2)).blowUpπ ≫ f) :=
      smooth_blowUpπ_comp_of_smooth' f _
    exact disjoinSeqAux_isSmooth (m + 1) ((disjoinCenter G (m + 2)).blowUpπ ≫ f)
      (isSnc_totalTransform_disjoinCenter f hF G hG (m + 1) hm) _
      (strictTransform_mem_range_totalTransform hG _)
      (meetLocus_strictTransform_disjoinCenter f hF G hG (m + 1) hm)

/-- Every center of the disjoining steps has simple normal crossings with the total transform of
`F` at its stage [Kol07, 72]; the second half of clause (1) of [Kol07, Theorem 35] for the
disjoining part, with the total transform of [Kol07, Definition 25]. -/
theorem disjoinSeqAux_hasSncWith : ∀ (m : ℕ) {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f]
    {F : DivisorFamily X} (_ : F.IsSnc) (G : ι → X.IdealSheafData)
    (_ : ∀ i, G i ∈ Set.range F.component) (_ : meetLocus G (m + 1) = ⊥)
    (i : Fin (disjoinSeqAux m G).length),
    ((disjoinSeqAux m G).totalTransformSeq F i.castSucc).HasSncWith ((disjoinSeqAux m G).center i)
  | 0, _, _, _, _, _, _, _, _, i => i.elim0
  | 1, _, _, _, _, _, _, _, _, i => i.elim0
  | m + 2, X, f, _, F, hF, G, hG, hm, ⟨0, _⟩ => hasSncWith_disjoinCenter hF G hG (m + 1) hm
  | m + 2, X, f, _, F, hF, G, hG, hm, ⟨j + 1, h⟩ => by
    have hsm := smooth_disjoinCenter f hF G hG (m + 1) hm
    have : Smooth ((disjoinCenter G (m + 2)).blowUpπ ≫ f) :=
      smooth_blowUpπ_comp_of_smooth' f _
    exact disjoinSeqAux_hasSncWith (m + 1) ((disjoinCenter G (m + 2)).blowUpπ ≫ f)
      (isSnc_totalTransform_disjoinCenter f hF G hG (m + 1) hm) _
      (strictTransform_mem_range_totalTransform hG _)
      (meetLocus_strictTransform_disjoinCenter f hF G hG (m + 1) hm)
      ⟨j, Nat.lt_of_succ_lt_succ h⟩

/-- The total transform of `F` ([Kol07, Definition 25]) is snc at every stage of the disjoining
steps. -/
theorem isSnc_totalTransformSeq_disjoinSeqAux : ∀ (m : ℕ) {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [Smooth f] {F : DivisorFamily X} (_ : F.IsSnc) (G : ι → X.IdealSheafData)
    (_ : ∀ i, G i ∈ Set.range F.component) (_ : meetLocus G (m + 1) = ⊥)
    (i : Fin ((disjoinSeqAux m G).length + 1)), ((disjoinSeqAux m G).totalTransformSeq F i).IsSnc
  | 0, _, _, _, _, hF, _, _, _, _ => hF
  | 1, _, _, _, _, hF, _, _, _, _ => hF
  | m + 2, X, f, _, F, hF, G, hG, hm, ⟨0, _⟩ => hF
  | m + 2, X, f, _, F, hF, G, hG, hm, ⟨j + 1, h⟩ => by
    have hsm := smooth_disjoinCenter f hF G hG (m + 1) hm
    have : Smooth ((disjoinCenter G (m + 2)).blowUpπ ≫ f) :=
      smooth_blowUpπ_comp_of_smooth' f _
    exact isSnc_totalTransformSeq_disjoinSeqAux (m + 1) ((disjoinCenter G (m + 2)).blowUpπ ≫ f)
      (isSnc_totalTransform_disjoinCenter f hF G hG (m + 1) hm) _
      (strictTransform_mem_range_totalTransform hG _)
      (meetLocus_strictTransform_disjoinCenter f hF G hG (m + 1) hm)
      ⟨j, Nat.lt_of_succ_lt_succ h⟩

/-- "After `(k − 1)`-steps we get rid of all pairwise intersections as well" [Kol07, 72]: the
final strict transforms of the members are pairwise disjoint. -/
theorem meetLocus_strictTransformSeq_disjoinSeqAux : ∀ (m : ℕ) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Smooth f] {F : DivisorFamily X} (_ : F.IsSnc)
    (G : ι → X.IdealSheafData) (_ : ∀ i, G i ∈ Set.range F.component)
    (_ : meetLocus G (m + 1) = ⊥),
    meetLocus (fun i => (disjoinSeqAux m G).strictTransformSeq (G i) (Fin.last _)) 2 = ⊥
  | 0, _, _, _, _, _, G, _, hm =>
    le_bot_iff.mp ((meetLocus_antitone G (by norm_num : 1 ≤ 2)).trans hm.le)
  | 1, _, _, _, _, _, _, _, hm => hm
  | m + 2, X, f, _, F, hF, G, hG, hm => by
    have hsm := smooth_disjoinCenter f hF G hG (m + 1) hm
    have : Smooth ((disjoinCenter G (m + 2)).blowUpπ ≫ f) :=
      smooth_blowUpπ_comp_of_smooth' f _
    exact meetLocus_strictTransformSeq_disjoinSeqAux (m + 1)
      ((disjoinCenter G (m + 2)).blowUpπ ≫ f)
      (isSnc_totalTransform_disjoinCenter f hF G hG (m + 1) hm) _
      (strictTransform_mem_range_totalTransform hG _)
      (meetLocus_strictTransform_disjoinCenter f hF G hG (m + 1) hm)

end Steps

section Sequence

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f] (E : DivisorFamily X) (hE : E.IsSnc)
include f hE

/-- Every center of the disjoining sequence is smooth over `k` [Kol07, 72]. -/
theorem disjoinSeq_isSmooth : (disjoinSeq E).IsSmooth f :=
  disjoinSeqAux_isSmooth _ f hE E.component (fun i => ⟨i, rfl⟩)
    (meetLocus_component_card_succ E)

/-- Every center of the disjoining sequence has simple normal crossings with the total transform
of `E` at its stage [Kol07, 72]. -/
theorem disjoinSeq_hasSncWith (i : Fin (disjoinSeq E).length) :
    ((disjoinSeq E).totalTransformSeq E i.castSucc).HasSncWith ((disjoinSeq E).center i) :=
  disjoinSeqAux_hasSncWith _ f hE E.component (fun i => ⟨i, rfl⟩)
    (meetLocus_component_card_succ E) i

/-- The total transform of `E` is snc at every stage of the disjoining sequence. -/
theorem isSnc_totalTransformSeq_disjoinSeq (i : Fin ((disjoinSeq E).length + 1)) :
    ((disjoinSeq E).totalTransformSeq E i).IsSnc :=
  isSnc_totalTransformSeq_disjoinSeqAux _ f hE E.component (fun i => ⟨i, rfl⟩)
    (meetLocus_component_card_succ E) i

/-- The final birational transforms of the components are pairwise disjoint [Kol07, 72]. -/
theorem meetLocus_strictTransformSeq_disjoinSeq :
    meetLocus (fun a => (disjoinSeq E).strictTransformSeq (E.component a) (Fin.last _)) 2 = ⊥ :=
  meetLocus_strictTransformSeq_disjoinSeqAux _ f hE E.component (fun i => ⟨i, rfl⟩)
    (meetLocus_component_card_succ E)

end Sequence

end Hironaka.Sequence
