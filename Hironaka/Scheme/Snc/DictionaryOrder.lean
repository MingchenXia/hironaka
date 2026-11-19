/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Snc.Dictionary
public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
public import Hironaka.Scheme.IdealSheaf.Order.Constructible
import Hironaka.Scheme.BlowUpSequence.Remark67
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.IdealSheaf.Order.Specialization
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded


/-!
# The dictionary, part I: orders, the component family, and clause (ii) of Main Theorem II

The first part of the translation between Hironaka's Main Theorem II [Hir64, Main Theorem II] and
Kollár's smooth blow-up sequences of order `d` [Kol07, Definition 66] (definitions in
`Hironaka/Scheme/Snc/Dictionary.lean`):

* orders: Hironaka's "`d` the maximum of `ν(J_x)`" (`IsGreatest (Set.range J.ord) d`) is Kollár's
  "`max-ord J = d`, attained" [Kol07, Definition 47] (`maxOrd_le_iff`, `le_maxOrd`);
* the component family: its members are the reduced irreducible components (`rfl`), they cover
  `V(E)` (every point of a closed set specializes from a generic point,
  `Closeds.exists_mem_genericPoints_specializes`), the reduced union of the family is the radical
  of `E` (Mathlib's `vanishingIdeal_support`), and a reduced closed subscheme's ideal sheaf is
  radical (its sections are kernels of surjections onto the reduced rings of sections of the
  subscheme, `Ideal.isRadical_iff_quotient_reduced`);
* clause (ii): along a smooth blow-up sequence of order `d` for `(X, J, F)` with `max-ord J = d`,
  every weak transform has `max-ord ≤ d` ([Kol07, Remark 67]: `IsOrderGeSeq.maxOrd_le` through
  `isOrderGeSeq_iff_isOrderSeq`, the marked and the unmarked transforms coinciding), `= d` at a
  stage with a nonempty center, and at every point of a center the order is `≥ d` by upper
  semicontinuity from the generic points (`ord_le_ord_of_specializes` on the stage, smooth of
  relative dimension `n` over `k` by `IsSmooth.stageMap_smoothOfRelativeDimension`), hence `= d`.
-/

public section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing Scheme
  DivisorFamily BlowUpSequence Scheme.IdealSheafData

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- Hironaka's "`d` is the maximum of the orders `ν(J_x)`" [Hir64, Main Theorem II] is Kollár's
"`max-ord J = d` and the maximum is attained" [Kol07, Definition 47]. -/
theorem isGreatest_range_ord_iff (J : X.IdealSheafData) (d : ℕ∞) :
    IsGreatest (Set.range J.ord) d ↔ J.maxOrd = d ∧ ∃ x, J.ord x = d := by
  constructor
  · rintro ⟨⟨x, hx⟩, hub⟩
    refine ⟨le_antisymm (J.maxOrd_le_iff.mpr fun y => hub ⟨y, rfl⟩) ?_, x, hx⟩
    rw [← hx]
    exact J.le_maxOrd x
  · rintro ⟨hmax, x, hx⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    rintro y ⟨z, rfl⟩
    exact hmax ▸ J.le_maxOrd z

/-- The member of `E.componentFamily` at the generic point `η` is the irreducible component
`closure {η}` with its reduced structure. -/
theorem componentFamily_component [NoetherianSpace X] (E : X.IdealSheafData)
    (η : E.support.genericPoints) :
    E.componentFamily.component η = IdealSheafData.vanishingIdeal (Closeds.closure {(η : X)}) := rfl

/-- The support of the reduced union of a family is the union of the supports of its members
(`coe_support_vanishingIdeal`). -/
theorem support_unionIdeal (F : DivisorFamily X) : F.unionIdeal.support = F.support :=
  Closeds.ext (by simp [DivisorFamily.unionIdeal])

/-- The irreducible components of `V(E)` cover `V(E)`: each `closure {η}` lies in the closed
`V(E)`, and every point of `V(E)` is a specialization of one of its generic points
(`Closeds.exists_mem_genericPoints_specializes`). -/
theorem support_componentFamily [NoetherianSpace X] (E : X.IdealSheafData) :
    E.componentFamily.support = E.support := by
  change (⨆ η : E.support.genericPoints, (IdealSheafData.vanishingIdeal (Closeds.closure
      {(η : X)})).support) =
    E.support
  apply le_antisymm
  · refine iSup_le fun η => ?_
    rw [← SetLike.coe_subset_coe]
    simp only [IdealSheafData.coe_support_vanishingIdeal]
    exact E.support.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr η.2.1)
  · intro x hx
    obtain ⟨η, hη, hspec⟩ := E.support.exists_mem_genericPoints_specializes hx
    refine le_iSup (fun η : E.support.genericPoints =>
      (IdealSheafData.vanishingIdeal (Closeds.closure {(η : X)})).support) ⟨η, hη⟩ ?_
    rw [← SetLike.mem_coe]
    simp only [IdealSheafData.coe_support_vanishingIdeal]
    exact specializes_iff_mem_closure.mp hspec

/-- The reduced union of the irreducible components of `V(E)` is the radical of `E`
(`support_componentFamily` and Mathlib's `vanishingIdeal_support`). -/
theorem unionIdeal_componentFamily [NoetherianSpace X] (E : X.IdealSheafData) :
    E.componentFamily.unionIdeal = E.radical := by
  unfold DivisorFamily.unionIdeal
  rw [support_componentFamily, IdealSheafData.vanishingIdeal_support]

/-- The ideal sheaf of a reduced closed subscheme (Hironaka's "`E` a reduced subscheme") is
radical: on each affine open its ideal is the kernel of the surjection onto the sections of the
subscheme (Mathlib's `ker_subschemeι_app`, `subschemeι_app_surjective`), a reduced ring, so the
ideal is radical (`Ideal.isRadical_iff_quotient_reduced`). -/
theorem radical_eq_self_of_isReduced_subscheme (E : X.IdealSheafData) [IsReduced E.subscheme] :
    E.radical = E := by
  refine Scheme.IdealSheafData.ext (funext fun U => ?_)
  change (E.ideal U).radical = E.ideal U
  rw [← E.ker_subschemeι_app U, Ideal.radical_eq_iff, Ideal.isRadical_iff_quotient_reduced]
  have hsurj : Function.Surjective (E.subschemeι.app U).hom := E.subschemeι_app_surjective U
  exact isReduced_of_injective (RingHom.quotientKerEquivOfSurjective hsurj).toRingHom
    (RingHom.quotientKerEquivOfSurjective hsurj).injective

/-- For a reduced `E` the reduced union of its irreducible components is `E`. -/
theorem unionIdeal_componentFamily_of_isReduced [NoetherianSpace X] (E : X.IdealSheafData)
    [IsReduced E.subscheme] : E.componentFamily.unionIdeal = E := by
  rw [unionIdeal_componentFamily, radical_eq_self_of_isReduced_subscheme]

/-- Every stage of a smooth blow-up sequence (`IsSmooth`: smooth centers of any shape) over an
equidimensional smooth `X` is smooth of the same relative dimension [Kol07, Notation 19]:
`smoothOfRelativeDimension_blowUpπ_comp_of_smooth` at each step. This is
`IsSmoothOfRelativeDimension.smoothOfRelativeDimension_stageMap` under the weaker hypothesis. -/
theorem IsSmooth.stageMap_smoothOfRelativeDimension [PerfectField k] {S : BlowUpSequence X}
    {f : X ⟶ Spec (.of k)} {n : ℕ} [SmoothOfRelativeDimension n f] (h : S.IsSmooth f)
    (i : Fin (S.length + 1)) : SmoothOfRelativeDimension n (S.stageMap i ≫ f) := by
  induction S with
  | nil Y =>
    change SmoothOfRelativeDimension n (𝟙 Y ≫ f)
    rw [Category.id_comp]
    infer_instance
  | cons Y D rest ih =>
    obtain ⟨hD, ht⟩ := (isSmooth_cons_iff f D rest).1 h
    have := hD
    have : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) :=
      smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
    rcases i with ⟨_ | j, hi⟩
    · change SmoothOfRelativeDimension n (𝟙 Y ≫ f)
      rw [Category.id_comp]
      infer_instance
    · change SmoothOfRelativeDimension n
        ((rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hi⟩ ≫ D.blowUpπ) ≫ f)
      rw [Category.assoc]
      exact ih ht ⟨j, Nat.lt_of_succ_lt_succ hi⟩

section OrderSeq

variable [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
  {S : BlowUpSequence X} {J : X.IdealSheafData} {F : DivisorFamily X} {d : ℕ}

include f n

/-- Along a smooth blow-up sequence of order `d` starting with `max-ord J = d`, every weak
transform `J_i` has `max-ord J_i ≤ d` ([Kol07, Lemma 61] iterated, as in [Kol07, Remark 67]; the
remark following [Hir64, Main Theorem II]): `IsOrderGeSeq.maxOrd_le` for the marked transforms,
which are the weak transforms (`IsOrderSeq.markedTransformSeq_eq_weakTransformSeq`). -/
theorem IsOrderSeq.maxOrd_weakTransformSeq_le (h : S.IsOrderSeq f J F d) (hmax : J.maxOrd = d)
    (i : Fin (S.length + 1)) : (S.weakTransformSeq J i).maxOrd ≤ d := by
  have h' : S.IsOrderGeSeq f J d F := (isOrderGeSeq_iff_isOrderSeq f n hmax).mpr h
  have := IsOrderGeSeq.maxOrd_le f n hmax h' i
  rwa [IsOrderSeq.markedTransformSeq_eq_weakTransformSeq f n h i] at this

/-- "`d` is the maximum of `ν(J_{i,z})` for all the points `z` of `X_i`" (the remark following
[Hir64, Main Theorem II]): at a stage with a nonempty center the maximal order of `J_i` is exactly
`d`; it is `d` at a generic point of the center ([Kol07, Definition 66 (4)]) and at most `d`
everywhere. -/
theorem IsOrderSeq.maxOrd_weakTransformSeq_eq (h : S.IsOrderSeq f J F d) (hmax : J.maxOrd = d)
    (i : Fin S.length) (hne : ((S.center i).support : Set (S.stage i.castSucc)).Nonempty) :
    (S.weakTransformSeq J i.castSucc).maxOrd = d := by
  refine le_antisymm (IsOrderSeq.maxOrd_weakTransformSeq_le f n h hmax i.castSucc) ?_
  obtain ⟨x, hx⟩ := hne
  obtain ⟨η, hη, -⟩ := (S.center i).support.exists_mem_genericPoints_specializes hx
  have hord : (S.weakTransformSeq J i.castSucc).ord η = d := (h.2 i).2 η hη
  rw [← hord]
  exact (S.weakTransformSeq J i.castSucc).le_maxOrd η

/-- Along a smooth blow-up sequence of order `d`, `ν(J_{i,x}) ≥ d` at every point `x` of the
center: the order is `d` at a generic point of the center specializing to `x`
([Kol07, Definition 66 (4)]), and it can only increase under specialization on the stage, smooth
of relative dimension `n` over `k`. The inequality of clause (ii) of [Hir64, Main Theorem II]. -/
theorem IsOrderSeq.le_ord_of_mem_center (h : S.IsOrderSeq f J F d) (i : Fin S.length)
    {x : S.stage i.castSucc} (hx : x ∈ (S.center i).support) :
    (d : ℕ∞) ≤ (S.weakTransformSeq J i.castSucc).ord x := by
  obtain ⟨η, hη, hspec⟩ := (S.center i).support.exists_mem_genericPoints_specializes hx
  have hord : (S.weakTransformSeq J i.castSucc).ord η = d := (h.2 i).2 η hη
  have : SmoothOfRelativeDimension n (S.stageMap i.castSucc ≫ f) :=
    IsSmooth.stageMap_smoothOfRelativeDimension h.1 i.castSucc
  have := (S.weakTransformSeq J i.castSucc).ord_le_ord_of_specializes
    (S.stageMap i.castSucc ≫ f) n hspec
  change (d : ℕ∞) ≤ (S.weakTransformSeq J i.castSucc).ord x
  rw [← hord]
  exact this

/-- Along a smooth blow-up sequence of order `d` starting with `max-ord J = d`, `ν(J_{i,x}) = d`
at every point of the center: clause (ii) of [Hir64, Main Theorem II] and clause (2) of
[Hir64, Main Theorem II(N)]. -/
theorem IsOrderSeq.ord_eq_of_mem_center (h : S.IsOrderSeq f J F d) (hmax : J.maxOrd = d)
    (i : Fin S.length) {x : S.stage i.castSucc} (hx : x ∈ (S.center i).support) :
    (S.weakTransformSeq J i.castSucc).ord x = d := by
  refine le_antisymm ?_ (IsOrderSeq.le_ord_of_mem_center f n h i hx)
  change (S.weakTransformSeq J i.castSucc).ord x ≤ d
  exact ((S.weakTransformSeq J i.castSucc).le_maxOrd x).trans
    (IsOrderSeq.maxOrd_weakTransformSeq_le f n h hmax i.castSucc)

end OrderSeq

end AlgebraicGeometry
