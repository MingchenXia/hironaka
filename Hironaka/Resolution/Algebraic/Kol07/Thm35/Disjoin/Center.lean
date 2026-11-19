/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.MeetLocus
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.IdealSheaf.StalkLe
import Hironaka.Scheme.Snc.HasSncWith
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The center of a disjoining step is smooth and has normal crossings with the family

Kollár's next center `Z_1 ⊂ X_1` is the subset where `k − 1` of the `(π_0)^{-1}_* E_i` intersect,
and "`Z_1` is smooth since" these transforms have no `k`-fold intersections [Kol07, 72]. At a
point `x`
of the meet locus at multiplicity `m + 1` exactly `m + 1` members pass (at least `m + 1` by
membership, at most `m + 1` since there are no `(m+2)`-fold intersections); the coordinates `z` at
`x` of [Kol07, Definition 24] for the snc family the members belong to make those members the
coordinate hyperplanes `z_{c(i)} = 0`, and the center `∏_{|s| = m+1} ∑_{i ∈ s} G_i` has stalk
`(z_{c(i)} : i through x)`: the factor for the set of members through `x` is that ideal, every
other `(m+1)`-set contains a member missing `x`, whose stalk is the unit ideal, so its factor is
the unit ideal. Hence the center has simple normal crossings with the family
([Kol07, Definition 24 (4)]), and is smooth over `k`.

* `mem_meetLocus_iff_le_card`: `x` lies on at least `m` members iff the set of members through `x`
  has at least `m` elements.
* `exists_stalkIdeal_disjoinCenter_eq_span`: the stalk computation.
* `hasSncWith_disjoinCenter`, `smooth_disjoinCenter`: one disjoining step.
* `isRegular_subscheme_of_hasSncWith`, `smooth_of_hasSncWith`: a closed subscheme with simple
  normal crossings with a family is regular, and smooth over a perfect field; restatements of
  `AlgebraicGeometry.HasSncWith.isRegular` and `HasSncWith.smooth` under the names used here.
-/

public section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing Ideal Scheme
  Scheme.IdealSheafData

namespace Hironaka.Sequence

variable {X : Scheme.{u}}

/-- The stalk of a supremum over a finite set is the supremum of the stalks. -/
theorem stalkIdeal_biSup_finset {σ : Type*} (s : Finset σ) (J : σ → X.IdealSheafData) (x : X) :
    (⨆ i ∈ s, J i).stalkIdeal x = ⨆ i ∈ s, (J i).stalkIdeal x := by
  rw [iSup_subtype', iSup_subtype', IdealSheafData.stalkIdeal_iSup]

section MeetLocus

variable {ι : Type*} [Fintype ι]

/-- `x` lies on at least `m` members of `G` iff at least `m` members pass through `x`. -/
theorem mem_meetLocus_iff_le_card (G : ι → X.IdealSheafData) (m : ℕ) (x : X)
    [DecidablePred fun i => x ∈ (G i).support] :
    x ∈ meetLocus G m ↔
      m ≤ ((Finset.univ : Finset ι).filter fun i => x ∈ (G i).support).card := by
  classical
  rw [mem_meetLocus_iff]
  constructor
  · rintro ⟨s, hs, hx⟩
    rw [← hs]
    exact Finset.card_le_card fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ i, hx i hi⟩
  · intro h
    obtain ⟨t, ht, htc⟩ := Finset.exists_subset_card_eq h
    exact ⟨t, htc, fun i hi => (Finset.mem_filter.mp (ht hi)).2⟩

/-- At a point `x` of the meet locus at multiplicity `m + 1`, for members `G` of a family with
Kollár's coordinates `z` at `x` and no `(m+2)`-fold intersections, the center's stalk is generated
by the coordinates of the members through `x` [Kol07, 72]. -/
theorem exists_stalkIdeal_disjoinCenter_eq_span {F : DivisorFamily X} (G : ι → X.IdealSheafData)
    (hG : ∀ i, G i ∈ Set.range F.component) {m : ℕ} (hm : meetLocus G (m + 2) = ⊥) {x : X}
    (hx : x ∈ meetLocus G (m + 1)) {n : ℕ} {z : Fin n → X.presheaf.stalk x}
    (hz : F.IsSncAt x z) :
    ∃ s : Finset (Fin n), (disjoinCenter G (m + 1)).stalkIdeal x = span (z '' ↑s) ∧
      (∀ i, x ∈ (G i).support → ∃ j ∈ s, (G i).stalkIdeal x = span {z j}) ∧
      ∀ j ∈ s, ∃ i, x ∈ (G i).support ∧ (G i).stalkIdeal x = span {z j} := by
  classical
  obtain ⟨-, c, -, hc⟩ := hz
  set T := (Finset.univ : Finset ι).filter (fun i => x ∈ (G i).support) with hT
  have hTcard : T.card = m + 1 := by
    refine le_antisymm ?_ ((mem_meetLocus_iff_le_card G _ x).mp hx)
    by_contra h
    have hx2 : x ∈ meetLocus G (m + 2) :=
      (mem_meetLocus_iff_le_card G _ x).mpr (by rw [← hT]; omega)
    rw [hm] at hx2
    simp only [← SetLike.mem_coe, Closeds.coe_bot, Set.mem_empty_iff_false] at hx2
  have hstalk : ∀ i ∈ T, ∃ j : Fin n, (G i).stalkIdeal x = span {z j} := by
    intro i hi
    obtain ⟨a, ha⟩ := hG i
    have hxa : x ∈ (F.component a).support := ha ▸ (Finset.mem_filter.mp hi).2
    exact ⟨c ⟨a, hxa⟩, by rw [← ha]; exact hc ⟨a, hxa⟩⟩
  have hne : Nonempty (Fin n) := by
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
    exact ⟨(hstalk i hi).choose⟩
  choose! g hg using hstalk
  refine ⟨T.image g, ?_, fun i hi => ?_, fun j hj => ?_⟩
  rotate_left
  · have hiT : i ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
    exact ⟨g i, Finset.mem_image_of_mem g hiT, hg i hiT⟩
  · obtain ⟨i, hiT, rfl⟩ := Finset.mem_image.mp hj
    exact ⟨i, (Finset.mem_filter.mp hiT).2, hg i hiT⟩
  unfold disjoinCenter
  rw [IdealSheafData.stalkIdeal_finset_prod, Finset.prod_eq_single T]
  · rw [stalkIdeal_biSup_finset, Finset.coe_image, Set.image_image, Set.image_eq_iUnion,
      Ideal.span_iUnion]
    exact iSup_congr fun i => by
      rw [Ideal.span_iUnion]
      exact iSup_congr fun hi => hg i (Finset.mem_coe.mp hi)
  · intro s hs hsT
    have hns : ¬ s ⊆ T := fun h => hsT (Finset.eq_of_subset_of_card_le h
      (by rw [hTcard, (Finset.mem_powersetCard.mp hs).2]))
    obtain ⟨i, his, hiT⟩ := Finset.not_subset.mp hns
    have hi : x ∉ (G i).support := fun h => hiT (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
    rw [stalkIdeal_biSup_finset, Ideal.one_eq_top, eq_top_iff]
    exact le_iSup₂_of_le i his (IdealSheafData.stalkIdeal_eq_top_of_notMem_support _ hi).ge
  · intro h
    exact absurd (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hTcard⟩) h

/-- "`Z_1` is smooth since the `(π_0)^{-1}_* E_i` do not have any `k`-fold intersections"
[Kol07, 72]: the center at multiplicity `m + 1` of members of an snc family with no `(m+2)`-fold
intersections has simple normal crossings with the family ([Kol07, Definition 24 (4)]). -/
theorem hasSncWith_disjoinCenter {F : DivisorFamily X} (hF : F.IsSnc) (G : ι → X.IdealSheafData)
    (hG : ∀ i, G i ∈ Set.range F.component) (m : ℕ) (hm : meetLocus G (m + 2) = ⊥) :
    F.HasSncWith (disjoinCenter G (m + 1)) := by
  intro x hx
  rw [support_disjoinCenter] at hx
  obtain ⟨n, z, hz⟩ := hF.2 x
  obtain ⟨s, hs, -, -⟩ := exists_stalkIdeal_disjoinCenter_eq_span G hG hm hx hz
  exact ⟨n, z, hz, s, hs⟩

end MeetLocus

section Smooth

variable {k : Type u} [Field k]

/-- A closed subscheme with simple normal crossings with a family is regular ("in particular, `Z`
is smooth", [Kol07, Definition 24]); a restatement of `AlgebraicGeometry.HasSncWith.isRegular` under
the name used in this directory. -/
theorem isRegular_subscheme_of_hasSncWith (f : X ⟶ Spec (.of k)) [Smooth f] {E : DivisorFamily X}
    {Z : X.IdealSheafData} (h : E.HasSncWith Z) : IsRegular Z.subscheme :=
  HasSncWith.isRegular f h

/-- A closed subscheme with simple normal crossings with a family is smooth over the perfect
ground field (regular and smooth agree over a perfect field); a restatement of
`AlgebraicGeometry.HasSncWith.smooth` under the name used in this directory. -/
theorem smooth_of_hasSncWith [PerfectField k] (f : X ⟶ Spec (.of k)) [Smooth f]
    {E : DivisorFamily X} {Z : X.IdealSheafData} (h : E.HasSncWith Z) :
    Smooth (Z.subschemeι ≫ f) :=
  HasSncWith.smooth f h

/-- The center of a disjoining step is smooth over `k` [Kol07, 72]. -/
theorem smooth_disjoinCenter [PerfectField k] (f : X ⟶ Spec (.of k)) [Smooth f]
    {F : DivisorFamily X} (hF : F.IsSnc) {ι : Type*} [Fintype ι] (G : ι → X.IdealSheafData)
    (hG : ∀ i, G i ∈ Set.range F.component) (m : ℕ) (hm : meetLocus G (m + 2) = ⊥) :
    Smooth ((disjoinCenter G (m + 1)).subschemeι ≫ f) :=
  smooth_of_hasSncWith f (hasSncWith_disjoinCenter hF G hG m hm)

end Smooth

end Hironaka.Sequence
