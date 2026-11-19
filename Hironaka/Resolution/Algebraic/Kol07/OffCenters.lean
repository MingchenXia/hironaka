/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Basic
import Hironaka.Resolution.Algebraic.Snc.DictionaryBoundary
import Hironaka.Scheme.BlowUp.Composite
import Hironaka.Scheme.BlowUpSequence.Pullback
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.Snc.TotalTransformOffCentre
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The total exceptional locus and the points off the centers

The total exceptional set of a sequence of blow-ups is
`Ex_tot(Π) := ⋃_i (π_i ∘ ⋯ ∘ π_{r−1})⁻¹(Z_i)`, the union of the preimages of the centers
[Kol07, Definition 25], and a blow-up is an isomorphism
off its center, so the composite `Π_i` is a local isomorphism at every point of `X_i` lying over
no center, with the strict transform there the pull-back of the subscheme. The proof of
resolution from principalization needs both facts along a sequence, at the level of points and
stalks ("`g⁻¹(Sing X̄) = Z_j ∩ Ex_tot(π_0 ⋯ π_{j−1})`" in the proof of [Kol07, Theorem 27]):

* `mem_support_totalTransformSeq_iff`: a point of the `i`-th stage lies on the total transform of
  the family `E` iff it lies over `E` or over one of the earlier centers ([Kol07, Definition 25],
  by induction from the one-step `support_totalTransform_eq`).
* `isIso_stalkMap_stageMap_of_forall_notMem`, `stalkIdeal_strictTransformSeq_of_forall_notMem`:
  at a point over no earlier center the stage map is an isomorphism on stalks and the strict
  transform's stalk is the image of the subscheme's stalk (the one-step
  `isIso_stalkMap_π_of_notMem_support` and `stalkIdeal_strictTransformAlong_of_notMem_support`,
  composed along the stages; the pointwise form of `isIso_over_of_centers_disjoint`).

The schemes are arbitrary, locally Noetherian where the support law of the strict transform
needs it.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme IdealSheafData BlowUpSequence
  TopologicalSpace

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### The support of the total transform along a sequence -/

/-- `support_totalTransform_eq`, pointwise: a point of the blow-up lies on the total transform of
`F` iff its image lies on `F` or on the center. -/
theorem mem_support_totalTransform_iff [IsLocallyNoetherian X] (F : DivisorFamily X)
    (D : X.IdealSheafData) (x' : D.blowUp) :
    x' ∈ (F.totalTransform D).support ↔
      D.blowUpπ x' ∈ F.support ∨ D.blowUpπ x' ∈ D.support := by
  rw [← SetLike.mem_coe, support_totalTransform_eq, Closeds.coe_sup, Closeds.coe_preimage,
    Closeds.coe_preimage, Set.mem_union, Set.mem_preimage, Set.mem_preimage, SetLike.mem_coe,
    SetLike.mem_coe]

/-- The total exceptional set [Kol07, Definition 25], in the `⟨j, hj⟩` form: a point of the
`j`-th stage lies on the total transform of `E` iff its image lies on `E` or its image at some
earlier stage `m < j` lies on the center `Z_m`. -/
theorem mem_support_totalTransformSeq_iff_mk : ∀ {X : Scheme.{u}} (S : BlowUpSequence X)
    [IsLocallyNoetherian X] (E : DivisorFamily X) (j : ℕ) (hj : j < S.length + 1)
    (p : S.stage ⟨j, hj⟩),
    p ∈ (S.totalTransformSeq E ⟨j, hj⟩).support ↔
      S.stageMap ⟨j, hj⟩ p ∈ E.support ∨
        ∃ (m : ℕ) (hm : m < S.length) (hmj : m < j),
          S.stageMapBetween ⟨j, hj⟩ ⟨m, Nat.lt_succ_of_lt hm⟩ (Nat.le_of_lt hmj) p ∈
            (S.center ⟨m, hm⟩).support
  | _, nil Y, _, E, j, hj, p => by
    obtain rfl : j = 0 := Nat.lt_one_iff.mp hj
    refine ⟨fun h => Or.inl h, fun h => ?_⟩
    rcases h with h | ⟨m, hm, -⟩
    · exact h
    · exact absurd hm (Nat.not_lt_zero _)
  | _, cons Y D rest, _, E, 0, hj, p => by
    refine ⟨fun h => Or.inl h, fun h => ?_⟩
    rcases h with h | ⟨m, -, hmj, -⟩
    · exact h
    · exact absurd hmj (Nat.not_lt_zero _)
  | _, cons Y D rest, _, E, j + 1, hj, p => by
    have : IsLocallyNoetherian D.blowUp := blowUp.isLocallyNoetherian D
    revert p
    change ∀ p : rest.stage ⟨j, Nat.lt_of_succ_lt_succ hj⟩,
      p ∈ (rest.totalTransformSeq (E.totalTransform D) ⟨j, _⟩).support ↔
        D.blowUpπ (rest.stageMap ⟨j, _⟩ p) ∈ E.support ∨
          ∃ (m : ℕ) (hm : m < rest.length + 1) (hmj : m < j + 1),
            (cons Y D rest).stageMapBetween ⟨j + 1, hj⟩ ⟨m, Nat.lt_succ_of_lt hm⟩
              (Nat.le_of_lt hmj) p ∈ ((cons Y D rest).center ⟨m, hm⟩).support
    intro p
    have ih := mem_support_totalTransformSeq_iff_mk rest (E.totalTransform D) j
      (Nat.lt_of_succ_lt_succ hj) p
    rw [ih, mem_support_totalTransform_iff]
    constructor
    · rintro (⟨h | h⟩ | ⟨m, hm, hmj, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨0, Nat.succ_pos _, Nat.succ_pos _, h⟩
      · exact Or.inr ⟨m + 1, Nat.succ_lt_succ hm, Nat.succ_lt_succ hmj, h⟩
    · rintro (h | ⟨m, hm, hmj, h⟩)
      · exact Or.inl (Or.inl h)
      · rcases m with _ | m
        · exact Or.inl (Or.inr h)
        · exact Or.inr ⟨m, Nat.lt_of_succ_lt_succ hm, Nat.lt_of_succ_lt_succ hmj, h⟩

/-- A point of a stage lies on the total transform of `E` iff it lies over `E` or over one of the
earlier centers [Kol07, Definition 25]. -/
theorem mem_support_totalTransformSeq_iff [IsLocallyNoetherian X] (S : BlowUpSequence X)
    (E : DivisorFamily X) (i : Fin (S.length + 1)) (p : S.stage i) :
    p ∈ (S.totalTransformSeq E i).support ↔
      S.stageMap i p ∈ E.support ∨
        ∃ (m : Fin S.length) (hmi : m.val < i.val),
          S.stageMapBetween i m.castSucc (Nat.le_of_lt hmi) p ∈ (S.center m).support := by
  obtain ⟨j, hj⟩ := i
  rw [mem_support_totalTransformSeq_iff_mk]
  constructor
  · rintro (h | ⟨m, hm, hmj, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨⟨m, hm⟩, hmj, h⟩
  · rintro (h | ⟨⟨m, hm⟩, hmj, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨m, hm, hmj, h⟩

/-! ### Off the centers: stalk isomorphisms and the strict transform -/

/-- The identity's stalk map is the identity on ideals. -/
theorem stalkIdeal_map_stalkMap_id (J : X.IdealSheafData) (p : X) :
    (J.stalkIdeal ((𝟙 X : X ⟶ X) p)).map ((𝟙 X : X ⟶ X).stalkMap p).hom = J.stalkIdeal p := by
  rw [Scheme.Hom.stalkMap_id]
  exact Ideal.map_id _

/-- A blow-up is an isomorphism off its center, along a sequence, pointwise, in the `⟨j, hj⟩`
form: at a point of the `j`-th stage lying over no earlier center, the stage map is an
isomorphism on stalks and the strict transform of `J` has the stalk of the pull-back of `J`. -/
theorem isIso_stalkMap_stageMap_and_stalkIdeal_strictTransformSeq_mk :
    ∀ {X : Scheme.{u}} (S : BlowUpSequence X) (J : X.IdealSheafData) (j : ℕ) (hj : j < S.length + 1)
      (p : S.stage ⟨j, hj⟩),
      (∀ (m : ℕ) (hm : m < S.length) (hmj : m < j),
        S.stageMapBetween ⟨j, hj⟩ ⟨m, Nat.lt_succ_of_lt hm⟩ (Nat.le_of_lt hmj) p ∉
          (S.center ⟨m, hm⟩).support) →
      IsIso ((S.stageMap ⟨j, hj⟩).stalkMap p) ∧
        (S.strictTransformSeq J ⟨j, hj⟩).stalkIdeal p =
          (J.stalkIdeal (S.stageMap ⟨j, hj⟩ p)).map ((S.stageMap ⟨j, hj⟩).stalkMap p).hom
  | _, nil Y, J, j, hj, p, _ => by
    obtain rfl : j = 0 := Nat.lt_one_iff.mp hj
    exact ⟨isIso_stalkMap_id Y p, (stalkIdeal_map_stalkMap_id J p).symm⟩
  | _, cons Y D rest, J, 0, hj, p, _ =>
    ⟨isIso_stalkMap_id Y p, (stalkIdeal_map_stalkMap_id J p).symm⟩
  | _, cons Y D rest, J, j + 1, hj, p, h => by
    revert p h
    change ∀ (p : rest.stage ⟨j, Nat.lt_of_succ_lt_succ hj⟩),
      (∀ (m : ℕ) (hm : m < rest.length + 1) (hmj : m < j + 1),
        (cons Y D rest).stageMapBetween ⟨j + 1, hj⟩ ⟨m, Nat.lt_succ_of_lt hm⟩ (Nat.le_of_lt hmj) p ∉
          ((cons Y D rest).center ⟨m, hm⟩).support) →
      IsIso ((rest.stageMap ⟨j, _⟩ ≫ D.blowUpπ).stalkMap p) ∧
        (rest.strictTransformSeq (J.strictTransform D) ⟨j, _⟩).stalkIdeal p =
          (J.stalkIdeal (D.blowUpπ (rest.stageMap ⟨j, _⟩ p))).map
            ((rest.stageMap ⟨j, _⟩ ≫ D.blowUpπ).stalkMap p).hom
    intro p h
    have h0 : D.blowUpπ (rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hj⟩ p) ∉ D.support :=
      h 0 (Nat.succ_pos _) (Nat.succ_pos _)
    have hy : rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hj⟩ p ∉
        (D.comap D.blowUpπ).support := by
      rw [mem_support_comap_iff_apply]
      exact h0
    have h' : ∀ (m : ℕ) (hm : m < rest.length) (hmj : m < j),
        rest.stageMapBetween ⟨j, Nat.lt_of_succ_lt_succ hj⟩ ⟨m, Nat.lt_succ_of_lt hm⟩
          (Nat.le_of_lt hmj) p ∉ (rest.center ⟨m, hm⟩).support :=
      fun m hm hmj => h (m + 1) (Nat.succ_lt_succ hm) (Nat.succ_lt_succ hmj)
    obtain ⟨h1, h2⟩ := isIso_stalkMap_stageMap_and_stalkIdeal_strictTransformSeq_mk rest
      (J.strictTransform D) j (Nat.lt_of_succ_lt_succ hj) p h'
    have hiso : IsIso (D.blowUpπ.stalkMap (rest.stageMap ⟨j,
        Nat.lt_of_succ_lt_succ hj⟩ p)) :=
      isIso_stalkMap_π_of_notMem_support D hy
    have hone : (J.strictTransform D).stalkIdeal (rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hj⟩ p) =
        (J.stalkIdeal (D.blowUpπ (rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hj⟩ p))).map
          (D.blowUpπ.stalkMap (rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hj⟩ p)).hom :=
      stalkIdeal_strictTransformAlong_of_notMem_support D J hy
    refine ⟨?_, ?_⟩
    · rw [Scheme.Hom.stalkMap_comp]
      exact IsIso.comp_isIso' hiso h1
    · rw [h2, hone, Ideal.map_map, Scheme.Hom.stalkMap_comp]
      rfl

/-- At a point over no earlier center the stage map is an isomorphism on stalks (a blow-up is an
isomorphism off its center). -/
theorem isIso_stalkMap_stageMap_of_forall_notMem (S : BlowUpSequence X) (i : Fin (S.length + 1))
    (p : S.stage i)
    (h : ∀ (m : Fin S.length) (hmi : m.val < i.val),
      S.stageMapBetween i m.castSucc (Nat.le_of_lt hmi) p ∉ (S.center m).support) :
    IsIso ((S.stageMap i).stalkMap p) := by
  obtain ⟨j, hj⟩ := i
  exact (isIso_stalkMap_stageMap_and_stalkIdeal_strictTransformSeq_mk S ⊥ j hj p
    fun m hm hmj => h ⟨m, hm⟩ hmj).1

/-- At a point over no earlier center the strict transform of `J` has the stalk of the pull-back
(the birational transform of [Kol07, 30.2] off the centers). -/
theorem stalkIdeal_strictTransformSeq_of_forall_notMem (S : BlowUpSequence X)
    (J : X.IdealSheafData) (i : Fin (S.length + 1)) (p : S.stage i)
    (h : ∀ (m : Fin S.length) (hmi : m.val < i.val),
      S.stageMapBetween i m.castSucc (Nat.le_of_lt hmi) p ∉ (S.center m).support) :
    (S.strictTransformSeq J i).stalkIdeal p =
      (J.stalkIdeal (S.stageMap i p)).map ((S.stageMap i).stalkMap p).hom := by
  obtain ⟨j, hj⟩ := i
  exact (isIso_stalkMap_stageMap_and_stalkIdeal_strictTransformSeq_mk S J j hj p
    fun m hm hmj => h ⟨m, hm⟩ hmj).2

end Hironaka.Sequence
