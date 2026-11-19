/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm36.Affine
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUpSequence.BaseChangeOrder
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.BlowUpSequence.RestrictedCenters
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The first-centre index along a flat surjection

The proof of [Kol07, Theorem 36] derives the functoriality of the resolution `BR(X)` of an affine
scheme under change of fields [Kol07, 34.2] and under smooth morphisms [Kol07, 34.1] from the
same properties of the principalization sequence `BP(A, I_X, ∅)` of the ambient: a change of
fields and (through [Kol07, Lemma 41]) a smooth morphism of the schemes are covered by flat
surjections of the ambients, along which the truncated restriction transports. This file proves
the transport, for an arbitrary flat surjection `p` of the ambients.

* `comap_le_comap_iff_of_flat_surjective`: the inverse image of ideal sheaves along a flat
  surjective morphism reflects inclusions (a descent lemma for flat morphisms whose range
  hypothesis a surjection satisfies trivially).
* `centerContains_pullback_iff_of_flat_surjective`, `firstCenterIndex_pullback_of_flat_surjective`:
  the pullback of a blow-up sequence along a flat surjection [Kol07, Definition 30, 30.1]
  transports the predicate "the `n`-th centre contains the strict transform" exactly, the centres
  and strict transforms of the pullback being the inverse images of those of the original and the
  stage lifts being flat and surjective; `firstCenterIndex_pullback_of_isIso` is the special
  case of an isomorphism.
* `BR_affine_eq_of_BP_eq_pullback_of_flat`: `BR_affine TA' emb = BR_affine TA (emb ≫ p)` for
  triples over two fields `k` and `L`, granted `BP TA' = (BP TA).pullback p` and
  `TA'.I = TA.I.comap p`.
* `flat_of_isBaseChangeOf`, `surjective_of_isBaseChangeOf`: the base-change morphism of a triple
  along a field extension is flat and surjective, being the base change of `Spec L → Spec k`; so
  the transport applies to it (the change-of-fields clause for `BR_affine`).

These lemmas are used for the change-of-fields and smooth-morphism clauses of Kollár's resolution
functor (`Hironaka.Resolution.Algebraic.Kol07.Thm36.BaseChangeAffine`) and for
the transport of the first centre along flat covers
(`Hironaka.Resolution.Algebraic.Kol07.Thm36.FirstCenterPullback`).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Hironaka Scheme BlowUpSequence

namespace Hironaka.Resolution

variable {X Y : Scheme.{u}}

/-! ### Inverse images along a flat surjection reflect inclusions -/

/-- Along a flat surjective morphism the inverse image of ideal sheaves reflects and preserves
inclusions (the descent lemma `le_of_comap_le_of_flat`; a surjection satisfies its range
hypothesis). -/
theorem comap_le_comap_iff_of_flat_surjective (f : Y ⟶ X) [Flat f] (hs : Function.Surjective f)
    {A B : X.IdealSheafData} : A.comap f ≤ B.comap f ↔ A ≤ B := by
  refine ⟨fun h => ?_, fun h => Scheme.IdealSheafData.comap_mono f h⟩
  refine Scheme.IdealSheafData.le_of_comap_le_of_flat f B A ?_ h
  rw [Set.range_eq_univ.mpr hs]
  exact Set.subset_univ _

/-! ### The first-centre index along a flat surjection -/

/-- The predicate "the `n`-th centre contains the strict transform" transports exactly along the
pullback of a sequence along a flat surjective morphism [Kol07, Definition 30, 30.1]: the centres
and strict transforms of the pullback are the inverse images of those of the original. -/
theorem centerContains_pullback_iff_of_flat_surjective (S : BlowUpSequence X) (p : Y ⟶ X) [Flat p]
    (hs : Function.Surjective p) (I : X.IdealSheafData) (n : ℕ) :
    CenterContains (S.pullback p) (I.comap p) n ↔ CenterContains S I n := by
  constructor
  · rintro ⟨hn, h⟩
    have hn' : n < S.length := by rwa [length_pullback] at hn
    refine ⟨hn', ?_⟩
    have e1 : (S.pullback p).center ⟨n, hn⟩ =
        (S.center ⟨n, hn'⟩).comap (S.pullbackStageHom p ⟨n, Nat.lt_succ_of_lt hn'⟩) :=
      center_pullback_mk S p n hn'
    have e2 : (S.pullback p).strictTransformSeq (I.comap p) ⟨n, Nat.lt_succ_of_lt hn⟩ =
        (S.strictTransformSeq I ⟨n, Nat.lt_succ_of_lt hn'⟩).comap
          (S.pullbackStageHom p ⟨n, Nat.lt_succ_of_lt hn'⟩) :=
      strictTransformSeq_pullback_mk S p I n (Nat.lt_succ_of_lt hn')
    rw [e1, e2] at h
    have := flat_pullbackStageHom S p ⟨n, Nat.lt_succ_of_lt hn'⟩
    exact (comap_le_comap_iff_of_flat_surjective _
      (surjective_pullbackStageHom S p hs ⟨n, Nat.lt_succ_of_lt hn'⟩)).mp h
  · rintro ⟨hn, h⟩
    have hn' : n < (S.pullback p).length := by rwa [length_pullback]
    refine ⟨hn', ?_⟩
    have e1 : (S.pullback p).center ⟨n, hn'⟩ =
        (S.center ⟨n, hn⟩).comap (S.pullbackStageHom p ⟨n, Nat.lt_succ_of_lt hn⟩) :=
      center_pullback_mk S p n hn
    have e2 : (S.pullback p).strictTransformSeq (I.comap p) ⟨n, Nat.lt_succ_of_lt hn'⟩ =
        (S.strictTransformSeq I ⟨n, Nat.lt_succ_of_lt hn⟩).comap
          (S.pullbackStageHom p ⟨n, Nat.lt_succ_of_lt hn⟩) :=
      strictTransformSeq_pullback_mk S p I n (Nat.lt_succ_of_lt hn)
    rw [e1, e2]
    have := flat_pullbackStageHom S p ⟨n, Nat.lt_succ_of_lt hn⟩
    exact (comap_le_comap_iff_of_flat_surjective _
      (surjective_pullbackStageHom S p hs ⟨n, Nat.lt_succ_of_lt hn⟩)).mpr h

/-- The first-centre index of the pullback of a sequence along a flat surjection, for the
pulled-back ideal sheaf, is the first-centre index of the original;
`firstCenterIndex_pullback_of_isIso` is the special case of an isomorphism. -/
theorem firstCenterIndex_pullback_of_flat_surjective (S : BlowUpSequence X) (p : Y ⟶ X) [Flat p]
    (hs : Function.Surjective p) (I : X.IdealSheafData) :
    firstCenterIndex (S.pullback p) (I.comap p) = firstCenterIndex S I := by
  have hp : CenterContains (S.pullback p) (I.comap p) = CenterContains S I :=
    funext fun n => propext (centerContains_pullback_iff_of_flat_surjective S p hs I n)
  unfold firstCenterIndex
  rw [hp, length_pullback]

/-! ### `BR_affine` along a flat surjection of the ambients -/

section BRAffine

variable {k L : Type u} [Field k] [CharZero k] [Field L] [CharZero L]

/-- `BR_affine` transports along a flat surjection `p` of the ambients of two triples, over two
fields, granted that the principalization sequences correspond: if `BP TA' = (BP TA).pullback p`
and `TA'.I = TA.I.comap p`, then `BR_affine TA' emb = BR_affine TA (emb ≫ p)`. The first-centre
index is the same (`firstCenterIndex_pullback_of_flat_surjective`) and truncation commutes with
the pullback. This is how [Kol07, Theorem 36, proof] derives 34.1 and 34.2 for `BR` from `BP`. -/
theorem BR_affine_eq_of_BP_eq_pullback_of_flat (TA : Triple k) (TA' : Triple L)
    (p : TA'.X.left ⟶ TA.X.left) [Flat p] (hs : Function.Surjective p)
    (hBP : Hironaka.Sequence.BP TA' = (Hironaka.Sequence.BP TA).pullback p)
    (hI : TA'.I = TA.I.comap p) {Z : Scheme.{u}} (emb : Z ⟶ TA'.X.left) :
    BR_affine TA' emb = BR_affine TA (emb ≫ p) := by
  unfold BR_affine
  rw [hBP, hI, firstCenterIndex_pullback_of_flat_surjective _ _ hs, ← take_pullback, pullback_comp]

omit [CharZero k] [CharZero L] in
/-- The base-change morphism of a triple along a change of fields `σ : k → L`
(`Triple.IsBaseChangeOf`) is flat: it is the base change of the flat morphism `Spec L → Spec k`
(`flat_of_isPullback_specMap`). -/
theorem flat_of_isBaseChangeOf (σ : k →+* L) (TA : Triple k) (TA' : Triple L)
    (p : TA'.X.left ⟶ TA.X.left) (h : TA'.IsBaseChangeOf TA σ p) : Flat p :=
  flat_of_isPullback_specMap h.1

omit [CharZero k] [CharZero L] in
/-- The base-change morphism of a triple along a change of fields is surjective: it is the base
change of the surjective morphism `Spec L → Spec k` (`surjective_of_isPullback_specMap`). -/
theorem surjective_of_isBaseChangeOf (σ : k →+* L) (TA : Triple k) (TA' : Triple L)
    (p : TA'.X.left ⟶ TA.X.left) (h : TA'.IsBaseChangeOf TA σ p) : Function.Surjective p :=
  surjective_of_isPullback_specMap h.1

end BRAffine

end Hironaka.Resolution
