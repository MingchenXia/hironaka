/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Descent
public import Hironaka.Scheme.BlowUp.BlowUpMap.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Hironaka.Scheme.BlowUp.BlowUpMap
import Hironaka.Scheme.Smooth.ExceptionalChart
import Hironaka.Scheme.Smooth.ExceptionalDivisor
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# The exceptional divisor under a flat base change

The smoothness of `F → Z` of relative dimension `r − 1` for a smooth blow-up over an arbitrary
field `k` (`Hironaka/Scheme/Smooth/ExceptionalDivisorSmooth.lean`) is obtained from its
perfect-field form (`Hironaka/Scheme/Smooth/ExceptionalDivisor.lean`) by base change to a perfect
extension field `K` of `k` and descent along `Spec K → Spec k`
(`Hironaka/Scheme/Smooth/DescentRelativeDimension.lean`). This file is the base-change bookkeeping.

**Why the lemmas hold.** Blowing up commutes with flat base change ([Sta, Tag 0805]: for flat
`h : Y ⟶ X`, `B_{h⁻¹Z} Y = Y ×_X B_Z X`, the square `isPullback_blowUpMap`). The exceptional
divisor of `B_{h⁻¹Z} Y` is the inverse image of that of `B_Z X` along the projection (inverse
images of ideal sheaves compose and the square commutes), so the exceptional divisors form a
cartesian square over `h`, and, cancelling the square `h⁻¹Z = Y ×_X Z` of the centers from the
bottom, `F_Y → Z_Y` is the base change of `F → Z` along `Z_Y → Z`
(`isPullback_exceptionalMap_of_flat`). For `Y = X ×_k K` with `K/k` a field extension:
`X_K → Spec K` is smooth of relative dimension `n` and `Z_K → Spec K` of relative dimension `n − r`
as base changes (Mathlib's `smoothOfRelativeDimension_isStableUnderBaseChange`), and `Z_K → Z` is
surjective, flat and quasi-compact as the base change of `Spec K → Spec k` (every morphism to
`Spec k` is flat, `flat_of_field`, stalkwise since a ring map out of a ring isomorphic to a field
is flat, `RingHom.Flat.of_ringEquiv_field`; `Spec` of a field extension is surjective between
one-point spaces and affine).

## Main declarations

* `AlgebraicGeometry.comap_π_comap_eq_comap_blowUpMap`: the exceptional divisor of the base-changed
  blow-up is the inverse image of `F` along `blowUpMap`.
* `AlgebraicGeometry.isPullback_exceptionalMap_of_flat`: `F_Y → Z_Y` is the base change of `F → Z`.
* `AlgebraicGeometry.smoothOfRelativeDimension_pullback_snd_fieldExtension`,
  `isPullback_subschemeMap_comap_fst`, `smoothOfRelativeDimension_subschemeι_comap_fst_comp`,
  `fpqcCover_subschemeMap_comap_fst`: the field-extension base change.
* `AlgebraicGeometry.smoothOfRelativeDimension_subschemeMap_exceptional_of_descendsAlong`: the
  smoothness of `F → Z` over any field from its perfect-field form, given the descent of
  smoothness of relative dimension `r − 1` along fpqc coverings as a hypothesis (supplied by
  `descendsAlong_smoothOfRelativeDimension` where the two are combined).
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory Limits Scheme.IdealSheafData

namespace AlgebraicGeometry

section Field

/-- A ring map out of a ring isomorphic to a field is flat: every vector space is free, and
flatness passes along the isomorphism. -/
theorem _root_.RingHom.Flat.of_ringEquiv_field {k A B : Type*} [Field k] [CommRing A] [CommRing B]
    (e : k ≃+* A) (φ : A →+* B) : φ.Flat := by
  have h : φ = (φ.comp e.toRingHom).comp e.symm.toRingHom := by
    ext x
    simp
  rw [h]
  refine RingHom.Flat.comp (RingHom.Flat.of_bijective e.symm.bijective) ?_
  algebraize [φ.comp e.toRingHom]
  exact Module.Flat.of_free

/-- Every morphism to the spectrum of a field is flat: at each point the stalk of `Spec k` is `k`
(`isIso_toStalk_Spec_of_field`) and a ring map out of a field is flat.  This is the hypothesis
under which Hauser's product formula over a field [Hau14, Corollary 5.2 (e)] is flat base change
along the projection. -/
theorem flat_of_field {k : Type u} [Field k] {Z : Scheme.{u}} (f : Z ⟶ Spec (.of k)) : Flat f := by
  refine Flat.of_stalkMap f fun z => ?_
  have := isIso_toStalk_Spec_of_field (f z)
  exact RingHom.Flat.of_ringEquiv_field
    (asIso (StructureSheaf.toStalk k (f z))).commRingCatIsoToRingEquiv (f.stalkMap z).hom

end Field

end AlgebraicGeometry

namespace AlgebraicGeometry

open AlgebraicGeometry Scheme.Hom

section FlatBaseChange

variable {X Y : Scheme.{u}} (h : Y ⟶ X) (Z : X.IdealSheafData)

/-- The exceptional divisor of `B_{h⁻¹Z} Y` is the inverse image of the exceptional divisor of
`B_Z X` along `blowUpMap h Z` (`π_Y ≫ h = blowUpMap ≫ π`, and inverse images compose). -/
theorem comap_π_comap_eq_comap_blowUpMap :
    (Z.comap h).comap (Scheme.IdealSheafData.blowUpπ (Z.comap h)) = (Z.comap
        (Scheme.IdealSheafData.blowUpπ Z)).comap (blowUpMap h Z) := by
  have h1 := (Scheme.IdealSheafData.comap_comp Z (Scheme.IdealSheafData.blowUpπ (Z.comap h)) h).symm
  have h2 : Z.comap (Scheme.IdealSheafData.blowUpπ (Z.comap h) ≫ h) = Z.comap
      (blowUpMap h Z ≫ Scheme.IdealSheafData.blowUpπ Z) :=
    congrArg (fun m => Z.comap m) (blowUpMap_π h Z).symm
  exact h1.trans (h2.trans (Scheme.IdealSheafData.comap_comp Z (blowUpMap h Z)
      (Scheme.IdealSheafData.blowUpπ Z)))

/-- `F ≤ (blowUpMap h Z)_* F_Y`. -/
theorem le_map_exceptional_blowUpMap :
    Z.comap (Scheme.IdealSheafData.blowUpπ Z) ≤ ((Z.comap h).comap (Scheme.IdealSheafData.blowUpπ
        (Z.comap h))).map (blowUpMap h Z) :=
  Scheme.IdealSheafData.le_map_iff_comap_le.mpr (comap_π_comap_eq_comap_blowUpMap h Z).ge

/-- The centres form a cartesian square: `h⁻¹Z = Y ×_X Z`. -/
theorem isPullback_subschemeMap_comap :
    IsPullback (Scheme.IdealSheafData.subschemeMap (Z.comap h) Z h
        (Scheme.IdealSheafData.le_map_comap Z h)) (Z.comap h).subschemeι
      Z.subschemeι h :=
  (isPullback_of_isClosedImmersion _ _ _ _ (Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _
      _).symm
    (by rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι])).flip

/-- For flat `h : Y ⟶ X`, the map `F_Y → Z_Y` of the base-changed blow-up is the base change of
`F → Z` along `Z_Y = h⁻¹Z → Z` (blow-ups commute with flat base change, [Sta, Tag 0805]). -/
theorem isPullback_exceptionalMap_of_flat [Flat h] :
    IsPullback
      (Scheme.IdealSheafData.subschemeMap ((Z.comap h).comap (Scheme.IdealSheafData.blowUpπ
          (Z.comap h))) (Z.comap h) (Scheme.IdealSheafData.blowUpπ (Z.comap h))
        (Scheme.IdealSheafData.le_map_comap _ _))
      (Scheme.IdealSheafData.subschemeMap ((Z.comap h).comap (Scheme.IdealSheafData.blowUpπ
          (Z.comap h))) (Z.comap (Scheme.IdealSheafData.blowUpπ Z))
        (blowUpMap h Z) (le_map_exceptional_blowUpMap h Z))
      (Scheme.IdealSheafData.subschemeMap (Z.comap h) Z h (Scheme.IdealSheafData.le_map_comap Z h))
      (Scheme.IdealSheafData.subschemeMap (Z.comap (Scheme.IdealSheafData.blowUpπ Z)) Z
          (Scheme.IdealSheafData.blowUpπ Z) (Scheme.IdealSheafData.le_map_comap Z
          (Scheme.IdealSheafData.blowUpπ Z))) := by
  have s := isPullback_subschemeMap_of_isPullback (isPullback_blowUpMap h Z) (Z.comap
      (Scheme.IdealSheafData.blowUpπ Z))
    ((Z.comap h).comap (Scheme.IdealSheafData.blowUpπ (Z.comap h)))
        (comap_π_comap_eq_comap_blowUpMap h Z)
    (le_map_exceptional_blowUpMap h Z)
  rw [← Scheme.IdealSheafData.subschemeMap_subschemeι _ (Z.comap h) (Scheme.IdealSheafData.blowUpπ
      (Z.comap h)) (Scheme.IdealSheafData.le_map_comap _ _),
    ← Scheme.IdealSheafData.subschemeMap_subschemeι _ Z (Scheme.IdealSheafData.blowUpπ Z)
        (Scheme.IdealSheafData.le_map_comap Z (Scheme.IdealSheafData.blowUpπ Z))] at s
  refine (s.of_bot ?_ (isPullback_subschemeMap_comap h Z)).flip
  rw [← cancel_mono Z.subschemeι, Category.assoc, Scheme.IdealSheafData.subschemeMap_subschemeι,
      Category.assoc,
    Scheme.IdealSheafData.subschemeMap_subschemeι,
        Scheme.IdealSheafData.subschemeMap_subschemeι_assoc, blowUpMap_π,
    Scheme.IdealSheafData.subschemeMap_subschemeι_assoc]

end FlatBaseChange

section FieldExtension

/-- `Spec K → Spec k` for a field extension `K/k`. -/
noncomputable abbrev specMapField (k K : Type u) [Field k] [Field K] [Algebra k K] :
    Spec (.of K) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k K))

variable {k K : Type u} [Field k] [Field K] [Algebra k K] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (n r : ℕ) (Z : X.IdealSheafData)

/-- Every morphism to `Spec k` is flat, in particular the base change `X_K → X`. -/
theorem flat_pullback_fst_fieldExtension : Flat (Limits.pullback.fst f (specMapField k K)) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Flat)
    (IsPullback.of_hasPullback f (specMapField k K)).flip (flat_of_field _)

/-- `X_K → Spec K` is smooth of relative dimension `n` when `X → Spec k` is. -/
theorem smoothOfRelativeDimension_pullback_snd_fieldExtension [SmoothOfRelativeDimension n f] :
    SmoothOfRelativeDimension n (Limits.pullback.snd f (specMapField k K)) :=
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{u} (n := n)
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @SmoothOfRelativeDimension.{u} n)
    (IsPullback.of_hasPullback f (specMapField k K)) inferInstance

/-- `Z_K → Spec K` is the base change of `Z → Spec k` along `Spec K → Spec k`. -/
theorem isPullback_subschemeMap_comap_fst :
    IsPullback
      ((Z.comap (Limits.pullback.fst f (specMapField k K))).subschemeι ≫
        Limits.pullback.snd f (specMapField k K))
      (Scheme.IdealSheafData.subschemeMap (Z.comap (Limits.pullback.fst f (specMapField k K))) Z
        (Limits.pullback.fst f (specMapField k K)) (Scheme.IdealSheafData.le_map_comap _ _))
      (specMapField k K) (Z.subschemeι ≫ f) :=
  (isPullback_of_isClosedImmersion _ _ _ _ (Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _
      _).symm
    (by rw [Scheme.IdealSheafData.ker_subschemeι,
        Scheme.IdealSheafData.ker_subschemeι])).paste_horiz
      (IsPullback.of_hasPullback f (specMapField k K)).flip

/-- `Z_K → Spec K` is smooth of relative dimension `n − r` when `Z → Spec k` is. -/
theorem smoothOfRelativeDimension_subschemeι_comap_fst_comp
    [SmoothOfRelativeDimension (n - r) (Z.subschemeι ≫ f)] :
    SmoothOfRelativeDimension (n - r)
      ((Z.comap (Limits.pullback.fst f (specMapField k K))).subschemeι ≫
        Limits.pullback.snd f (specMapField k K)) :=
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{u} (n := n - r)
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @SmoothOfRelativeDimension.{u} (n - r)) (isPullback_subschemeMap_comap_fst f Z).flip
    inferInstance

/-- The property `surjective, flat and quasi-compact` of Mathlib's descent instances
(`Mathlib/AlgebraicGeometry/Morphisms/LocalFlatDescent.lean`): an fpqc covering by one morphism. -/
abbrev fpqcCover : MorphismProperty Scheme.{u} := @Surjective ⊓ @Flat ⊓ @QuasiCompact

/-- `Spec K → Spec k` is surjective: both spaces are points. -/
theorem surjective_specMapField : Surjective (specMapField k K) := by
  constructor
  intro y
  refine ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K), ?_⟩
  exact Subsingleton.elim (α := PrimeSpectrum k) _ _

/-- `Spec K → Spec k` is surjective, flat and quasi-compact: an fpqc covering. -/
theorem fpqcCover_specMapField : fpqcCover (specMapField k K) :=
  ⟨⟨surjective_specMapField (k := k) (K := K), flat_of_field _⟩, inferInstance⟩

/-- `Z_K → Z` is surjective, flat and quasi-compact, as the base change of `Spec K → Spec k`
(each of the three properties is stable under base change; the meet is assembled by hand rather
than through the base-change instance of the meet). -/
theorem fpqcCover_subschemeMap_comap_fst :
    fpqcCover
      (Scheme.IdealSheafData.subschemeMap (Z.comap (Limits.pullback.fst f (specMapField k K))) Z
        (Limits.pullback.fst f (specMapField k K)) (Scheme.IdealSheafData.le_map_comap _ _)) :=
  have sq := isPullback_subschemeMap_comap_fst f Z
  ⟨⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective) sq
      (surjective_specMapField (k := k) (K := K)),
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Flat) sq (flat_of_field _)⟩,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiCompact) sq inferInstance⟩

end FieldExtension

section Descent

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (n r : ℕ)
  [SmoothOfRelativeDimension n f] (Z : X.IdealSheafData)
  [SmoothOfRelativeDimension (n - r) (Z.subschemeι ≫ f)] (hrn : r ≤ n)

include f hrn in
/-- If smoothness of relative dimension `r − 1` descends along fpqc coverings, then for a smooth
blow-up over any field `k` the map `F → Z` from the exceptional divisor to the center is smooth of
relative dimension `r − 1` (the smoothness of `F` in [Kol07, Notation 19], relative to `Z`): base
change along `Spec K → Spec k` for `K` the algebraic closure of `k` (perfect, so the perfect-field
form applies to `F_K → Z_K`), the square `isPullback_exceptionalMap_of_flat`, and descent along
the surjective, flat, quasi-compact `Z_K → Z`. -/
theorem smoothOfRelativeDimension_subschemeMap_exceptional_of_descendsAlong
    (hdesc : MorphismProperty.DescendsAlong (@SmoothOfRelativeDimension.{u} (r - 1)) fpqcCover) :
    SmoothOfRelativeDimension (r - 1)
      (Scheme.IdealSheafData.subschemeMap (Z.comap (Scheme.IdealSheafData.blowUpπ Z)) Z
          (Scheme.IdealSheafData.blowUpπ Z) (Scheme.IdealSheafData.le_map_comap Z
          (Scheme.IdealSheafData.blowUpπ Z))) := by
  have hflat : Flat (Limits.pullback.fst f (specMapField k (AlgebraicClosure k))) :=
    flat_pullback_fst_fieldExtension f
  have h1 : SmoothOfRelativeDimension n (Limits.pullback.snd f (specMapField k
      (AlgebraicClosure k))) :=
    smoothOfRelativeDimension_pullback_snd_fieldExtension f n
  have h2 : SmoothOfRelativeDimension (n - r)
      ((Z.comap (Limits.pullback.fst f (specMapField k (AlgebraicClosure k)))).subschemeι ≫
        Limits.pullback.snd f (specMapField k (AlgebraicClosure k))) :=
    smoothOfRelativeDimension_subschemeι_comap_fst_comp f n r Z
  have hK := smoothOfRelativeDimension_subschemeMap_exceptional
    (Limits.pullback.snd f (specMapField k (AlgebraicClosure k))) n r
    (Z.comap (Limits.pullback.fst f (specMapField k (AlgebraicClosure k)))) hrn
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @SmoothOfRelativeDimension.{u} (r - 1)) (Q := fpqcCover)
    (isPullback_exceptionalMap_of_flat (Limits.pullback.fst f (specMapField k
        (AlgebraicClosure k))) Z)
    (fpqcCover_subschemeMap_comap_fst f Z) hK

end Descent

end AlgebraicGeometry
