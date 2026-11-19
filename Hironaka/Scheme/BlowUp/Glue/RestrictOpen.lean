/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.BlowUpMap.Defs
import Hironaka.Scheme.BlowUp.BlowUpMap
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The blow-up commutes with restriction to opens

For a morphism `h : Y ⟶ X`, the universal property lifts `π_Y ≫ h` to the morphism of blow-ups
`blowUpMap h D : blowUp (D.comap h) ⟶ blowUp D` over `h`. For an open immersion it is the
restriction to `π⁻¹(U)`:

Blowing up commutes with restriction to open subschemes [Sta, Tag 02OS];
[Hau14, Corollary 5.2 (b)]: for an open `U ⊆ X`, the blow-up of the open subscheme `U` along
`I|_U = I.comap U.ι` is `π⁻¹(U)`, as a pullback square `blowUp (I.comap U.ι) ⟶ blowUp I` over
`U ⟶ X`.

The argument is Hauser's universal-property proof of the behaviour of blow-ups under base change
[Hau14, Proposition 5.1], as in `Hironaka.Scheme.BlowUp.AffineBlowUp.Universal.Restrict` but with
the global universal property (`blowUp.lift`, `blowUp.hom_ext`): `π⁻¹(U) → U` is admissible for
`I|_U` (the exceptional ideal of `X` restricted to an open), so it lifts to
`blowUp (I.comap U.ι)`; `blowUp (I.comap U.ι) → U → X` is admissible for `I` (its inverse image
of `I` is the exceptional ideal of the blow-up of `U`), so it lifts to `blowUp I`, landing in
`π⁻¹(U)`; the two composites are identities by uniqueness over `X` and over `U`, and the
resulting isomorphism carries Mathlib's restriction square `isPullback_morphismRestrict` to the
square of the lift.
-/

@[expose] public section

namespace AlgebraicGeometry

open Scheme.IdealSheafData Scheme.Hom

open AlgebraicGeometry CategoryTheory Scheme.IdealSheafData TopologicalSpace

universe u

variable {X : Scheme.{u}}

variable (I : X.IdealSheafData) (U : X.Opens)

/-- `blowUpMap U.ι I` lands in `π⁻¹(U)`. -/
theorem range_restrictHom_subset :
    Set.range (blowUpMap U.ι I) ⊆ Set.range (blowUpπ I ⁻¹ᵁ U).ι := by
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι]
  change blowUpπ I (blowUpMap U.ι I x) ∈ U
  rw [← Scheme.Hom.comp_apply, blowUpMap_π, Scheme.Hom.comp_apply]
  have hw : U.ι (blowUpπ (I.comap U.ι) x) ∈ (U : Set X) := by
    rw [← Scheme.Opens.range_ι]
    exact ⟨_, rfl⟩
  exact hw

/-- `blowUpMap U.ι I` as a morphism to `π⁻¹(U)`. -/
noncomputable def restrictHomToPreimage :
    blowUp (I.comap U.ι) ⟶ (blowUpπ I ⁻¹ᵁ U : Scheme.{u}) :=
  IsOpenImmersion.lift _ (blowUpMap U.ι I) (range_restrictHom_subset I U)

@[reassoc (attr := simp)]
theorem restrictHomToPreimage_ι :
    restrictHomToPreimage I U ≫ (blowUpπ I ⁻¹ᵁ U).ι = blowUpMap U.ι I :=
  IsOpenImmersion.lift_fac _ _ _

/-- `π⁻¹(U) → U` is admissible for `I|_U`: the exceptional ideal restricted to an open. -/
theorem isInvertible_comap_morphismRestrict :
    ((I.comap U.ι).comap (blowUpπ I ∣_ U)).IsInvertible := by
  rw [← comap_comp, morphismRestrict_ι, comap_comp]
  exact (blowUp.isInvertible_comap_π I).comap_of_isOpenImmersion _

/-- The lift `π⁻¹(U) ⟶ blowUp (I|_U)` over `U`. -/
noncomputable def preimageToRestrict : (blowUpπ I ⁻¹ᵁ U : Scheme.{u}) ⟶ blowUp (I.comap U.ι) :=
  blowUp.lift (I.comap U.ι) (blowUpπ I ∣_ U) (isInvertible_comap_morphismRestrict I U)

@[reassoc (attr := simp)]
theorem preimageToRestrict_π :
    preimageToRestrict I U ≫ blowUpπ (I.comap U.ι) = blowUpπ I ∣_ U :=
  blowUp.lift_π _ _ _

theorem preimageToRestrict_restrictHom :
    preimageToRestrict I U ≫ blowUpMap U.ι I = (blowUpπ I ⁻¹ᵁ U).ι := by
  refine blowUp.hom_ext I ((blowUpπ I ⁻¹ᵁ U).ι ≫ blowUpπ I) ?_ _ _ ?_ rfl
  · rw [comap_comp]
    exact (blowUp.isInvertible_comap_π I).comap_of_isOpenImmersion _
  · rw [Category.assoc, blowUpMap_π, preimageToRestrict_π_assoc, morphismRestrict_ι]

theorem preimageToRestrict_restrictHomToPreimage :
    preimageToRestrict I U ≫ restrictHomToPreimage I U = 𝟙 _ := by
  rw [← cancel_mono (blowUpπ I ⁻¹ᵁ U).ι, Category.assoc, restrictHomToPreimage_ι,
    preimageToRestrict_restrictHom, Category.id_comp]

theorem restrictHomToPreimage_morphismRestrict :
    restrictHomToPreimage I U ≫ (blowUpπ I ∣_ U) = blowUpπ (I.comap U.ι) := by
  rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, restrictHomToPreimage_ι_assoc,
    blowUpMap_π]

theorem restrictHomToPreimage_preimageToRestrict :
    restrictHomToPreimage I U ≫ preimageToRestrict I U = 𝟙 _ := by
  refine blowUp.hom_ext (I.comap U.ι) (blowUpπ (I.comap U.ι))
    (blowUp.isInvertible_comap_π _) _ _ ?_ (Category.id_comp _)
  rw [Category.assoc, preimageToRestrict_π, restrictHomToPreimage_morphismRestrict]

/-- `blowUp (I|_U) ≅ π⁻¹(U)`. -/
noncomputable def Scheme.IdealSheafData.blowUp.restrictIso : blowUp (I.comap U.ι) ≅
    (blowUpπ I ⁻¹ᵁ U : Scheme.{u}) where
  hom := restrictHomToPreimage I U
  inv := preimageToRestrict I U
  hom_inv_id := restrictHomToPreimage_preimageToRestrict I U
  inv_hom_id := preimageToRestrict_restrictHomToPreimage I U

/-- **The blow-up commutes with restriction to opens** [Sta, Tag 02OS]; [Hau14, Corollary 5.2 (b)]:
the square of `blowUpMap U.ι I : blowUp (I|_U) ⟶ blowUp I` over `U ⟶ X` is a pullback. -/
theorem Scheme.IdealSheafData.blowUp.isPullback_restrictHom :
    IsPullback (blowUpMap U.ι I) (blowUpπ (I.comap U.ι)) (blowUpπ I) U.ι := by
  refine (isPullback_morphismRestrict (blowUpπ I) U).flip.of_iso (blowUp.restrictIso I U).symm
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
    exact (preimageToRestrict_restrictHom I U).symm
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
    exact (preimageToRestrict_π I U).symm
  · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
  · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]

/-- Existentially: some morphism `blowUp (I|_U) ⟶ blowUp I` makes a pullback square over `U ⟶ X`. -/
theorem Scheme.IdealSheafData.blowUp.exists_isPullback_restrict :
    ∃ φ : blowUp (I.comap U.ι) ⟶ blowUp I,
      IsPullback φ (blowUpπ (I.comap U.ι)) (blowUpπ I) U.ι :=
  ⟨_, blowUp.isPullback_restrictHom I U⟩

end AlgebraicGeometry
