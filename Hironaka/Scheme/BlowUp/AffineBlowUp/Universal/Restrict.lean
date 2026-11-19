/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.AffineBlowUp.Universal.Existence
import Hironaka.Scheme.BlowUp.AffineBlowUp.Exceptional
import Hironaka.Scheme.BlowUp.AffineBlowUp.Universal.Uniqueness
import Hironaka.Scheme.BlowUp.InverseImage
import Hironaka.Scheme.BlowUp.InvertibleSheaf

/-!
# Open restriction of the affine blow-up is a pullback

The blow-up of an open subscheme `U` of `X` along `U ∩ Z` is the restriction of the blow-up of
`X` along `Z` to `π⁻¹(U)` [Hau14, Corollary 5.2 (b)], a special case of the behaviour of blow-ups
under base change [Hau14, Proposition 5.1], proved here through the universal property: for an
affine open `U = Spec S ⊆ Spec R` and `J = I S`, the square of
`affineBlowUp.mapHom φ : affineBlowUp J ⟶ affineBlowUp I` over `Spec.map φ : Spec S ⟶ Spec R` is
a pullback, and `affineBlowUp J ≅ π⁻¹(U)` over `U`.

The argument.  Let `P = π⁻¹(U) ⊆ B = affineBlowUp I`.  The map `P → U ≅ Spec S` is admissible
for `J` — `J·𝒪_P` is the exceptional ideal of `B` restricted to the open `P`, invertible by
`affineBlowUp.isInvertible_exceptionalIdeal` — so the universal property gives
`ψ : P ⟶ B' = affineBlowUp J` over `Spec S`.  The morphism `mapHom φ : B' ⟶ B` lies over
`Spec.map φ`, hence lands in `P`, as `m' : B' ⟶ P` (`IsOpenImmersion.lift`).  Both `ψ ≫ m' ≫ P.ι`
and `P.ι` are lifts of `P → Spec R` (admissible for `I`), so they agree by uniqueness and
`ψ ≫ m' = 𝟙` (`P.ι` is a monomorphism); both `m' ≫ ψ` and `𝟙` are lifts of `π' : B' → Spec S`
(admissible for `J`), so `m' ≫ ψ = 𝟙`.  Thus `m'` is an isomorphism `B' ≅ P` with
`m' ≫ P.ι = mapHom φ`, and the pullback square `isPullback_morphismRestrict` of `P` transports
along it.  Openness of `U` is used three times (to restrict the exceptional ideal, to factor
`mapHom φ` through `P`, and to transport the restriction square); for an arbitrary base change
the blow-up of the base change is only the strict transform inside the fibre product
[Hau14, Proposition 5.1]. A chartwise proof is also possible [Sta, Tag 0805].
-/

@[expose] public section

namespace AlgebraicGeometry

open AlgebraicGeometry CategoryTheory Scheme.IdealSheafData TopologicalSpace

universe u

variable {R S : CommRingCat.{u}} (φ : R ⟶ S) [IsOpenImmersion (Spec.map φ)]
  {I : Ideal R} {J : Ideal S} (hJ : I.map φ.hom = J)

omit [IsOpenImmersion (Spec.map φ)] in
include hJ in
/-- The ideal sheaf of `J = I S` on `Spec S` is the inverse image of the ideal sheaf of `I` along
`Spec.map φ`. -/
theorem specIdealSheaf_eq_comap_specMap :
    specIdealSheaf J = (specIdealSheaf I).comap (Spec.map φ) := by
  subst hJ
  exact (Scheme.IdealSheafData.comap_ofIdealTop_Spec_map φ I).symm

/-- The isomorphism `Spec S ≅ U` onto the image `U` of the open immersion `Spec.map φ`. -/
noncomputable def specMapIsoOpensRange : Spec S ≅ ((Spec.map φ).opensRange : Scheme.{u}) :=
  IsOpenImmersion.isoOfRangeEq (Spec.map φ) (Spec.map φ).opensRange.ι
    (by rw [Scheme.Opens.range_ι]; rfl)

@[reassoc (attr := simp)]
theorem specMapIsoOpensRange_hom_ι :
    (specMapIsoOpensRange φ).hom ≫ (Spec.map φ).opensRange.ι = Spec.map φ :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[reassoc (attr := simp)]
theorem specMapIsoOpensRange_inv_specMap :
    (specMapIsoOpensRange φ).inv ≫ Spec.map φ = (Spec.map φ).opensRange.ι :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

variable (I) in
/-- The open `P = π⁻¹(U) ⊆ affineBlowUp I`, for `U` the image of `Spec.map φ`. -/
noncomputable abbrev preimageOpens : (affineBlowUp I).Opens :=
  affineBlowUp.π I ⁻¹ᵁ (Spec.map φ).opensRange

include hJ in
/-- `mapHom φ` lands in `π⁻¹(U)` (it lies over `Spec.map φ`, whose image is `U`). -/
theorem range_mapHom_subset :
    Set.range (affineBlowUp.mapHom φ hJ) ⊆ Set.range (preimageOpens φ I).ι := by
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι]
  change affineBlowUp.π I (affineBlowUp.mapHom φ hJ x) ∈ (Spec.map φ).opensRange
  rw [← Scheme.Hom.comp_apply, affineBlowUp.mapHom_π, Scheme.Hom.comp_apply]
  exact ⟨_, rfl⟩

/-- `mapHom φ` as a morphism to `π⁻¹(U)`. -/
noncomputable def mapHomToPreimage : affineBlowUp J ⟶ (preimageOpens φ I : Scheme.{u}) :=
  IsOpenImmersion.lift _ (affineBlowUp.mapHom φ hJ) (range_mapHom_subset φ hJ)

@[reassoc (attr := simp)]
theorem mapHomToPreimage_ι :
    mapHomToPreimage φ hJ ≫ (preimageOpens φ I).ι = affineBlowUp.mapHom φ hJ :=
  IsOpenImmersion.lift_fac _ _ _

variable (I) in
/-- The structure map `π⁻¹(U) → U ≅ Spec S`. -/
noncomputable def preimageToSpec : (preimageOpens φ I : Scheme.{u}) ⟶ Spec S :=
  (affineBlowUp.π I ∣_ (Spec.map φ).opensRange) ≫ (specMapIsoOpensRange φ).inv

variable (I) in
theorem preimageToSpec_specMap :
    preimageToSpec φ I ≫ Spec.map φ = (preimageOpens φ I).ι ≫ affineBlowUp.π I := by
  unfold preimageToSpec
  rw [Category.assoc, specMapIsoOpensRange_inv_specMap, morphismRestrict_ι]

variable (I) in
/-- `π⁻¹(U) → Spec R` is admissible for `I`: the exceptional ideal restricted to an open is
invertible. -/
theorem isInvertible_comap_ι_π :
    ((specIdealSheaf I).comap ((preimageOpens φ I).ι ≫ affineBlowUp.π I)).IsInvertible := by
  rw [Scheme.IdealSheafData.comap_comp]
  exact (affineBlowUp.isInvertible_exceptionalIdeal I).comap_of_isOpenImmersion _

include hJ in
/-- `π⁻¹(U) → Spec S` is admissible for `J`. -/
theorem isInvertible_comap_preimageToSpec :
    ((specIdealSheaf J).comap (preimageToSpec φ I)).IsInvertible := by
  rw [specIdealSheaf_eq_comap_specMap φ hJ, ← Scheme.IdealSheafData.comap_comp,
      preimageToSpec_specMap]
  exact isInvertible_comap_ι_π φ I

/-- The lift `π⁻¹(U) ⟶ affineBlowUp J` over `Spec S`. -/
noncomputable def preimageToBlowUp : (preimageOpens φ I : Scheme.{u}) ⟶ affineBlowUp J :=
  affineBlowUp.lift J (preimageToSpec φ I) (isInvertible_comap_preimageToSpec φ hJ)

@[reassoc (attr := simp)]
theorem preimageToBlowUp_π :
    preimageToBlowUp φ hJ ≫ affineBlowUp.π J = preimageToSpec φ I :=
  affineBlowUp.lift_π _ _ _

theorem preimageToBlowUp_mapHom :
    preimageToBlowUp φ hJ ≫ affineBlowUp.mapHom φ hJ = (preimageOpens φ I).ι := by
  refine affineBlowUp.hom_ext I _ (isInvertible_comap_ι_π φ I) _ _ ?_ rfl
  rw [Category.assoc, affineBlowUp.mapHom_π, preimageToBlowUp_π_assoc, preimageToSpec_specMap]

theorem preimageToBlowUp_mapHomToPreimage :
    preimageToBlowUp φ hJ ≫ mapHomToPreimage φ hJ = 𝟙 _ := by
  rw [← cancel_mono (preimageOpens φ I).ι, Category.assoc, mapHomToPreimage_ι,
    preimageToBlowUp_mapHom, Category.id_comp]

theorem mapHomToPreimage_preimageToSpec :
    mapHomToPreimage φ hJ ≫ preimageToSpec φ I = affineBlowUp.π J := by
  rw [← cancel_mono (Spec.map φ), Category.assoc, preimageToSpec_specMap, ← Category.assoc,
    mapHomToPreimage_ι, affineBlowUp.mapHom_π]

theorem mapHomToPreimage_preimageToBlowUp :
    mapHomToPreimage φ hJ ≫ preimageToBlowUp φ hJ = 𝟙 _ := by
  refine affineBlowUp.hom_ext J (affineBlowUp.π J) (affineBlowUp.isInvertible_exceptionalIdeal J)
    _ _ ?_ (Category.id_comp _)
  rw [Category.assoc, preimageToBlowUp_π, mapHomToPreimage_preimageToSpec]

/-- `affineBlowUp (I S) ≅ π⁻¹(U)` over `U`, the isomorphism composed with the inclusion being
`mapHom φ`. -/
noncomputable def blowUpIsoPreimage : affineBlowUp J ≅ (preimageOpens φ I : Scheme.{u}) where
  hom := mapHomToPreimage φ hJ
  inv := preimageToBlowUp φ hJ
  hom_inv_id := mapHomToPreimage_preimageToBlowUp φ hJ
  inv_hom_id := preimageToBlowUp_mapHomToPreimage φ hJ

theorem blowUpIsoPreimage_hom_ι :
    (blowUpIsoPreimage φ hJ).hom ≫ (preimageOpens φ I).ι = affineBlowUp.mapHom φ hJ :=
  mapHomToPreimage_ι φ hJ

/-- **Open restriction is a pullback** [Hau14, Proposition 5.1 and Corollary 5.2 (b)]: for
`Spec S ⊆ Spec R` an affine open and `J = I S`, the square of `affineBlowUp.mapHom φ` over
`Spec.map φ` is a pullback (`isPullback_morphismRestrict` transported along
`blowUpIsoPreimage`). -/
theorem affineBlowUp.isPullback_mapHom :
    IsPullback (affineBlowUp.mapHom φ hJ) (affineBlowUp.π J) (affineBlowUp.π I) (Spec.map φ) := by
  refine (isPullback_morphismRestrict (affineBlowUp.π I) (Spec.map φ).opensRange).flip.of_iso
    (blowUpIsoPreimage φ hJ).symm (Iso.refl _) (specMapIsoOpensRange φ).symm (Iso.refl _)
    ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
    exact (preimageToBlowUp_mapHom φ hJ).symm
  · rw [Iso.symm_hom, Iso.symm_hom]
    exact (preimageToBlowUp_π φ hJ).symm
  · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, specMapIsoOpensRange_inv_specMap]

/-- Existentially: `affineBlowUp (I S)` is `π⁻¹(U)`, compatibly with `mapHom φ`. -/
theorem affineBlowUp.exists_iso_preimage :
    ∃ e : affineBlowUp J ≅ (affineBlowUp.π I ⁻¹ᵁ (Spec.map φ).opensRange : Scheme.{u}),
      e.hom ≫ (affineBlowUp.π I ⁻¹ᵁ (Spec.map φ).opensRange).ι = affineBlowUp.mapHom φ hJ :=
  ⟨blowUpIsoPreimage φ hJ, blowUpIsoPreimage_hom_ι φ hJ⟩

end AlgebraicGeometry
