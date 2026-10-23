import DeJongAlterations.Algebra.ReesCoefficientLocalization
import DeJongAlterations.Geometry.AffineBlowupFunctor
import DeJongAlterations.Geometry.ProjCoefficientLocalization
import DeJongAlterations.Geometry.AffineBlowupIsomorphism

/-!
# Actual affine blowup compatibility with principal coefficient localization

Coefficientwise mapping of the native Rees algebras preserves the actual affine
structure morphisms. Principal coefficient localization identifies the blowup of the
extended ideal with the genuine inverse image of the target principal open.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open DeJongAlterations.Algebra.ReesLocalization

noncomputable section

namespace DeJongAlterations.Geometry.AffineBlowupBaseChange

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The actual degree-zero Rees coefficient map is the original ring map. -/
theorem reesGradedMap_degreeZero_constants (I : Ideal R) (f : R →+* S) :
    (reesGradedMap I f).gradedZeroRingHom.comp (reesDegreeZeroEquiv I).toRingHom =
      (reesDegreeZeroEquiv (I.map f)).toRingHom.comp f := by
  apply RingHom.ext
  intro r
  apply Subtype.ext
  change reesMap I f (algebraMap R (reesAlgebra I) r) =
    algebraMap S (reesAlgebra (I.map f)) (f r)
  exact reesMap_algebraMap I f r

/-- The native Proj morphism of an actual Rees coefficient map preserves the original bases. -/
theorem reesGradedMap_projStructure (I : Ideal R) (f : R →+* S)
    (hf : HomogeneousIdeal.irrelevant (reesGrading (I.map f)) ≤
      (HomogeneousIdeal.irrelevant (reesGrading I)).map (reesGradedMap I f)) :
    Proj.map (reesGradedMap I f) hf ≫ affineBlowupStructure I =
      affineBlowupStructure (I.map f) ≫ Spec.map (CommRingCat.ofHom f) := by
  have H := ProjStructureMap.map_toSpec_base (reesGradedMap I f) hf
    (reesDegreeZeroEquiv I).toRingHom ((reesDegreeZeroEquiv (I.map f)).toRingHom.comp f)
    (reesGradedMap_degreeZero_constants I f)
  change Proj.map (reesGradedMap I f) hf ≫
      (Proj.toSpecZero (reesGrading I) ≫
        Spec.map (CommRingCat.ofHom (reesDegreeZeroEquiv I).toRingHom)) =
    Proj.toSpecZero (reesGrading (I.map f)) ≫
      Spec.map (CommRingCat.ofHom (reesDegreeZeroEquiv (I.map f)).toRingHom) ≫
        Spec.map (CommRingCat.ofHom f)
  simpa only [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp] using H

private instance reesConstants_isLocalization (I : Ideal R) (s : R) :
    IsLocalization.Away ((reesConstants I s : reesGrading I 0) : reesAlgebra I)
      (reesAlgebra (I.map (algebraMap R (Localization.Away s)))) := by
  change IsLocalization.Away (algebraMap R (reesAlgebra I) s)
    (reesAlgebra (I.map (algebraMap R (Localization.Away s))))
  infer_instance

/-- The literal native Proj map of the actual localized Rees coefficient homomorphism. -/
def affineBlowupLocalizationMap (I : Ideal R) (s : R) :
    affineBlowup (I.map (algebraMap R (Localization.Away s))) ⟶ affineBlowup I :=
  Proj.map (reesGradedMap I (algebraMap R (Localization.Away s)))
    (ProjCoefficientLocalization.irrelevant_le_map
      (reesGradedMap I (algebraMap R (Localization.Away s))) (reesConstants I s) rfl)

/-- The actual coefficient localization comparison lies over the original localization map. -/
@[reassoc]
theorem affineBlowupLocalizationMap_structure (I : Ideal R) (s : R) :
    affineBlowupLocalizationMap I s ≫ affineBlowupStructure I =
      affineBlowupStructure (I.map (algebraMap R (Localization.Away s))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away s))) :=
  reesGradedMap_projStructure I _ _

/-- Principal coefficient localization induces an actual open immersion of native blowups. -/
instance affineBlowupLocalizationMap_isOpenImmersion (I : Ideal R) (s : R) :
    IsOpenImmersion (affineBlowupLocalizationMap I s) :=
  ProjCoefficientLocalization.isOpenImmersion_map
    (reesGradedMap I (algebraMap R (Localization.Away s))) (reesConstants I s) rfl _

/-- Its image is exactly the inverse image of the target principal open. -/
theorem affineBlowupLocalizationMap_opensRange (I : Ideal R) (s : R) :
    (affineBlowupLocalizationMap I s).opensRange =
      affineBlowupStructure I ⁻¹ᵁ PrimeSpectrum.basicOpen s := by
  rw [affineBlowupStructure_preimage_basicOpen]
  apply SetLike.coe_injective
  exact ProjCoefficientLocalization.map_range
    (reesGradedMap I (algebraMap R (Localization.Away s))) (reesConstants I s) rfl _

/-- The blowup after actual principal coefficient localization is the actual target restriction. -/
def affineBlowupLocalizationIso (I : Ideal R) (s : R) :
    affineBlowup (I.map (algebraMap R (Localization.Away s))) ≅
      (affineBlowupStructure I ⁻¹ᵁ PrimeSpectrum.basicOpen s).toScheme :=
  IsOpenImmersion.isoOfRangeEq (affineBlowupLocalizationMap I s)
    (affineBlowupStructure I ⁻¹ᵁ PrimeSpectrum.basicOpen s).ι (by
      rw [Scheme.Opens.range_ι]
      exact congrArg SetLike.coe (affineBlowupLocalizationMap_opensRange I s))

/-- This isomorphism factors the literal native comparison map. -/
@[reassoc (attr := simp)]
theorem affineBlowupLocalizationIso_hom_ι (I : Ideal R) (s : R) :
    (affineBlowupLocalizationIso I s).hom ≫
      (affineBlowupStructure I ⁻¹ᵁ PrimeSpectrum.basicOpen s).ι =
        affineBlowupLocalizationMap I s := by
  simp [affineBlowupLocalizationIso]

/-- The actual restriction isomorphism preserves the structure map to the localized base. -/
@[reassoc]
theorem affineBlowupLocalizationIso_hom_structure (I : Ideal R) (s : R) :
    (affineBlowupLocalizationIso I s).hom ≫
      (affineBlowupStructure I ∣_ PrimeSpectrum.basicOpen s) ≫
        (basicOpenIsoSpecAway (R := CommRingCat.of R) s).hom =
      affineBlowupStructure (I.map (algebraMap R (Localization.Away s))) := by
  let e := basicOpenIsoSpecAway (R := CommRingCat.of R) s
  have he : e.inv ≫ Scheme.Opens.ι (X := Spec (CommRingCat.of R))
      (PrimeSpectrum.basicOpen s) =
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away s))) := by
    rw [Iso.inv_comp_eq]
    exact (basicOpenIsoSpecAway_hom_SpecMap (R := CommRingCat.of R) s).symm
  change (affineBlowupLocalizationIso I s).hom ≫
    (affineBlowupStructure I ∣_ PrimeSpectrum.basicOpen s) ≫ e.hom = _
  apply (cancel_mono (e.inv ≫ Scheme.Opens.ι (X := Spec (CommRingCat.of R))
    (PrimeSpectrum.basicOpen s))).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [morphismRestrict_ι (affineBlowupStructure I) (PrimeSpectrum.basicOpen s),
    ← Category.assoc, affineBlowupLocalizationIso_hom_ι,
    he, affineBlowupLocalizationMap_structure]

/-- Principal coefficient localization gives the genuine Cartesian native blowup square. -/
theorem isPullback_affineBlowupLocalization (I : Ideal R) (s : R) :
    IsPullback (affineBlowupLocalizationMap I s)
      (affineBlowupStructure (I.map (algebraMap R (Localization.Away s))))
      (affineBlowupStructure I)
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away s)))) := by
  let e := affineBlowupLocalizationIso I s
  let eb := basicOpenIsoSpecAway (R := CommRingCat.of R) s
  refine (isPullback_morphismRestrict (affineBlowupStructure I)
    (PrimeSpectrum.basicOpen s)).flip.of_iso
    e.symm (Iso.refl _) eb (Iso.refl _) ?_ ?_ ?_ ?_
  · simpa only [Iso.refl_hom, Iso.symm_hom, Category.comp_id] using
      (show (affineBlowupStructure I ⁻¹ᵁ PrimeSpectrum.basicOpen s).ι =
        e.inv ≫ affineBlowupLocalizationMap I s from by
          rw [← affineBlowupLocalizationIso_hom_ι, ← Category.assoc, Iso.inv_hom_id,
            Category.id_comp])
  · change (affineBlowupStructure I ∣_ PrimeSpectrum.basicOpen s) ≫ eb.hom =
      e.inv ≫ affineBlowupStructure (I.map (algebraMap R (Localization.Away s)))
    rw [← affineBlowupLocalizationIso_hom_structure, ← Category.assoc,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  · simp
  · simpa only [Iso.refl_hom, Category.comp_id] using
      (basicOpenIsoSpecAway_hom_SpecMap (R := CommRingCat.of R) s).symm

section GeneralLocalization

variable [Algebra R S]

private instance reesConstants_general_isLocalization (I : Ideal R) (s : R)
    [IsLocalization.Away s S] :
    IsLocalization.Away ((reesConstants I s : reesGrading I 0) : reesAlgebra I)
      (reesAlgebra (I.map (algebraMap R S))) := by
  change IsLocalization.Away (algebraMap R (reesAlgebra I) s)
    (reesAlgebra (I.map (algebraMap R S)))
  infer_instance

/-- Any presentation of a principal coefficient localization induces the actual open immersion. -/
theorem affineBlowupMap_isOpenImmersion_of_isLocalization (I : Ideal R) (s : R)
    [IsLocalization.Away s S] :
    IsOpenImmersion (affineBlowupMap I (algebraMap R S)) :=
  ProjCoefficientLocalization.isOpenImmersion_map
    (reesGradedMap I (algebraMap R S)) (reesConstants I s) rfl _

/-- The actual image is independent of the chosen presentation of the coefficient localization. -/
theorem affineBlowupMap_opensRange_of_isLocalization (I : Ideal R) (s : R)
    [IsLocalization.Away s S] :
    let := affineBlowupMap_isOpenImmersion_of_isLocalization (S := S) I s
    (affineBlowupMap I (algebraMap R S)).opensRange =
      affineBlowupStructure I ⁻¹ᵁ PrimeSpectrum.basicOpen s := by
  let := affineBlowupMap_isOpenImmersion_of_isLocalization (S := S) I s
  rw [affineBlowupStructure_preimage_basicOpen]
  apply SetLike.coe_injective
  exact ProjCoefficientLocalization.map_range
    (reesGradedMap I (algebraMap R S)) (reesConstants I s) rfl _

/-- The actual coefficient-induced blowup square is Cartesian for any principal localization. -/
theorem isPullback_affineBlowupMap_of_isLocalization (I : Ideal R) (s : R)
    [IsLocalization.Away s S] :
    IsPullback (affineBlowupMap I (algebraMap R S))
      (affineBlowupStructure (I.map (algebraMap R S)))
      (affineBlowupStructure I) (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  let q := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let : IsOpenImmersion q := IsOpenImmersion.of_isLocalization s
  let := affineBlowupMap_isOpenImmersion_of_isLocalization (S := S) I s
  have hq : q.opensRange = PrimeSpectrum.basicOpen s := by
    apply SetLike.coe_injective
    exact PrimeSpectrum.localization_away_comap_range S s
  apply IsPullback.flip
  apply IsOpenImmersion.isPullback
  · exact affineBlowupMap_structure I (algebraMap R S)
  · rw [hq]
    exact (affineBlowupMap_opensRange_of_isLocalization (S := S) I s).symm

/-- The same actual square with a named extended center, as needed for affine-site gluing. -/
theorem isPullback_affineBlowupMapTo_of_isLocalization (I : Ideal R) (J : Ideal S) (s : R)
    [IsLocalization.Away s S] (hIJ : I.map (algebraMap R S) = J) :
    IsPullback (affineBlowupMapTo I J (algebraMap R S) hIJ)
      (affineBlowupStructure J) (affineBlowupStructure I)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  subst J
  exact isPullback_affineBlowupMap_of_isLocalization (S := S) I s

end GeneralLocalization

end DeJongAlterations.Geometry.AffineBlowupBaseChange
