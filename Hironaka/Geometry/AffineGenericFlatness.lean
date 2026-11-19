import Hironaka.Algebra.GenericFlatness
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Generic flatness of actual affine restrictions

The principal-open restriction is compared with the genuine tensor base change over the
localized coefficient ring, retaining the original affine morphism.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

noncomputable section

namespace Hironaka.Geometry.AffineGenericFlatness

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (D A : Type u) [CommRing D] [CommRing A] [Algebra D A]

/-- The actual affine scheme morphism induced by the specified algebra structure. -/
abbrev affineStructure : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of D) :=
  Spec.map (CommRingCat.ofHom (R := D) (S := A) (algebraMap D A))

/-- The projection of the actual localized tensor scheme to the original affine source. -/
def tensorOriginalProjection (b : D) :
    Spec (CommRingCat.of (Localization.Away b ⊗[D] A)) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (R := A) (S := Localization.Away b ⊗[D] A)
    (Algebra.TensorProduct.includeRight (R := D) (A := Localization.Away b)).toRingHom)

/-- The tensor scheme is the actual affine localization pullback. -/
theorem isPullback_tensorAffine (b : D) :
    IsPullback (affineStructure (Localization.Away b) (Localization.Away b ⊗[D] A))
      (tensorOriginalProjection D A b)
      (affineStructure D (Localization.Away b)) (affineStructure D A) := by
  refine (IsPullback.of_hasPullback (affineStructure D (Localization.Away b))
    (affineStructure D A)).of_iso (pullbackSpecIso D (Localization.Away b) A)
      (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simpa only [affineStructure, Category.comp_id, Iso.refl_hom] using
      (pullbackSpecIso_hom_fst' D (Localization.Away b) A).symm
  · simpa only [tensorOriginalProjection, affineStructure, Category.comp_id, Iso.refl_hom,
      AlgHom.toRingHom_eq_coe] using
      (pullbackSpecIso_hom_snd D (Localization.Away b) A).symm
  · simp
  · simp

/-- The original principal-open restriction is a pullback over the localized coefficient ring. -/
theorem isPullback_restrictedAffine (b : D) :
    IsPullback
      ((affineStructure D A ∣_ PrimeSpectrum.basicOpen b) ≫
        (basicOpenIsoSpecAway (R := CommRingCat.of D) b).hom)
      ((affineStructure D A ⁻¹ᵁ PrimeSpectrum.basicOpen b).ι)
      (affineStructure D (Localization.Away b)) (affineStructure D A) := by
  refine (isPullback_morphismRestrict (affineStructure D A)
    (PrimeSpectrum.basicOpen b)).of_iso (Iso.refl _)
      (basicOpenIsoSpecAway (R := CommRingCat.of D) b) (Iso.refl _) (Iso.refl _)
      ?_ ?_ ?_ ?_
  · simp
  · simp
  · simpa only [affineStructure, Category.comp_id, Iso.refl_hom] using
      (basicOpenIsoSpecAway_hom_SpecMap (R := CommRingCat.of D) b).symm
  · simp

/-- The actual source of the principal-open restriction is its genuine tensor base change. -/
def affineRestrictionTensorIso (b : D) :
    (affineStructure D A ⁻¹ᵁ PrimeSpectrum.basicOpen b).toScheme ≅
      Spec (CommRingCat.of (Localization.Away b ⊗[D] A)) :=
  (isPullback_restrictedAffine D A b).isoIsPullback _ _ (isPullback_tensorAffine D A b)

/-- The source comparison commutes with the actual morphism to the localized target. -/
theorem affineRestrictionTensorIso_hom_structure (b : D) :
    (affineRestrictionTensorIso D A b).hom ≫
        affineStructure (Localization.Away b) (Localization.Away b ⊗[D] A) =
      (affineStructure D A ∣_ PrimeSpectrum.basicOpen b) ≫
        (basicOpenIsoSpecAway (R := CommRingCat.of D) b).hom :=
  (isPullback_restrictedAffine D A b).isoIsPullback_hom_fst _ _
    (isPullback_tensorAffine D A b)

/-- The principal-open restriction and localized tensor morphism are isomorphic arrows. -/
def affineRestrictionTensorArrowIso (b : D) :
    Arrow.mk (affineStructure D A ∣_ PrimeSpectrum.basicOpen b) ≅
      Arrow.mk (affineStructure (Localization.Away b) (Localization.Away b ⊗[D] A)) :=
  Arrow.isoMk (affineRestrictionTensorIso D A b)
    (basicOpenIsoSpecAway (R := CommRingCat.of D) b)
    (affineRestrictionTensorIso_hom_structure D A b)

/-- Native flatness is equivalent for the actual restriction and its tensor base change. -/
theorem flat_morphismRestrict_iff_tensor (b : D) :
    Flat (affineStructure D A ∣_ PrimeSpectrum.basicOpen b) ↔
      Flat (affineStructure (Localization.Away b) (Localization.Away b ⊗[D] A)) :=
  MorphismProperty.arrow_mk_iso_iff (@Flat) (affineRestrictionTensorArrowIso D A b)

/-- A finite-type algebra over a domain has a flat actual restriction over a principal open. -/
theorem exists_nonzero_flat_morphismRestrict [IsDomain D] [Algebra.FiniteType D A] :
    ∃ b : D, b ≠ 0 ∧ Flat (affineStructure D A ∣_ PrimeSpectrum.basicOpen b) := by
  obtain ⟨b, hb, hflat⟩ :=
    Hironaka.Algebra.GenericFlatness.exists_nonzero_flat_finiteType_algebra D A
  exact ⟨b, hb, (flat_morphismRestrict_iff_tensor D A b).mpr hflat⟩

/-- A nonzero element of a domain defines a nonempty actual affine principal open. -/
theorem basicOpen_nonempty_of_ne_zero [IsDomain D] {b : D} (hb : b ≠ 0) :
    Nonempty (PrimeSpectrum.basicOpen b) := by
  refine ⟨⟨(⊥ : PrimeSpectrum D), ?_⟩⟩
  change b ∉ (⊥ : Ideal D)
  simpa only [Ideal.mem_bot] using hb

/-- A nonzero element of a domain defines a dense actual affine principal open. -/
theorem basicOpen_dense_of_ne_zero [IsDomain D] {b : D} (hb : b ≠ 0) :
    Dense (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum D)) := by
  apply (PrimeSpectrum.basicOpen b).isOpen.dense
  obtain ⟨x⟩ := basicOpen_nonempty_of_ne_zero D hb
  exact ⟨x.1, x.2⟩

/-- Generic flatness of the actual morphism between affine schemes over an integral base. -/
theorem exists_nonempty_flat_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffine X] [IsAffine Y] [IsIntegral Y] [LocallyOfFiniteType f] :
    ∃ U : Y.Opens, Nonempty U ∧ Flat (f ∣_ U) := by
  let D : Type u := Γ(Y, ⊤)
  let A : Type u := Γ(X, ⊤)
  let : Algebra D A := f.appTop.hom.toAlgebra
  let : IsDomain D := inferInstance
  let : Algebra.FiniteType D A := RingHom.finiteType_algebraMap.mp
    (HasRingHomProperty.appTop (P := @LocallyOfFiniteType) f inferInstance)
  obtain ⟨b, hb, hflat⟩ := exists_nonzero_flat_morphismRestrict D A
  let g := Spec.map f.appTop
  let V : (Spec (CommRingCat.of D)).Opens := PrimeSpectrum.basicOpen b
  let iY : V.toScheme ⟶ Y := V.ι ≫ Y.isoSpec.inv
  let : IsOpenImmersion iY := by dsimp [iY]; infer_instance
  have H : IsPullback
      ((g ⁻¹ᵁ V).ι ≫ X.isoSpec.inv) (g ∣_ V) f iY := by
    refine (isPullback_morphismRestrict g V).flip.of_iso
      (Iso.refl _) X.isoSpec.symm (Iso.refl _) Y.isoSpec.symm ?_ ?_ ?_ ?_
    · simp
    · simp
    · exact (show X.isoSpec.inv ≫ f = g ≫ Y.isoSpec.inv from
        (arrowIsoSpecΓOfIsAffine f).inv.w).symm
    · simp [iY]
  have hpbflat : Flat (pullback.snd f iY) := by
    apply (MorphismProperty.cancel_left_of_respectsIso @Flat H.isoPullback.hom _).mp
    rw [H.isoPullback_hom_snd]
    exact hflat
  refine ⟨iY.opensRange, ?_, ?_⟩
  · obtain ⟨v⟩ := basicOpen_nonempty_of_ne_zero D hb
    exact ⟨⟨iY v, ⟨v, rfl⟩⟩⟩
  · exact (MorphismProperty.arrow_mk_iso_iff @Flat
      (morphismRestrictOpensRange f iY)).mpr hpbflat

end Hironaka.Geometry.AffineGenericFlatness
