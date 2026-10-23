import DeJongAlterations.Geometry.NormalizationInExtensionFinite
import DeJongAlterations.Algebra.NormalizationInExtensionEtale

/-! # Generic etaleness of the actual normalization in a separable extension -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.NormalizationInExtension

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  (L : Type u) [Field L] [Algebra X.functionField L]
  [FiniteDimensional X.functionField L] [Algebra.IsSeparable X.functionField L]

attribute [local instance] sectionsAlgebra

/-- Actual affine closures in the specified separable extension have an internally
constructed nonzero source localization which is etale over the actual coefficient ring. -/
theorem exists_affine_etale_localization (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (U : NonemptyAffineOpen X) :
    ∃ c : closureRing L U, c ≠ 0 ∧ Algebra.Etale Γ(X, U.1.1) (Localization.Away c) := by
  let := (NormalizationFinite.affineCoefficientMap p ⟨U.1.1, U.1.2⟩).toAlgebra
  let : Algebra.FiniteType k Γ(X, U.1.1) :=
    NormalizationFinite.affineSections_finiteType p ⟨U.1.1, U.1.2⟩
  let : IsDomain Γ(X, U.1.1) := IsIntegral.component_integral U.1.1
  let : IsFractionRing Γ(X, U.1.1) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U.1.1 U.1.2
  exact Algebra.NormalizationInExtension.exists_etale_localization
    k Γ(X, U.1.1) X.functionField L

omit [FiniteDimensional X.functionField L] [Algebra.IsSeparable X.functionField L] in
/-- The actual principal source open, with its original structure map, is etale. -/
theorem affine_etale_open (U : NonemptyAffineOpen X) (c : closureRing L U)
    [Algebra.Etale Γ(X, U.1.1) (Localization.Away c)] :
    Etale ((Scheme.Opens.ι (X := Spec (.of (closureRing L U))) (PrimeSpectrum.basicOpen c)) ≫ affineStructure L U) := by
  let A := Γ(X, U.1.1)
  let C := closureRing L U
  let : Etale (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away c)))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr inferInstance)
  rw [← basicOpenIsoSpecAway_hom_SpecMap_assoc (R := .of C) c]
  have hm : Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away c))) ≫
      affineStructure L U =
        Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away c))) := by
    rw [affineStructure, ← Spec.map_comp]
    rfl
  rw [hm]
  infer_instance

/-- Under the actual separability hypothesis, the actual global finite alteration is
etale on an internally constructed nonempty dense source open. -/
theorem normalizationStructure_isGenericallyEtale
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] :
    IsGenericallyEtale (normalizationStructure X L) := by
  let : IsIntegral (normalization X L) := isIntegral_normalization L
  let U : NonemptyAffineOpen X :=
    (NormalizationFinite.nonemptyAffineCoordinateOpenCover X).idx (genericPoint X)
  obtain ⟨c, hc, he⟩ := exists_affine_etale_localization L p U
  let : Algebra.Etale Γ(X, U.1.1) (Localization.Away c) := he
  let V : (Spec (.of (closureRing L U))).Opens := PrimeSpectrum.basicOpen c
  let j := chartInclusion X L U
  let W := j ''ᵁ V
  have hne : (W : Set (normalization X L)).Nonempty := by
    refine ⟨j (⊥ : PrimeSpectrum (closureRing L U)), ?_⟩
    refine ⟨(⊥ : PrimeSpectrum (closureRing L U)), ?_, rfl⟩
    change c ∉ (⊥ : Ideal (closureRing L U))
    simpa only [Ideal.mem_bot] using hc
  have : Etale (V.ι ≫ j ≫ normalizationStructure X L) := by
    rw [chartInclusion_structure, ← Category.assoc]
    let := affine_etale_open L U c
    infer_instance
  refine ⟨W, W.isOpen.dense hne, ?_⟩
  rw [← j.isoImage_inv_ι V, Category.assoc, Category.assoc]
  infer_instance

end DeJongAlterations.Geometry.NormalizationInExtension
