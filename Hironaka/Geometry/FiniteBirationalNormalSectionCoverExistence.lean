import Hironaka.Geometry.FiniteBirationalNormalSectionCover

/-!
# Internally constructed Galois normalization with whole component section coverage

For an actual finite flat dominant generically-etale integral component,
the field extension, normalization, closed-immersion sections, and whole
actual fiber-product coverage are all constructed internally. No desired
geometric output or generic/global covering certificate is supplied.

The intrinsic component assembly for arbitrary reduced boundaries is a
separate step. The output here is exact coverage by actual section images.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Hironaka.Geometry.FiniteBirationalNormal

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {S T : Scheme.{u}} [IsIntegral T]

/-- An actual finite-flat integral component splits into covering closed sections after
an internally constructed actual projective normal Galois alteration. -/
theorem exists_galois_normalization_section_cover
    (p : S ⟶ Spec (.of k)) [IsVariety p] (hp : IsProjectiveOver p)
    (f : T ⟶ S) [IsDominant f] [IsFinite f] [Flat f]
    (hf : IsGenericallyEtale f) :
    ∃ L : IntermediateField S.functionField (SeparableClosure S.functionField),
      ∃ hfinite : FiniteDimensional S.functionField L,
        letI := hfinite
        IsGalois S.functionField L ∧
        IsVariety (NormalizationInExtension.normalizationStructure S L ≫ p) ∧
        IsNormalScheme (NormalizationInExtension.normalization S L) ∧
        IsFinite (NormalizationInExtension.normalizationStructure S L) ∧
        IsAlteration (NormalizationInExtension.normalizationStructure S L) ∧
        IsGenericallyEtale (NormalizationInExtension.normalizationStructure S L) ∧
        IsProjectiveOver (NormalizationInExtension.normalizationStructure S L ≫ p) ∧
        (letI := functionFieldAlgebra f;
          (∀ σ : T.functionField →ₐ[S.functionField] L,
            normalizationSection f L σ ≫
                pullback.snd f (NormalizationInExtension.normalizationStructure S L) = 𝟙 _ ∧
              IsClosedImmersion (normalizationSection f L σ)) ∧
          ⋃ σ : T.functionField →ₐ[S.functionField] L,
            Set.range (normalizationSection f L σ) = Set.univ) := by
  let := functionFieldAlgebra f
  let : FiniteDimensional S.functionField T.functionField :=
    (functionField_finite_separable f hf).1
  let : Algebra.IsSeparable S.functionField T.functionField :=
    (functionField_finite_separable f hf).2
  let E : ULift.{u} Unit → Type u := fun _ => T.functionField
  let L := Hironaka.Algebra.FiniteSeparableSplitting.commonField S.functionField E
  let hfinite : FiniteDimensional S.functionField L := inferInstance
  let : IsFinite (NormalizationInExtension.normalizationStructure S L) :=
    NormalizationInExtension.normalizationStructure_isFinite L p
  refine ⟨L, hfinite, inferInstance,
    NormalizationInExtension.normalization_isVariety p L,
    NormalizationInExtension.normalization_isNormalScheme L,
    inferInstance, NormalizationInExtension.normalizationStructure_isAlteration L p,
    NormalizationInExtension.normalizationStructure_isGenericallyEtale L p,
    FiniteProjective.isProjectiveOver_comp_of_isFinite p hp
      (NormalizationInExtension.normalizationStructure S L),
    ⟨fun σ => ⟨normalizationSection_snd f L σ, inferInstance⟩,
      normalizationSections_cover p L f ?_⟩⟩
  exact Hironaka.Algebra.FiniteSeparableSplitting.embedding S.functionField E ⟨()⟩

end Hironaka.Geometry.FiniteBirationalNormal
