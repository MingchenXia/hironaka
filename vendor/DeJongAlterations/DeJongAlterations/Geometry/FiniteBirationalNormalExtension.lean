import DeJongAlterations.Algebra.FiniteSeparableSplitting
import DeJongAlterations.Geometry.FiniteBirationalNormalFunctionField
import DeJongAlterations.Geometry.NormalizationInExtension
import DeJongAlterations.Geometry.FiniteProjectivePreservation

/-!
# An actual common Galois normalization for generically etale component maps

The input consists of the original dominant component morphisms. Their
actual canonical function fields are internally finite and separable. One
finite Galois field and its native normalization are then constructed,
retaining the original projective coefficient structure.

The further assertion that all pulled-back boundary points are covered by
actual section images is a separate geometric bridge.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace DeJongAlterations.Geometry.FiniteBirationalNormal

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {S : Scheme.{u}} {ι : Type u} [Finite ι]

/-- Actual generically-etale component maps internally produce one finite
Galois field and the same genuine projective normal generically-etale alteration.
No field extension, embeddings, normalization or geometric output is supplied. -/
theorem exists_common_galois_normalization (p : S ⟶ Spec (.of k)) [IsVariety p]
    (hp : IsProjectiveOver p) (T : ι → Scheme.{u}) [∀ i, IsIntegral (T i)]
    (f : ∀ i, T i ⟶ S) [∀ i, IsDominant (f i)] [∀ i, LocallyOfFiniteType (f i)]
    (hf : ∀ i, IsGenericallyEtale (f i)) :
    ∃ L : IntermediateField S.functionField (SeparableClosure S.functionField),
      ∃ hfinite : FiniteDimensional S.functionField L,
        letI := hfinite
        IsGalois S.functionField L ∧
        (letI (i : ι) := functionFieldAlgebra (f i);
          Nonempty (∀ i, (T i).functionField →ₐ[S.functionField] L)) ∧
        IsVariety (NormalizationInExtension.normalizationStructure S L ≫ p) ∧
        IsNormalScheme (NormalizationInExtension.normalization S L) ∧
        IsFinite (NormalizationInExtension.normalizationStructure S L) ∧
        IsAlteration (NormalizationInExtension.normalizationStructure S L) ∧
        IsGenericallyEtale (NormalizationInExtension.normalizationStructure S L) ∧
        IsProjectiveOver (NormalizationInExtension.normalizationStructure S L ≫ p) ∧
        ∃ e : (NormalizationInExtension.normalization S L).functionField ≃+* L,
          e.toRingHom.comp (NormalizationInExtension.functionFieldMap
            (NormalizationInExtension.normalizationStructure S L)).hom =
              algebraMap S.functionField L := by
  let (i : ι) := functionFieldAlgebra (f i)
  let (i : ι) : FiniteDimensional S.functionField (T i).functionField :=
    (functionField_finite_separable (f i) (hf i)).1
  let (i : ι) : Algebra.IsSeparable S.functionField (T i).functionField :=
    (functionField_finite_separable (f i) (hf i)).2
  let L := DeJongAlterations.Algebra.FiniteSeparableSplitting.commonField
    S.functionField (fun i => (T i).functionField)
  let hfinite : FiniteDimensional S.functionField L := inferInstance
  let : IsFinite (NormalizationInExtension.normalizationStructure S L) :=
    NormalizationInExtension.normalizationStructure_isFinite L p
  refine ⟨L, hfinite, inferInstance,
    ⟨fun i => DeJongAlterations.Algebra.FiniteSeparableSplitting.embedding
      S.functionField (fun i => (T i).functionField) i⟩,
    NormalizationInExtension.normalization_isVariety p L,
    NormalizationInExtension.normalization_isNormalScheme L,
    inferInstance, NormalizationInExtension.normalizationStructure_isAlteration L p,
    NormalizationInExtension.normalizationStructure_isGenericallyEtale L p,
    FiniteProjective.isProjectiveOver_comp_of_isFinite p hp
      (NormalizationInExtension.normalizationStructure S L),
    NormalizationInExtension.normalizationFunctionFieldEquiv L,
    NormalizationInExtension.normalizationFunctionFieldEquiv_comp L⟩

end DeJongAlterations.Geometry.FiniteBirationalNormal
