import Hironaka.Algebra.FiniteNormalSplitting
import Hironaka.Geometry.FiniteBirationalNormalReducedSectionCover

/-!
# Actual finite flat boundary splitting, including inseparable and nonreduced cases

The native reduced components and their actual canonical finite function
fields internally construct one finite normal extension in the algebraic
closure. Its same actual projective normalization has covering closed
sections of the whole original pullback. Generic etaleness is not an
input or an output. The base is a projective variety over any field;
arbitrary excellent bases require a separate normalization-finiteness producer.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hironaka.Geometry.FiniteBirationalNormal

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {S Z : Scheme.{u}}

/-- The set-theoretic section splitting of an arbitrary actual finite-flat boundary
over a projective variety, with its finite normal field and projective alteration constructed.
Neither reducedness nor separability nor generic etaleness is assumed. -/
theorem exists_normal_normalization_section_cover
    (p : S ⟶ Spec (.of k)) [IsVariety p] (hp : IsProjectiveOver p)
    (f : Z ⟶ S) [IsFinite f] [Flat f] :
    ∃ L : IntermediateField S.functionField (AlgebraicClosure S.functionField),
      ∃ hfinite : FiniteDimensional S.functionField L,
        letI := hfinite
        Normal S.functionField L ∧
        IsVariety (NormalizationInExtension.normalizationStructure S L ≫ p) ∧
        IsNormalScheme (NormalizationInExtension.normalization S L) ∧
        IsFinite (NormalizationInExtension.normalizationStructure S L) ∧
        IsAlteration (NormalizationInExtension.normalizationStructure S L) ∧
        IsProjectiveOver (NormalizationInExtension.normalizationStructure S L ≫ p) ∧
        (∀ (C : irreducibleComponents Z) (σ : reducedComponentEmbeddings f L C),
          reducedComponentSection f L C σ ≫
              pullback.snd f (NormalizationInExtension.normalizationStructure S L) = 𝟙 _ ∧
            IsClosedImmersion (reducedComponentSection f L C σ)) ∧
        ⋃ C : irreducibleComponents Z, ⋃ σ : reducedComponentEmbeddings f L C,
          Set.range (reducedComponentSection f L C σ) = Set.univ := by
  let : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian p
  let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace p
  let : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace f
  let : AlgebraicGeometry.IsNoetherian Z := ⟨⟩
  let : Fintype (irreducibleComponents Z) := NoetherianSpace.finite_irreducibleComponents.fintype
  let (C : irreducibleComponents Z) := functionFieldAlgebra (reducedComponentInclusion Z C ≫ f)
  let (C : irreducibleComponents Z) :
      FiniteDimensional S.functionField (reducedComponent Z C).functionField :=
    finite_functionField (reducedComponentInclusion Z C ≫ f)
  let E : irreducibleComponents Z → Type u := fun C => (reducedComponent Z C).functionField
  let L := Hironaka.Algebra.FiniteNormalSplitting.commonField S.functionField E
  let hfinite : FiniteDimensional S.functionField L := inferInstance
  let : IsFinite (NormalizationInExtension.normalizationStructure S L) :=
    NormalizationInExtension.normalizationStructure_isFinite L p
  refine ⟨L, hfinite, inferInstance,
    NormalizationInExtension.normalization_isVariety p L,
    NormalizationInExtension.normalization_isNormalScheme L, inferInstance,
    NormalizationInExtension.normalizationStructure_isAlteration L p,
    FiniteProjective.isProjectiveOver_comp_of_isFinite p hp
      (NormalizationInExtension.normalizationStructure S L),
    (fun C σ => ⟨reducedComponentSection_snd f L C σ, inferInstance⟩),
    reducedComponentSections_cover p L f ?_⟩
  exact Hironaka.Algebra.FiniteNormalSplitting.embedding S.functionField E

end Hironaka.Geometry.FiniteBirationalNormal
