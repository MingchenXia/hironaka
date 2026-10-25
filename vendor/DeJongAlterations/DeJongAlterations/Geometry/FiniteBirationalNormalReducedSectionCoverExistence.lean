import DeJongAlterations.Geometry.FiniteBirationalNormalReducedSectionCover

/-!
# Internally split the actual reduced finite flat boundary

The native irreducible components, their canonical finite separable
function fields, one common Galois field, the same actual projective
normalization, and its covering closed sections are all constructed.
Flatness is imposed only on the whole original boundary map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.Geometry.FiniteBirationalNormal

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {S Z : Scheme.{u}}

/-- An actual reduced finite-flat generically etale boundary is covered by genuine
closed sections after an internally constructed projective Galois normalization.
No component decomposition, field extension, section, or covering certificate is supplied. -/
theorem exists_galois_normalization_reduced_section_cover
    (p : S ⟶ Spec (.of k)) [IsVariety p] (hp : IsProjectiveOver p)
    (f : Z ⟶ S) [IsFinite f] [Flat f] [IsReduced Z]
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
  let T : irreducibleComponents Z → Scheme.{u} := fun C => reducedComponent Z C
  let fC : ∀ C, T C ⟶ S := fun C => reducedComponentInclusion Z C ≫ f
  have hfC : ∀ C, IsGenericallyEtale (fC C) := reducedComponent_genericallyEtale f hf
  obtain ⟨L, hfinite, hG, he, hvar, hnormal, hfin, halt, hEt, hproj, _⟩ :=
    exists_common_galois_normalization p hp T fC hfC
  let := hfinite
  let := hG
  obtain ⟨e⟩ := he
  refine ⟨L, hfinite, hG, hvar, hnormal, hfin, halt, hEt, hproj,
    (fun C σ => ⟨reducedComponentSection_snd f L C σ, inferInstance⟩),
    reducedComponentSections_cover p L f e⟩

end DeJongAlterations.Geometry.FiniteBirationalNormal
