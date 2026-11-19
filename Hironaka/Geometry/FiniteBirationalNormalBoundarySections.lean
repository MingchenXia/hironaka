import Hironaka.Geometry.FiniteBirationalNormalNormalSectionCoverExistence

/-!
# Exact finite boundary splitting in the original ambient fiber product

The sections retain the original closed boundary immersion and its
original ambient structure map. Their union is exactly the original
inverse image of that boundary, set theoretically as in de Jong 5.6.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hironaka.Geometry.FiniteBirationalNormal

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Z X S Y : Scheme.{u}}

/-- The actual base change of the original ambient boundary inclusion. -/
def boundaryBaseChange (j : Z ⟶ X) (h : X ⟶ S) (g : Y ⟶ S) :
    pullback (j ≫ h) g ⟶ pullback h g :=
  pullback.lift (pullback.fst (j ≫ h) g ≫ j) (pullback.snd (j ≫ h) g)
    (by rw [Category.assoc, pullback.condition])

@[reassoc (attr := simp)]
theorem boundaryBaseChange_fst (j : Z ⟶ X) (h : X ⟶ S) (g : Y ⟶ S) :
    boundaryBaseChange j h g ≫ pullback.fst h g = pullback.fst (j ≫ h) g ≫ j :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem boundaryBaseChange_snd (j : Z ⟶ X) (h : X ⟶ S) (g : Y ⟶ S) :
    boundaryBaseChange j h g ≫ pullback.snd h g = pullback.snd (j ≫ h) g :=
  pullback.lift_snd _ _ _

/-- Its actual original boundary square is Cartesian. -/
theorem isPullback_boundaryBaseChange (j : Z ⟶ X) (h : X ⟶ S) (g : Y ⟶ S) :
    IsPullback (boundaryBaseChange j h g) (pullback.fst (j ≫ h) g)
      (pullback.fst h g) j := by
  have H : IsPullback (boundaryBaseChange j h g ≫ pullback.snd h g)
      (pullback.fst (j ≫ h) g) g (j ≫ h) := by
    rw [boundaryBaseChange_snd]
    exact (IsPullback.of_hasPullback (j ≫ h) g).flip
  exact H.of_right (boundaryBaseChange_fst j h g) (IsPullback.of_hasPullback h g).flip

instance boundaryBaseChange_isClosedImmersion (j : Z ⟶ X) [IsClosedImmersion j]
    (h : X ⟶ S) (g : Y ⟶ S) : IsClosedImmersion (boundaryBaseChange j h g) :=
  MorphismProperty.of_isPullback (isPullback_boundaryBaseChange j h g).flip inferInstance

/-- The actual ambient base change has exactly the original inverse-boundary image. -/
theorem boundaryBaseChange_range (j : Z ⟶ X) (h : X ⟶ S) (g : Y ⟶ S) :
    Set.range (boundaryBaseChange j h g) = (pullback.fst h g) ⁻¹' Set.range j := by
  simpa only [Set.preimage_univ, Set.image_univ] using
    Scheme.image_preimage_eq_of_isPullback (isPullback_boundaryBaseChange j h g).flip Set.univ

section ComponentSections

variable [IsIntegral S] (j : Z ⟶ X) (h : X ⟶ S)
  [IsFinite (j ≫ h)] [Flat (j ≫ h)]
  (L : Type u) [Field L] [Algebra S.functionField L]

/-- The genuine component section into the original ambient fiber product. -/
def boundaryNormalizationSection (C : irreducibleComponents Z)
    (σ : reducedComponentEmbeddings (j ≫ h) L C) :
    NormalizationInExtension.normalization S L ⟶
      pullback h (NormalizationInExtension.normalizationStructure S L) :=
  reducedComponentSection (j ≫ h) L C σ ≫
    boundaryBaseChange j h (NormalizationInExtension.normalizationStructure S L)

@[reassoc (attr := simp)]
theorem boundaryNormalizationSection_snd (C : irreducibleComponents Z)
    (σ : reducedComponentEmbeddings (j ≫ h) L C) :
    boundaryNormalizationSection j h L C σ ≫
      pullback.snd h (NormalizationInExtension.normalizationStructure S L) = 𝟙 _ := by
  simp only [boundaryNormalizationSection, Category.assoc, boundaryBaseChange_snd,
    reducedComponentSection_snd]

instance boundaryNormalizationSection_isClosedImmersion [IsClosedImmersion j]
    (C : irreducibleComponents Z)
    (σ : reducedComponentEmbeddings (j ≫ h) L C) :
    IsClosedImmersion (boundaryNormalizationSection j h L C σ) := by
  delta boundaryNormalizationSection
  infer_instance

/-- The same original section images are the images of the genuine boundary sections. -/
theorem boundaryNormalizationSection_range (C : irreducibleComponents Z)
    (σ : reducedComponentEmbeddings (j ≫ h) L C) :
    Set.range (boundaryNormalizationSection j h L C σ) =
      boundaryBaseChange j h (NormalizationInExtension.normalizationStructure S L) ''
        Set.range (reducedComponentSection (j ≫ h) L C σ) := by
  have heq : ⇑(boundaryNormalizationSection j h L C σ) =
      ⇑(boundaryBaseChange j h (NormalizationInExtension.normalizationStructure S L)) ∘
        ⇑(reducedComponentSection (j ≫ h) L C σ) := by
    funext x
    exact Scheme.Hom.comp_apply _ _ x
  rw [heq]
  exact Set.range_comp _ _

end ComponentSections

variable {k : Type u} [Field k] {S Z X : Scheme.{u}}

/-- The actual ambient set-theoretic assertion of de Jong 5.6 for a projective variety base.
The finite normal field, projective normal alteration and all covering sections are internal.
The boundary may be nonreduced or have inseparable component fields. -/
theorem exists_normal_normalization_boundary_sections
    (p : S ⟶ Spec (.of k)) [IsVariety p] (hp : IsProjectiveOver p)
    (h : X ⟶ S) (j : Z ⟶ X) [IsClosedImmersion j]
    [IsFinite (j ≫ h)] [Flat (j ≫ h)] :
    ∃ L : IntermediateField S.functionField (AlgebraicClosure S.functionField),
      ∃ hfinite : FiniteDimensional S.functionField L,
        letI := hfinite
        Normal S.functionField L ∧
        IsVariety (NormalizationInExtension.normalizationStructure S L ≫ p) ∧
        IsNormalScheme (NormalizationInExtension.normalization S L) ∧
        IsFinite (NormalizationInExtension.normalizationStructure S L) ∧
        IsAlteration (NormalizationInExtension.normalizationStructure S L) ∧
        IsProjectiveOver (NormalizationInExtension.normalizationStructure S L ≫ p) ∧
        (∀ (C : irreducibleComponents Z) (σ : reducedComponentEmbeddings (j ≫ h) L C),
          boundaryNormalizationSection j h L C σ ≫
              pullback.snd h (NormalizationInExtension.normalizationStructure S L) = 𝟙 _ ∧
            IsClosedImmersion (boundaryNormalizationSection j h L C σ)) ∧
        ⋃ C : irreducibleComponents Z, ⋃ σ : reducedComponentEmbeddings (j ≫ h) L C,
          Set.range (boundaryNormalizationSection j h L C σ) =
            (pullback.fst h (NormalizationInExtension.normalizationStructure S L)) ⁻¹' Set.range j := by
  obtain ⟨L, hfinite, hnormal, hvar, hN, hfin, halt, hproj, _, hcover⟩ :=
    exists_normal_normalization_section_cover p hp (j ≫ h)
  let := hfinite
  refine ⟨L, hfinite, hnormal, hvar, hN, hfin, halt, hproj,
    (fun C σ => ⟨boundaryNormalizationSection_snd j h L C σ, inferInstance⟩), ?_⟩
  calc
    _ = boundaryBaseChange j h (NormalizationInExtension.normalizationStructure S L) ''
        (⋃ C : irreducibleComponents Z, ⋃ σ : reducedComponentEmbeddings (j ≫ h) L C,
          Set.range (reducedComponentSection (j ≫ h) L C σ)) := by
      simp only [Set.image_iUnion, boundaryNormalizationSection_range]
    _ = Set.range (boundaryBaseChange j h (NormalizationInExtension.normalizationStructure S L)) := by
      rw [hcover, Set.image_univ]
    _ = _ := boundaryBaseChange_range j h _

end Hironaka.Geometry.FiniteBirationalNormal
