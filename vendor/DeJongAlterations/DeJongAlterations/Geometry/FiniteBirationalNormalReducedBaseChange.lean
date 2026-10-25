import DeJongAlterations.Geometry.FiniteBirationalNormalReducedComponents
import DeJongAlterations.Geometry.FiniteBirationalNormalSectionGeneric

/-!
# Actual base changes and sections of intrinsic reduced components

The native component inclusions cover every actual base change, including
the residue-field choices present in native scheme pullbacks.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.Geometry.FiniteBirationalNormal

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Z S Y : Scheme.{u}}

/-- The actual morphism from a component pullback into the whole pullback. -/
def reducedComponentBaseChange (f : Z ⟶ S) (g : Y ⟶ S) (C : irreducibleComponents Z) :
    pullback (reducedComponentInclusion Z C ≫ f) g ⟶ pullback f g :=
  pullback.lift (pullback.fst (reducedComponentInclusion Z C ≫ f) g ≫
      reducedComponentInclusion Z C)
    (pullback.snd (reducedComponentInclusion Z C ≫ f) g)
    (by rw [Category.assoc, pullback.condition])

@[reassoc (attr := simp)]
theorem reducedComponentBaseChange_fst (f : Z ⟶ S) (g : Y ⟶ S)
    (C : irreducibleComponents Z) :
    reducedComponentBaseChange f g C ≫ pullback.fst f g =
      pullback.fst (reducedComponentInclusion Z C ≫ f) g ≫ reducedComponentInclusion Z C :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem reducedComponentBaseChange_snd (f : Z ⟶ S) (g : Y ⟶ S)
    (C : irreducibleComponents Z) :
    reducedComponentBaseChange f g C ≫ pullback.snd f g =
      pullback.snd (reducedComponentInclusion Z C ≫ f) g :=
  pullback.lift_snd _ _ _

/-- This is the actual base change of the original component inclusion. -/
theorem isPullback_reducedComponentBaseChange (f : Z ⟶ S) (g : Y ⟶ S)
    (C : irreducibleComponents Z) :
    IsPullback (reducedComponentBaseChange f g C)
      (pullback.fst (reducedComponentInclusion Z C ≫ f) g)
      (pullback.fst f g) (reducedComponentInclusion Z C) := by
  have h : IsPullback (reducedComponentBaseChange f g C ≫ pullback.snd f g)
      (pullback.fst (reducedComponentInclusion Z C ≫ f) g)
      g (reducedComponentInclusion Z C ≫ f) := by
    rw [reducedComponentBaseChange_snd]
    exact (IsPullback.of_hasPullback (reducedComponentInclusion Z C ≫ f) g).flip
  exact h.of_right (reducedComponentBaseChange_fst f g C)
    (IsPullback.of_hasPullback f g).flip

/-- Every point of the whole native pullback lifts to an actual intrinsic component pullback. -/
theorem reducedComponentBaseChanges_cover (f : Z ⟶ S) (g : Y ⟶ S) :
    ⋃ C : irreducibleComponents Z, Set.range (reducedComponentBaseChange f g C) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : pullback.fst f g x ∈
      ⋃ C : irreducibleComponents Z, Set.range (reducedComponentInclusion Z C) := by
    rw [reducedComponents_cover]
    trivial
  obtain ⟨C, z, hz⟩ := Set.mem_iUnion.mp hx
  obtain ⟨w, hw, _⟩ := Scheme.exists_preimage_of_isPullback
    (isPullback_reducedComponentBaseChange f g C) x z hz.symm
  exact Set.mem_iUnion.mpr ⟨C, w, hw⟩

variable [IsIntegral S] (f : Z ⟶ S) [Flat f] [IsFinite f]
  (L : Type u) [Field L] [Algebra S.functionField L]

/-- Embeddings of the original actual function field of an intrinsic component. -/
abbrev reducedComponentEmbeddings (C : irreducibleComponents Z) :=
  letI := functionFieldAlgebra (reducedComponentInclusion Z C ≫ f)
  (reducedComponent Z C).functionField →ₐ[S.functionField] L

/-- A genuine section into the whole boundary pullback, with its original component retained. -/
def reducedComponentSection (C : irreducibleComponents Z)
    (σ : reducedComponentEmbeddings f L C) :
    NormalizationInExtension.normalization S L ⟶
      pullback f (NormalizationInExtension.normalizationStructure S L) :=
  normalizationSection (reducedComponentInclusion Z C ≫ f) L σ ≫
    reducedComponentBaseChange f (NormalizationInExtension.normalizationStructure S L) C

@[reassoc (attr := simp)]
theorem reducedComponentSection_snd (C : irreducibleComponents Z)
    (σ : reducedComponentEmbeddings f L C) :
    reducedComponentSection f L C σ ≫
      pullback.snd f (NormalizationInExtension.normalizationStructure S L) = 𝟙 _ := by
  simp only [reducedComponentSection, Category.assoc, reducedComponentBaseChange_snd,
    normalizationSection_snd]

instance reducedComponentSection_isClosedImmersion (C : irreducibleComponents Z)
    (σ : reducedComponentEmbeddings f L C) :
    IsClosedImmersion (reducedComponentSection f L C σ) := by
  let : IsClosedImmersion (reducedComponentSection f L C σ ≫
      pullback.snd f (NormalizationInExtension.normalizationStructure S L)) := by
    rw [reducedComponentSection_snd]
    infer_instance
  exact IsClosedImmersion.of_comp (reducedComponentSection f L C σ)
    (pullback.snd f (NormalizationInExtension.normalizationStructure S L))

end DeJongAlterations.Geometry.FiniteBirationalNormal
