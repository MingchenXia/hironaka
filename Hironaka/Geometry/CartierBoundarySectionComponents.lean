import Hironaka.Geometry.CartierBoundaryAlteredModel
import Hironaka.Geometry.FiniteBirationalNormalExtension
import Hironaka.Geometry.FiniteBirationalNormalBoundarySections
import Hironaka.Geometry.AlterationDominatingBaseChangeComponentEtale

/-!
# Original nonflat Cartier boundary components and their actual sections

The component maps and their generic etaleness are derived from the
original reduced boundary, without a component flatness assumption.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hironaka.Geometry.CartierBoundarySection

open Scheme.IdealSheafData CartierBoundaryComponentDimension CartierBoundaryDominance
open FiniteBirationalNormal

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X S : Scheme.{u}}

/-- The actual component inclusion retains the original native irreducible component. -/
theorem componentBoundaryInclusion_range_component (D : X.IdealSheafData)
    (C : DivisorComponent D) :
    Set.range (componentBoundaryInclusion D C) ∈ irreducibleComponents (reducedBoundary D) := by
  obtain ⟨V, hV, hVC⟩ := C.property
  have hrange : Set.range (componentBoundaryInclusion D C) = V := by
    apply Set.image_injective.mpr (reducedBoundaryInclusion D).isClosedEmbedding.injective
    calc
      (reducedBoundaryInclusion D) '' Set.range (componentBoundaryInclusion D C) =
          Set.range (componentInclusion D C) := by
        rw [← Set.range_comp]
        change Set.range (componentBoundaryInclusion D C ≫ reducedBoundaryInclusion D) = _
        rw [componentBoundaryInclusion_structure]
      _ = (C.val : Set X) := by
        exact range_subschemeι _
      _ = (reducedBoundaryInclusion D) '' V := hVC.symm
  rwa [hrange]

/-- Every point of the actual full support lifts to an original reduced component. -/
theorem components_cover (D : X.IdealSheafData) (x : X) (hx : x ∈ D.support) :
    ∃ C : DivisorComponent D, ∃ z : componentScheme D C, componentInclusion D C z = x := by
  let V := irreducibleComponent (⟨x, hx⟩ : D.support)
  let hV : V ∈ irreducibleComponents D.support := irreducibleComponent_mem_irreducibleComponents _
  let C := divisorComponentOf D V hV
  have hxC : x ∈ (C.val : Set X) := ⟨⟨x, hx⟩, mem_irreducibleComponent, rfl⟩
  have hrange : Set.range (componentInclusion D C) = (C.val : Set X) := range_subschemeι _
  rw [← hrange] at hxC
  exact ⟨C, hxC⟩

/-- Generic etaleness of each actual reduced component follows from the original whole map. -/
theorem component_genericallyEtale (f : X ⟶ S) (D : X.IdealSheafData)
    [AlgebraicGeometry.IsNoetherian (reducedBoundary D)]
    (hGE : IsGenericallyEtale (reducedBoundaryInclusion D ≫ f)) (C : DivisorComponent D) :
    IsGenericallyEtale (componentInclusion D C ≫ f) := by
  let : IsReduced (reducedBoundary D) :=
    ReducedClosedSubscheme.isReduced_vanishingIdeal_subscheme _
  rw [← componentBoundaryInclusion_structure D C, Category.assoc]
  apply IsGenericallyEtale.comp _ hGE
  exact AlterationDominatingBaseChange.genericallyEtale_component
    (componentBoundaryInclusion D C) (componentBoundaryInclusion_range_component D C)

variable [IsIntegral S] (f : X ⟶ S) (D : X.IdealSheafData)
  [IsFinite (reducedBoundaryInclusion D ≫ f)]
  [∀ C : DivisorComponent D, IsDominant (componentInclusion D C ≫ f)]
  (L : Type u) [Field L] [Algebra S.functionField L]

/-- Compatible embeddings of the actual original component function field. -/
abbrev ComponentEmbeddings (C : DivisorComponent D) :=
  letI := functionFieldAlgebra (componentInclusion D C ≫ f)
  (componentScheme D C).functionField →ₐ[S.functionField] L

/-- A literal ambient section, through the original reduced component map. -/
def ambientSection (C : DivisorComponent D) (σ : ComponentEmbeddings f D L C) :
    NormalizationInExtension.normalization S L ⟶
      pullback f (NormalizationInExtension.normalizationStructure S L) :=
  normalizationSection (componentInclusion D C ≫ f) L σ ≫
    boundaryBaseChange (componentInclusion D C) f
      (NormalizationInExtension.normalizationStructure S L)

@[reassoc (attr := simp)]
theorem ambientSection_snd (C : DivisorComponent D) (σ : ComponentEmbeddings f D L C) :
    ambientSection f D L C σ ≫
      pullback.snd f (NormalizationInExtension.normalizationStructure S L) = 𝟙 _ := by
  simp only [ambientSection, Category.assoc, boundaryBaseChange_snd, normalizationSection_snd]

instance ambientSection_isClosedImmersion (C : DivisorComponent D)
    (σ : ComponentEmbeddings f D L C) : IsClosedImmersion (ambientSection f D L C σ) := by
  delta ambientSection
  infer_instance

/-- Every actual section image lies in the inverse image of the original full support. -/
theorem ambientSection_mem_support (C : DivisorComponent D)
    (σ : ComponentEmbeddings f D L C) (y : NormalizationInExtension.normalization S L) :
    pullback.fst f (NormalizationInExtension.normalizationStructure S L)
      (ambientSection f D L C σ y) ∈ D.support := by
  change pullback.fst f _
    (boundaryBaseChange _ f _ (normalizationSection _ L σ y)) ∈ D.support
  rw [← Scheme.Hom.comp_apply, boundaryBaseChange_fst]
  change componentInclusion D C _ ∈ D.support
  apply SNCSubdivisorComponent.component_le_support D C
  exact (range_subschemeι (vanishingIdeal C.val)).subset ⟨_, rfl⟩

end Hironaka.Geometry.CartierBoundarySection
