import Hironaka.Geometry.FiniteBirationalNormalBoundarySections

/-!
# A genuine finite family of sections splitting the original ambient boundary

The finite index is the actual dependent sum of native components and
their compatible field embeddings. Its finiteness is proved internally.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hironaka.Geometry.FiniteBirationalNormal

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {S Z X : Scheme.{u}}

/-- There are genuinely finitely many intrinsic component embeddings into any common field. -/
theorem finite_reducedComponentSectionIndex
    (p : S ⟶ Spec (.of k)) [IsVariety p]
    (f : Z ⟶ S) [IsFinite f] [Flat f]
    (L : Type u) [Field L] [Algebra S.functionField L] :
    Finite (Σ C : irreducibleComponents Z, reducedComponentEmbeddings f L C) := by
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
  let (C : irreducibleComponents Z) : Finite (reducedComponentEmbeddings f L C) := inferInstance
  infer_instance

/-- De Jong 5.6 over a projective variety base, with an internally constructed actual finite
normal alteration and an actual finite family of sections of the original ambient morphism.
The image union is the exact inverse image of the original closed boundary.
No reducedness, separability, generic etaleness, or output certificate is assumed. -/
theorem exists_finite_normal_alteration_boundary_sections
    (p : S ⟶ Spec (.of k)) [IsVariety p] (hp : IsProjectiveOver p)
    (h : X ⟶ S) (j : Z ⟶ X) [IsClosedImmersion j]
    [IsFinite (j ≫ h)] [Flat (j ≫ h)] :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ S) (ι : Type u) (_ : Finite ι)
      (σ : ι → (Y ⟶ pullback h g)),
      IsFinite g ∧ IsAlteration g ∧ IsNormalScheme Y ∧
      IsVariety (g ≫ p) ∧ IsProjectiveOver (g ≫ p) ∧
      (∀ i, σ i ≫ pullback.snd h g = 𝟙 Y ∧ IsClosedImmersion (σ i)) ∧
      ⋃ i, Set.range (σ i) = (pullback.fst h g) ⁻¹' Set.range j := by
  obtain ⟨L, hfinite, _, hvar, hN, hfin, halt, hproj, hsections, hcover⟩ :=
    exists_normal_normalization_boundary_sections p hp h j
  let := hfinite
  let Y := NormalizationInExtension.normalization S L
  let g := NormalizationInExtension.normalizationStructure S L
  let ι := Σ C : irreducibleComponents Z, reducedComponentEmbeddings (j ≫ h) L C
  let : Finite ι := finite_reducedComponentSectionIndex p (j ≫ h) L
  let σ : ι → (Y ⟶ pullback h g) := fun i => boundaryNormalizationSection j h L i.1 i.2
  refine ⟨Y, g, ι, inferInstance, σ, hfin, halt, hN, hvar, hproj,
    (fun i => hsections i.1 i.2), ?_⟩
  simpa only [ι, σ, g, Set.iUnion_sigma] using hcover

end Hironaka.Geometry.FiniteBirationalNormal
