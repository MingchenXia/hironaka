import Hironaka.Analytic.Unibranch.Resolution
import Hironaka.Resolution.HironakaSingularSubspaceBlowupLift
import Hironaka.Resolution.HironakaEmbeddedResolutionLocal

/-!
# The SAME embedded blowup projection in the original complex-space category

The source is the literal analytic strict transform, with analyticity produced
by the existing native theorem. Original proper bimeromorphicity is derived
from the actual projection, full off-centre LRS isomorphism and density on both
original subspaces. No proper-bimeromorphic, thinness or restriction-isomorphism
certificate is supplied. No resolution or intrinsic modification is asserted.

Blueprint: `embedded-blowup.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.EmbeddedBlowup

noncomputable section

open Hironaka Hironaka.BlowupSequences
  Hironaka HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceOpenRestriction HironakaResolutionSpaceComplex
  HironakaSingularSubspaceBlowupLift SourceReducedComplexSpace

private theorem dense_compl_trace_of_subset_closure_sdiff {X : Type} [TopologicalSpace X]
    {A B : Set X} (h : A ⊆ closure (A \ B)) : Dense {x : A | x.val ∉ B} := by
  have himage : (Subtype.val : A → X) '' {x : A | x.val ∉ B} = A \ B := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · intro hx
      exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩
  rw [dense_iff_closure_eq, eq_univ_iff_forall]
  intro x
  rw [closure_subtype]
  change x.val ∈ closure ((Subtype.val : A → X) '' {x : A | x.val ∉ B})
  rw [himage]
  exact h x.property

variable {n : ℕ} {M Y : Type}
  [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {C W : Set M} {π : Y → M}

/-- The ORIGINAL complex-space morphism is the SAME full actual projection.
Analyticity of its literal strict-transform source is internally produced. -/
def strictTransformMorphism (hπ : IsBlowupAlong n C π)
    (hWa : IsComplexAnalyticSubset (n := n) W) :
    ofClosedAnalytic (strictTransform n π W)
        (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
          hπ hWa) ⟶ ofClosedAnalytic W hWa :=
  ObjectProperty.homMk (Over.homMk (strictTransformProjection hπ hWa.isClosed)
    (strictTransformProjection_point hπ hWa.isClosed))

/-- The whole original LRS morphism, including the sheaf map, is unchanged. -/
theorem strictTransformMorphism_left (hπ : IsBlowupAlong n C π)
    (hWa : IsComplexAnalyticSubset (n := n) W) :
    (strictTransformMorphism hπ hWa).hom.left = strictTransformProjection hπ hWa.isClosed := rfl

/-- The literal original point map remains the given ambient projection. -/
theorem strictTransformMorphism_point (hπ : IsBlowupAlong n C π)
    (hWa : IsComplexAnalyticSubset (n := n) W) (y : strictTransform n π W) :
    (((strictTransformMorphism hπ hWa).hom.left.base y).val) = π y.val := rfl

/-- The original `IsIsoOver` condition is derived from the actual full
off-centre isomorphism, with the two exact original inclusion ranges. -/
theorem strictTransformMorphism_isIsoOver_compl_centre (hπ : IsBlowupAlong n C π)
    (hWa : IsComplexAnalyticSubset (n := n) W) :
    IsIsoOver (strictTransformMorphism hπ hWa) (((Subtype.val : W → M) ⁻¹' C)ᶜ) := by
  refine ⟨_, actualOpenSubspaceMap (n := n) (strictTransform n π W)
    (centreComplementPreimage hπ), inferInstance, ?_, ?_, ?_⟩
  · change range (actualOpenSubspaceMap (n := n) (strictTransform n π W)
        (centreComplementPreimage hπ)).base =
      (strictTransformProjection hπ hWa.isClosed).base ⁻¹' (((Subtype.val : W → M) ⁻¹' C)ᶜ)
    rw [range_actualOpenSubspaceMap]
    rfl
  · change LocallyRingedSpace.IsOpenImmersion
      (actualOpenSubspaceMap (n := n) (strictTransform n π W)
        (centreComplementPreimage hπ) ≫ strictTransformProjection hπ hWa.isClosed)
    rw [offCentreIso_comm hπ hWa.isClosed]
    infer_instance
  · change range (actualOpenSubspaceMap (n := n) (strictTransform n π W)
        (centreComplementPreimage hπ) ≫ strictTransformProjection hπ hWa.isClosed).base = _
    rw [offCentreIso_comm hπ hWa.isClosed, range_iso_hom_comp_base,
      range_actualOpenSubspaceMap]
    rfl

/-- Ordinary ORIGINAL ambient blowup/analytic/density geometry produces the
original proper-bimeromorphic predicate, with no such certificate as input. -/
theorem strictTransformMorphism_isProperBimeromorphic (hπ : IsBlowupAlong n C π)
    (hWa : IsComplexAnalyticSubset (n := n) W)
    (hCa : IsComplexAnalyticSubset (n := n) C) (hdense : W ⊆ closure (W \ C)) :
    IsProperBimeromorphic (strictTransformMorphism hπ hWa) := by
  refine ⟨strictTransformProjection_isProperMap hπ hWa.isClosed,
    (Subtype.val : W → M) ⁻¹' C, isAnalyticSubset_preimage_val hWa hCa, ?_, ?_,
    strictTransformMorphism_isIsoOver_compl_centre hπ hWa⟩
  · rw [interior_eq_empty_iff_dense_compl]
    exact dense_compl_trace_of_subset_closure_sdiff hdense
  · rw [interior_eq_empty_iff_dense_compl]
    change Dense ((strictTransformProjection hπ hWa.isClosed).base ⁻¹'
      {x : W | x.val ∉ C})
    exact dense_preimage_compl_centre hπ hWa.isClosed hdense

/-- The SAME original complex-space morphism is surjective onto the WHOLE
original analytic carrier under the original off-centre density hypothesis. -/
theorem strictTransformMorphism_surjective (hπ : IsBlowupAlong n C π)
    (hWa : IsComplexAnalyticSubset (n := n) W) (hdense : W ⊆ closure (W \ C)) :
    Function.Surjective (strictTransformMorphism hπ hWa).hom.left.base :=
  strictTransformProjection_surjective hπ hWa.isClosed hdense

end

end Hironaka.Analytic.Unibranch.EmbeddedBlowup
