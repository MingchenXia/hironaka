import Hironaka.Resolution.HironakaResolutionSpaceComplex
import Hironaka.Resolution.HironakaEmbeddedAnalyticLocal
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Resolution.HironakaChowLemma

/-!
# Local resolution of closed analytic subsets (goal G11, local form of G11a)

Blueprint: `blueprint/src/hironaka-g11-resolution.tex`, node `g11:resolution-local`.

Let `M` be a complex manifold, `W ⊆ M` a closed analytic subset (components of any dimensions,
possibly with interior) and `X₀ ⊆ M` an open set contained in a compact set.  The embedded
resolution of `W \ interior W` over `X₀`
(`HironakaEmbeddedAnalyticLocal.exists_embeddedResolution_analytic_of_subset_isCompact`) resolves
`W ∩ X₀` by its strict transform, with a proper blowup sequence
(`exists_isStrictTransformResolution_local`); the induced morphism of reduced closed subspaces is
then proper (`resolutionMap_isProperMap_of_isProperMap`).  This is the resolution used locally in
the proof of the Grauert--Remmert extension theorem (Hironaka `thm:GRexten2`).  Sorry-free.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaResolutionSpaceLocal

open Hironaka.BlowupSequences HironakaResolutionSpace HironakaResolutionSpaceComplex
open HironakaEmbeddedAnalytic (singularSet)

noncomputable section

section Manifold

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The singular set commutes with restriction to an open subset. -/
theorem singularSet_preimage_val {W : Set M} (U : Opens M) :
    singularSet (n := n) ((Subtype.val : U → M) ⁻¹' W) =
      (Subtype.val : U → M) ⁻¹' singularSet (n := n) W := by
  ext x
  constructor
  · rintro ⟨hxW, hreg⟩
    refine ⟨hxW, fun h => hreg ?_⟩
    obtain ⟨k, hk⟩ := mem_iUnion.mp h
    exact mem_iUnion.mpr ⟨k, AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hk⟩
  · rintro ⟨hxW, hreg⟩
    refine ⟨hxW, fun h => hreg ?_⟩
    obtain ⟨k, hk⟩ := mem_iUnion.mp h
    exact mem_iUnion.mpr ⟨k, AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp hk⟩

/-- **Local resolution (G11a over relatively compact open sets).**  For a closed analytic subset
`W` of a complex manifold `M` and an open set `X₀` contained in a compact set, there are a
complex manifold `X₀'` and a proper finite sequence of blowups `σ : X₀' → X₀` with smooth centres
over the singular set of `W ∩ X₀` whose strict transform resolves `W ∩ X₀`. -/
theorem exists_isStrictTransformResolution_local {W : Set M}
    (hWa : IsComplexAnalyticSubset (n := n) W) (X₀ : Opens M) {K : Set M} (hK : IsCompact K)
    (hX₀ : (X₀ : Set M) ⊆ K) :
    ∃ (X₀' : Type u) (_ : TopologicalSpace X₀') (_ : ChartedSpace (ComplexModel n) X₀')
      (_ : IsComplexManifold n X₀') (σ : X₀' → X₀) (E : List (Set X₀')),
      IsProperMap σ ∧ IsStrictTransformResolution n ((Subtype.val : X₀ → M) ⁻¹' W) σ E := by
  have hW₁a := isComplexAnalyticSubset_diff_interior hWa
  obtain ⟨X₀', _, _, _, σ, E, hadm, hsnc, hexc, hunion, hiso, hsub, -, -, -, -⟩ :=
    HironakaEmbeddedAnalyticLocal.exists_embeddedResolution_analytic_of_subset_isCompact hW₁a
      (interior_diff_interior W) X₀ hK hX₀
  rw [← singularSet_preimage_val] at hadm hunion hiso
  have hprop : IsProperMap σ :=
    (HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hadm.isBlowupSequence).2.1
  have h₁ := isStrictTransformResolution_of_data
    (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hW₁a X₀) hadm hsnc hexc hunion hiso
    hsub hprop.isClosedMap
  have hint : (Subtype.val : X₀ → M) ⁻¹' (W \ interior W) =
      (Subtype.val : X₀ → M) ⁻¹' W \ interior ((Subtype.val : X₀ → M) ⁻¹' W) := by
    rw [preimage_sdiff]
    congr 1
    exact X₀.isOpen.isOpenMap_subtype_val.preimage_interior_eq_interior_preimage
      continuous_subtype_val W
  rw [hint] at h₁
  exact ⟨X₀', inferInstance, inferInstance, inferInstance, σ, E, hprop,
    isStrictTransformResolution_of_diff_interior
      (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hWa X₀) h₁⟩

end Manifold

section Complex

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {M' : Type} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M']
  [IsComplexManifold n M'] {W : Set M} {σ : M' → M} {E : List (Set M')}

/-- If the blowup sequence is proper, so is the resolution morphism. -/
theorem resolutionMap_isProperMap_of_isProperMap (h : IsStrictTransformResolution n W σ E)
    (hσ : IsProperMap σ) : IsProperMap (resolutionMap h).base := by
  change IsProperMap (fun y : strictTransform n σ W => (⟨σ y.val, _⟩ : W))
  refine isProperMap_of_comp_of_t2 (g := (Subtype.val : W → M))
    ((h.contMDiff.continuous.comp continuous_subtype_val).subtype_mk _) continuous_subtype_val ?_
  exact hσ.comp h.isClosed_strictTransform.isClosedEmbedding_subtypeVal.isProperMap

end Complex

end

end Hironaka.HironakaResolutionSpaceLocal
