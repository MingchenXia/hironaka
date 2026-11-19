import Hironaka.Resolution.HironakaReducedComplexAnalyticMorphismCharts
import Hironaka.Resolution.HironakaResolutionSpaceComplex

/-!
# Arbitrary intrinsic actual model morphisms have local ambient representatives

The target need not already be in an open coordinate space. The genuine
original target chart, actual open-immersion factorization, and intrinsic
coordinate-model lifting internally construct the ambient representative.
The result retains the entire actual quotient-sheaf square over ℂ.

Blueprint: `hironaka-singular-subspace-blowup-cartier-universal-ambient-lifting.tex`.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaSingularSubspaceBlowupCartierUniversalAmbientLifting

open Hironaka.HolomorphicIdealSheaves
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction HironakaReducedComplexAnalyticSpaces
  HironakaActualAnalyticSubspaceIntrinsicLifting HironakaReducedComplexAnalyticMorphismCharts
  HironakaActualAnalyticSubspaceLocalFunctions
  HironakaResolutionSpaceComplex

noncomputable section

variable {n m : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N]

/-- An arbitrary original intrinsic actual subspace morphism, into ANY
manifold-embedded actual target, internally acquires a genuine local ambient
holomorphic representative with the ENTIRE original LRS square. -/
theorem exists_local_ambient_representative {S : Set N} {W : Set M}
    (F : actualSubspaceLocallyRingedSpace (n := m) S ⟶ actualSubspaceLocallyRingedSpace (n := n) W)
    (hF : F ≫ subspacePointMap (n := n) W = subspacePointMap (n := m) S) (x : S) :
    ∃ (T : Opens N) (hxT : x.val ∈ T) (O : Opens T) (_hxO : (⟨x.val, hxT⟩ : T) ∈ O)
      (G : O → M) (hG : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ G)
      (hSW : ∀ z ∈ (Subtype.val : O → T) ⁻¹' ((Subtype.val : T → N) ⁻¹' S), G z ∈ W),
      actualSubspaceMap hG hSW =
        actualOpenSubspaceMap (n := m) ((Subtype.val : T → N) ⁻¹' S) O ≫
          actualOpenSubspaceMap (n := m) S T ≫ F := by
  let q : M := (F.base x).val
  let j : actualSubspaceLocallyRingedSpace (n := n) (chartTrace W q) ⟶
      actualSubspaceLocallyRingedSpace (n := n) W := chartModelMap (n := n) W q
  have hj : LocallyRingedSpace.IsOpenImmersion j :=
    chartModelMap_isOpenImmersion (n := n) W q
  have hjp : j ≫ subspacePointMap (n := n) W = subspacePointMap (n := n) (chartTrace W q) :=
    chartModelMap_point (n := n) W q
  have hxj : F.base x ∈ Set.range j.base := mem_range_chartModelMap W (F.base x).property
  obtain ⟨T, hxT, H, hHp, hHfac⟩ := exists_actual_model_chart_factor
    (Over.mk (subspacePointMap (n := n) W)) F hF j (hj := hj) hjp x hxj
  let xT : ((Subtype.val : T → N) ⁻¹' S) := ⟨⟨x.val, hxT⟩, x.property⟩
  obtain ⟨O, hxO, f, hf, hCD, hfH⟩ := exists_actualSubspaceMap_local_holomorphic_lift H hHp xT
  let G : O → M := fun z => (((chartDiffeo (n := n) q).symm (f z) : chartDomain q) : M)
  have hG : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ G :=
    contMDiff_subtype_val.comp ((chartDiffeo (n := n) q).symm.contMDiff.comp hf)
  have hSW : ∀ z ∈ (Subtype.val : O → T) ⁻¹' ((Subtype.val : T → N) ⁻¹' S), G z ∈ W := by
    intro z hz
    exact hCD z hz
  have hmap : actualSubspaceMap hG hSW = actualSubspaceMap hf hCD ≫ j := by
    apply actualSubspaceMap_eq_of_base_eq
    · exact actualSubspaceMap_point hG hSW
    · rw [Category.assoc, hjp, actualSubspaceMap_point]
    · ext z
      rfl
  refine ⟨T, hxT, O, hxO, G, hG, hSW, ?_⟩
  calc
    _ = actualSubspaceMap hf hCD ≫ j := hmap
    _ = (actualOpenSubspaceMap (n := m) ((Subtype.val : T → N) ⁻¹' S) O ≫ H) ≫ j :=
      congrArg (fun k => k ≫ j) hfH
    _ = actualOpenSubspaceMap (n := m) ((Subtype.val : T → N) ⁻¹' S) O ≫ (H ≫ j) :=
      Category.assoc _ _ _
    _ = _ := congrArg
      (fun k => actualOpenSubspaceMap (n := m) ((Subtype.val : T → N) ⁻¹' S) O ≫ k) hHfac

end

end Hironaka.HironakaSingularSubspaceBlowupCartierUniversalAmbientLifting
