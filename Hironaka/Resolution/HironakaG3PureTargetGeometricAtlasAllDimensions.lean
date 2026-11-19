import Hironaka.Resolution.HironakaG3PureTargetGeometricAtlas
import Hironaka.Resolution.HironakaG3IdentityGeometricAtlas
import Hironaka.Resolution.HironakaG3PureIndexedBoundaryTop
import Hironaka.Resolution.HironakaG3PureGlobalComponents
import Hironaka.Resolution.HironakaG3SeparatedCompositionFinalSupport
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3PureTargetGeometricAtlasAllDimensions
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers NormalCrossings SubmanifoldChartedSpace
  HironakaActualLocallyFiniteBoundary HironakaActualIndexedBoundaryContinuation GlobalComponents
  HironakaG3PureGlobalComponents HironakaG3SeparatedCompositionFinalSupport
  HironakaG3PureTargetGeometricAtlas HironakaG3IdentityGeometricAtlas HironakaG3RTowerClass HironakaG3PureIndexedBoundaryTop

theorem exists_pure_target_geometric_atlas_all_dimensions {n d : ℕ} {X : CMfd.{0} n} {κ : Type}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (hPure : W ⊆ closure (regularLocus (n := n) W d))
    (D : κ → Set X) (hD : IsLocallyFiniteSNCDivisor n D) :
    ∃ (Y : CMfd.{0} n) (P : Y → X) (ρ : Type) (B : ρ → Set Y),
      IsGluedFrom (fun _ _ _ => True) Y P ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ P ∧ IsProperMap P ∧ Surjective P ∧
      P '' strictTransform n P W = W ∧
      IsIsomorphismOver n P (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ j, D j)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n P W) ∧
      (∀ z ∈ strictTransform n P W, RegularAtDim (n := n) (strictTransform n P W) z d) ∧
      P ⁻¹' (W \ regularLocus (n := n) W d) ⊆ exceptionalLocus n P ∧
      IsLocallyFiniteSNCDivisor n B ∧ (∀ a, (B a).Nonempty) ∧
      (⋃ a, B a) = P ⁻¹' (⋃ j, D j) ∪ exceptionalLocus n P ∧
      (⋃ a, B a) = P ⁻¹' ((⋃ j, D j) ∪ W \ regularLocus (n := n) W d) ∧
      HasNormalCrossingsWithBoundary (strictTransform n P W) B := by
  by_cases hd : d < n
  · exact exists_pure_target_geometric_atlas W hW hd hPure D hD
  · obtain ⟨ρ,B,hImage,hGood,hSmooth,hRegular,hSing,hB,hNE,hSupport,hSupport',hNC⟩ :=
      pure_indexed_boundary_identity W hW (Nat.le_of_not_gt hd) hPure D hD
    exact ⟨X,id,ρ,B,identity_geometric_atlas X,contMDiff_id,isProperMap_id,surjective_id,hImage,hGood,hSmooth,hRegular,
      hSing,hB,hNE,hSupport,hSupport',hNC⟩
end
end Hironaka.HironakaG3PureTargetGeometricAtlasAllDimensions
