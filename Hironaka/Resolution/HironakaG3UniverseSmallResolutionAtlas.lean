import Hironaka.Resolution.HironakaG3UniversePureBoundaryInput
import Hironaka.Resolution.HironakaG3UniverseShrinkManifold
import Hironaka.Resolution.HironakaG3PureTargetGeometricAtlasAllDimensions
set_option autoImplicit false
set_option linter.style.haveILetI false
open Set Function
open scoped Manifold ContDiff Topology
universe u v
namespace Hironaka.HironakaG3UniverseSmallResolution
noncomputable section
open Hironaka.BlowupSequences BlowupTowers HironakaActualLocallyFiniteBoundary
  HironakaActualIndexedBoundaryContinuation HironakaG3UniverseSmallManifold
  HironakaG3UniverseShrinkManifold HironakaG3UniversePureBoundaryInput
  HironakaG3PureTargetGeometricAtlasAllDimensions HironakaG3RTowerClass

/-- An arbitrary-universe pure input admits a geometric endpoint and universal tower atlas on its literal small model. -/
theorem exists_small_model_pure_resolution {n d : ℕ} (X : CMfd.{u} n) {ι : Type v}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (hPure : W ⊆ closure (regularLocus (n := n) W d))
    (D : ι → Set X) (hD : IsLocallyFiniteSNCDivisor n D) :
    let e := shrinkDiffeomorph X
    let W₀ : Set (shrinkCMfd X) := e.symm ⁻¹' W
    ∃ (κ : Type) (D₀ : κ → Set (shrinkCMfd X)),
      IsLocallyFiniteSNCDivisor n D₀ ∧ (∀ i, (D₀ i).Nonempty) ∧
      (⋃ i, D₀ i) = e.symm ⁻¹' (⋃ i, D i) ∧
      ∃ (Y₀ : CMfd.{0} n) (P₀ : Y₀ → shrinkCMfd X) (ρ : Type) (B : ρ → Set Y₀),
        IsGluedFrom (fun _ _ _ => True) Y₀ P₀ ∧
        ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ P₀ ∧ IsProperMap P₀ ∧ Surjective P₀ ∧
        P₀ '' strictTransform n P₀ W₀ = W₀ ∧
        IsIsomorphismOver n P₀ (W₀ \ regularLocus (n := n) W₀ d ∪ W₀ ∩ ⋃ i, D₀ i)ᶜ ∧
        IsClosedSubmanifold n (strictTransform n P₀ W₀) ∧
        (∀ z ∈ strictTransform n P₀ W₀, RegularAtDim (n := n) (strictTransform n P₀ W₀) z d) ∧
        P₀ ⁻¹' (W₀ \ regularLocus (n := n) W₀ d) ⊆ exceptionalLocus n P₀ ∧
        IsLocallyFiniteSNCDivisor n B ∧ (∀ j, (B j).Nonempty) ∧
        (⋃ j, B j) = P₀ ⁻¹' (⋃ i, D₀ i) ∪ exceptionalLocus n P₀ ∧
        (⋃ j, B j) = P₀ ⁻¹' ((⋃ i, D₀ i) ∪ W₀ \ regularLocus (n := n) W₀ d) ∧
        HasNormalCrossingsWithBoundary (strictTransform n P₀ W₀) B := by
  letI : Small.{0} X := complex_manifold_small X
  let e := Shrink.homeomorph X
  have hInput := transported_pure_boundary_input X e W hW hPure D hD
  change IsComplexAnalyticSubset (n := n) ((shrinkDiffeomorph X).symm ⁻¹' W) ∧
    (shrinkDiffeomorph X).symm ⁻¹' W ⊆ closure (regularLocus (n := n) ((shrinkDiffeomorph X).symm ⁻¹' W) d) ∧
    ∃ (κ : Type) (D₀ : κ → Set (shrinkCMfd X)), IsLocallyFiniteSNCDivisor n D₀ ∧
      (∀ i, (D₀ i).Nonempty) ∧ (⋃ i, D₀ i) = (shrinkDiffeomorph X).symm ⁻¹' (⋃ i, D i) at hInput
  obtain ⟨hW₀,hPure₀,κ,D₀,hD₀,hNE,hSupp⟩ := hInput
  exact ⟨κ,D₀,hD₀,hNE,hSupp,exists_pure_target_geometric_atlas_all_dimensions _ hW₀ hPure₀ D₀ hD₀⟩
end
end Hironaka.HironakaG3UniverseSmallResolution
