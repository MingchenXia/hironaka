import Hironaka.Resolution.HironakaG3RBoundaryTop
import Hironaka.Resolution.HironakaG3IndexedTopContactEndpoint
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaG3PureIndexedBoundaryTop
noncomputable section
open Hironaka.BlowupSequences BlowupTowers NormalCrossings SubmanifoldChartedSpace
  HironakaActualLocallyFiniteBoundary HironakaActualIndexedBoundaryContinuation
  HironakaG3RPureFinal HironakaG3RBoundaryTop HironakaG3IndexedTopContactEndpoint

/-- In full ambient dimension the identity resolves an arbitrary indexed boundary. -/
theorem pure_indexed_boundary_identity {n d : ℕ} {X : CMfd.{u} n} {κ : Type v}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W) (hd : n ≤ d)
    (hPure : W ⊆ closure (regularLocus (n := n) W d))
    (D : κ → Set X) (hD : IsLocallyFiniteSNCDivisor n D) :
    ∃ (ρ : Type v) (B : ρ → Set X),
      (id : X → X) '' strictTransform n (id : X → X) W = W ∧
      IsIsomorphismOver n (id : X → X) (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ j, D j)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n (id : X → X) W) ∧
      (∀ z ∈ strictTransform n (id : X → X) W, RegularAtDim (n := n) (strictTransform n (id : X → X) W) z d) ∧
      (id : X → X) ⁻¹' (W \ regularLocus (n := n) W d) ⊆ exceptionalLocus n (id : X → X) ∧
      IsLocallyFiniteSNCDivisor n B ∧ (∀ a, (B a).Nonempty) ∧
      (⋃ a, B a) = (id : X → X) ⁻¹' (⋃ j, D j) ∪ exceptionalLocus n (id : X → X) ∧
      (⋃ a, B a) = (id : X → X) ⁻¹' ((⋃ j, D j) ∪ W \ regularLocus (n := n) W d) ∧
      HasNormalCrossingsWithBoundary (strictTransform n (id : X → X) W) B := by
  obtain ⟨hExc,_,hSmooth,hRegular,_⟩ := identity_resolution_of_le hW hd hPure
  have hOpen := (isOpen_of_pure_of_le hW hd hPure).1
  have hSing := diff_regularLocus_eq_empty_of_le hW hd hPure
  have hStrict : strictTransform n (id : X → X) W = W := by
    simp [strictTransform,exceptionalLocus_id,hW.isClosed.closure_eq]
  have hNC : HasNormalCrossingsWithBoundary W D := hasNormalCrossingsWithBoundary_of_isOpen hOpen hD
  obtain ⟨ρ,B,hB,hNE,hUnion,hNC'⟩ := nonempty_boundary_reindex D hD hNC
  refine ⟨ρ,B,?_,?_,hSmooth,hRegular,?_,hB,hNE,?_,?_,?_⟩
  · simp [hStrict]
  · exact ⟨bijOn_id _,by rw [exceptionalLocus_id]; exact disjoint_empty _⟩
  · exact hExc.symm.subset
  · simpa [exceptionalLocus_id] using hUnion
  · simpa [hSing] using hUnion
  · simpa only [hStrict] using hNC'
end
end Hironaka.HironakaG3PureIndexedBoundaryTop
