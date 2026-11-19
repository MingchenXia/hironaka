import Hironaka.Resolution.HironakaG3GluedClassFootprint
import Hironaka.Resolution.HironakaEmbeddedBoundary
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3ContainedExceptionalDivisorBound
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms RestrictEmptyTower
  HironakaEmbeddedBoundary

/-- If every actual centre lies over a set contained in the boundary support,
the tower exceptional divisor lies over that support. The set can be empty. -/
theorem exceptional_divisor_bound_of_centres_over_boundary {n : ℕ} {X Y : CMfd.{0} n}
    (G F : Set X) (hFG : F ⊆ G) (U : Opens X)
    (T : BlowupTower (CMfd.of (n := n) U) Y)
    (hOver : CentresOver ((Subtype.val : U → X) ⁻¹' F) T) :
    (exceptionalDivisor T).support ⊆ T.proj ⁻¹' ((Subtype.val : U → X) ⁻¹' G) ∪ exceptionalLocus n T.proj := by
  intro y hy
  have hF := support_exceptionalDivisor_subset_of_centresOver ((Subtype.val : U → X) ⁻¹' F) T hOver hy
  exact Or.inl (hFG hF)
end
end Hironaka.HironakaG3ContainedExceptionalDivisorBound
