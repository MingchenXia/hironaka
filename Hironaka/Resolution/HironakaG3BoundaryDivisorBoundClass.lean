import Hironaka.Resolution.HironakaG3GluedClassFootprint
import Hironaka.Resolution.HironakaEmbeddedBoundary
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3BoundaryDivisorBoundClass
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms HironakaG3RTowerClass

/-- A local tower class has the boundary-divisor bound when every actual
member's born divisor lies over the original boundary or in its exceptional locus. -/
def HasBoundaryDivisorBound {n : ℕ} {X : CMfd.{0} n} {κ : Type*}
    (D : κ → Set X) (K : LocalTowerClass X) : Prop :=
  ∀ (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
    K U Y T → (exceptionalDivisor T).support ⊆
      T.proj ⁻¹' ((Subtype.val : U → X) ⁻¹' (⋃ j, D j)) ∪ exceptionalLocus n T.proj
end
end Hironaka.HironakaG3BoundaryDivisorBoundClass
