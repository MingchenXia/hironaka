import Hironaka.Resolution.HironakaG3BoundaryDivisorBoundClass
import Hironaka.Resolution.HironakaG3AvoidingExceptionalDivisorBound
import Hironaka.Resolution.HironakaG3ContainedExceptionalDivisorBound
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3BoundaryDivisorBoundProducers
noncomputable section
open Hironaka.BlowupSequences BlowupTowers NormalCrossings RestrictEmptyTower
  HironakaActualLocallyFiniteBoundary HironakaG3IndexedContainingBoundary HironakaG3RTowerClass
  HironakaG3IndexedAvoidingBoundaryClass HironakaG3BoundaryDivisorBoundClass
  HironakaG3AvoidingExceptionalDivisorBound HironakaG3ContainedExceptionalDivisorBound

/-- The actual zero-containing stopped class has the bound. -/
theorem avoiding_class_has_boundary_divisor_bound {n r : ℕ} {X : CMfd.{0} n}
    {κ : Type*} [LinearOrder κ] (C : Set X) (D : κ → Set X)
    (hC : IsComplexAnalyticallyIrreducible (n := n) C) (hD : IsLocallyFiniteSNCDivisor n D)
    (hS : containingLabels C D hC.nonempty hD.1 = ∅) (hr : r < n)
    (hpure : C ⊆ closure (regularLocus (n := n) C r)) :
    HasBoundaryDivisorBound D (indexedAvoidingBoundaryClass C r D) := by
  intro U Y T hT
  exact indexed_avoiding_exceptional_divisor_bound C D hC hD hS hr hpure U T hT

/-- Any actual class with centres over F, where F lies in the original
boundary union, has the bound; F may be empty. -/
theorem class_has_boundary_divisor_bound_of_centres {n : ℕ} {X : CMfd.{0} n}
    {κ : Type*} (D : κ → Set X) (K : LocalTowerClass X) (F : Set X) (hF : F ⊆ ⋃ j, D j)
    (hOver : ∀ (U : Opens X) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      K U Y T → CentresOver ((Subtype.val : U → X) ⁻¹' F) T) : HasBoundaryDivisorBound D K := by
  intro U Y T hT
  exact exceptional_divisor_bound_of_centres_over_boundary (⋃ j, D j) F hF U T (hOver U Y T hT)
end
end Hironaka.HironakaG3BoundaryDivisorBoundProducers
