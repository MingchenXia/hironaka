import Hironaka.Resolution.HironakaG3StratumTerminalNC
import Hironaka.Resolution.HironakaG8P1ArcTangentTrace
import Hironaka.Resolution.HironakaEmbeddedBoundary

/-! Projection of an un-erased strict target and its containing-stratum lift. -/
set_option autoImplicit false
open Set Filter Function TopologicalSpace Topology
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3Nonerasure
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  SubmanifoldChartedSpace HironakaDisjointFiniteControlledHistory
  HironakaG3ControlledHistorySubsetTransport HironakaG3EndpointNC
  HironakaG3StratumTerminalNC

/-- A finite tower avoiding a dense open of a closed target maps its literal
strict transform onto the entire target. -/
theorem projection_strictAlong_eq_of_centresAvoid
    {n : ℕ} {X Y : CMfd.{0} n} (W : Set X) (hW : IsClosed W)
    (O : Opens X) (hdense : W ⊆ closure (W ∩ (O : Set X)))
    (T : BlowupTower X Y) (hAvoid : RestrictEmptyTower.CentresAvoid O T) :
    T.proj '' strictAlong T W = W := by
  have hEq := HironakaG8P1ArcTangentTrace.strictAlong_eq_conventional_of_centresAvoid
    W hW O hdense T hAvoid
  have hClosed : IsClosed (T.proj '' strictAlong T W) :=
    (HironakaLocalPrincipalization.isProperMap_proj T).isClosedMap _ (by rw [hEq]; exact isClosed_closure)
  apply Subset.antisymm
  · rintro x ⟨y, hy, rfl⟩
    rw [hEq] at hy
    exact EmbeddedFromResolution.strictTransform_subset_preimage hW T hy
  · apply hdense.trans
    apply closure_minimal _ hClosed
    rintro x ⟨hxW, hxO⟩
    obtain ⟨y, rfl⟩ := HironakaLocalPrincipalization.IsBlowupSequence.surjective T.isBlowupSequence x
    refine ⟨y, ?_, rfl⟩
    rw [hEq]
    exact (EmbeddedFromResolution.mem_strictTransform_iff_of_centresAvoid O T hAvoid hW hxO).2 hxW

end
end Hironaka.HironakaG3Nonerasure
