import Hironaka.Resolution.HironakaG3DisjointPhysicalOverlap
import Hironaka.Resolution.HironakaG3UniversePhysicalClassComparisons
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3PhysicalClassComparisons
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms HironakaG3RTowerClass
  HironakaG3EmptyAwareHistory HironakaOriginalTerminalOverlapComparison MaxLocusLocal

def HasPhysicalComparisons {n : ℕ} {X : CMfd.{0} n} (K : LocalTowerClass X) : Prop :=
  G3UniversePhysicalClassComparisons.HasPhysicalComparisons K

theorem physical_comparisons_to_comparisons {n : ℕ} {X : CMfd.{0} n} {K : LocalTowerClass X}
    (h : HasPhysicalComparisons K) : HasComparisons K :=
  G3UniversePhysicalClassComparisons.physical_comparisons_to_comparisons h

end
end Hironaka.HironakaG3PhysicalClassComparisons
