import Hironaka.Resolution.HironakaG11ResidualActualContact
import Hironaka.Resolution.HironakaG11InvBMLowerTailSucc

set_option autoImplicit false

/-! The successor regime supplies the old member needed at a residual birth. -/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG11ResidualSelectedOld
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers HomogenizedGlueingTower MarkedIdeals MarkedIdeals.MarkedIdeal
  StepOneValue HironakaG11InvBMLower HironakaG11InvBMLowerTailSucc
  HironakaG11ResidualBirthPoint DivisorExponentAlong

/-- A positive successor level has an old member through its anchor, and
actual residual divisibility also puts the evaluated endpoint in that member. -/
theorem successor_residual_selects_old_member
    {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (A B : MarkedIdeal n X) (hA : A.IsWellFormed) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (barMarked A) T) (a z : Y) (s : ℕ)
    (hreg : stepRegime A (s+1) T a) {H : Set Y}
    (hzA : z ∈ (lowerIdealBM A (s+1) T a).N)
    (hzB : z ∈ (lowerIdealBM B (s+1) T a).N) (hzH : z ∈ H)
    (hdiv : IsDivNearAlong n (lowerIdealBM A (s+1) T a).N
      (exceptionalTermBM (n := n) (throughMembers A T a) (coeffEmptyBM A).d) H 1 z ∨
      IsDivNearAlong n (lowerIdealBM B (s+1) T a).N
      (exceptionalTermBM (n := n) (throughMembers A T a) (coeffEmptyBM A).d) H 1 z) :
    ∃ K, K ∈ throughMembers A T a ∧ z ∈ K := by
  have hne := throughMembers_ne_nil A T hreg.1
  obtain ⟨K,hK⟩ := List.exists_mem_of_ne_nil (throughMembers A T a) hne
  have hS : ∀ K ∈ throughMembers A T a, IsClosed K := fun K hK =>
    (isClosedSubmanifold_of_mem_throughMembers A hA hn T hT a K hK).1
  refine ⟨K,hK,?_⟩
  rcases hdiv with hdiv | hdiv
  · exact residual_endpoint_mem_throughMember hS hzA hzH hdiv K hK
  · exact residual_endpoint_mem_throughMember hS hzB hzH hdiv K hK

end Hironaka.HironakaG11ResidualSelectedOld
