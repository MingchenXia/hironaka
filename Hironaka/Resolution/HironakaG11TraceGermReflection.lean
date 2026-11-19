import Hironaka.Resolution.HironakaG11TraceGermDichotomy
import Hironaka.Resolution.HironakaG8TestTraceIdentity
import Hironaka.Invariant.MemberInterAlong

set_option autoImplicit false

/-! Actual endpoint exceptional divisibility reflects back to containment
of the literal birth trace germ in the old boundary member. -/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG11TraceGermReflection
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal BoundaryCount MemberInterAlong MemberInterTowerAlong
  DivisorExponentAlong HironakaG11InvBMLower HironakaG11TraceGermDichotomy
  HironakaG8TestTraceIdentity

/-- If an exceptional sum containing the strict old member is divisible
along a transformed boundary trace, then the initial smooth carrier--member
trace is locally contained in that old member at the projected point. -/
theorem initial_trace_germ_contained_of_div
    {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (D K : Set X) (hD : D ∈ M.E) (hK : IsClosedSubmanifold n K)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    {S : List (Set Y)} (hS : ∀ H ∈ S, IsClosed H)
    (hmem : strictAlong T K ∈ S) (e : ℕ) {y : Y}
    (hyN : y ∈ strictAlong T M.N) (hyD : y ∈ strictAlong T D)
    (hdiv : IsDivNearAlong n (strictAlong T M.N) (exceptionalTermBM (n := n) S e)
      (strictAlong T D) 1 y) :
    ∀ᶠ x in 𝓝 (T.proj y), x ∈ M.N ∩ D → x ∈ K := by
  obtain ⟨i,hi⟩ := List.get_of_mem hD
  have hA : IsClosedSubmanifold n (M.N ∩ D) := by
    have h := isClosedSubmanifold_inter_memberInter hn hM.isClosedSubmanifold_N.1
      hM.isSNCDivisor hM.isTransverse {i}
    rwa [memberInter_singleton,hi] at h
  have hyA := mem_strictAlong_inter_of_test M hM D hD T hT hyN hyD
  have hqA : T.proj y ∈ M.N ∩ D := strictAlong_subset_preimage T hA.1 hyA
  by_contra hnot
  obtain ⟨V,hqV,hDense⟩ := exists_local_dense_off_of_not_contained hA hK hqA hnot
  exact not_div_of_trace_density M hM V D K hD hK.1 hDense T hT hS hmem e hqV hyN hyD hdiv

end Hironaka.HironakaG11TraceGermReflection
