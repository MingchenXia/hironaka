import Hironaka.Resolution.HironakaG1LocalNormalizedOrder
import Hironaka.Resolution.HironakaG8MixedOrderInvariance
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1LocalOffBoundary
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  ResolutionInvariantSpec HironakaG8LocalHistory HironakaG8MixedOrderInvariance
  HironakaG1LocalNormalizedOrder HironakaSharpOriginalProductTraceOrder
  MarkedIdealEquivalence.MarkedIdeal NonmonomialOrderLocal

/-- Away from the transformed retained boundary, normalized nonmonomial
orders agree at every actual suffix of locally equivalent native records. -/
theorem nmOrd_along_local_off_boundary {n kA kB : ℕ} {X Y : CMfd.{0} n}
    (A B : MarkedIdeal n X) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hN : A.N = B.N) (hL : LocWPEquiv A B) (T : BlowupTower X Y) (hT : IsGeoTestTower A T)
    (y : Y) (hy : y ∈ (geoTransformAlong A T).cosupp)
    (hoff : ∀ H ∈ (geoTransformAlong A T).E, y ∉ H) :
    (geoTransformAlong B T).d * nmOrd (geoTransformAlong A T) y =
      (geoTransformAlong A T).d * nmOrd (geoTransformAlong B T) y := by
  let AT := geoTransformAlong A T
  let BT := geoTransformAlong B T
  have hE : AT.E = BT.E := E_geoTransformAlong_eq hL.wEquiv.1 T
  have hAT : ∀ i : Fin AT.E.length, y ∉ AT.E.get i := fun i => hoff _ (List.get_mem _ i)
  have hBT : ∀ i : Fin BT.E.length, y ∉ BT.E.get i := by
    intro i
    apply hoff
    rw [hE]
    exact List.get_mem _ i
  rw [nmOrd_eq_ordinaryTraceOrder_of_notMem AT hAT, nmOrd_eq_ordinaryTraceOrder_of_notMem BT hBT]
  exact normalized_order_along_local A B hA hB hN hL T hT y hy
end
end Hironaka.HironakaG1LocalOffBoundary
