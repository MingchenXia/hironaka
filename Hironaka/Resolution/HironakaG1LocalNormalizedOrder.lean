import Hironaka.Resolution.HironakaG1MemberStageLocal
import Hironaka.Resolution.HironakaActualProjectedNormalizedOrderDetection
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators
namespace Hironaka.HironakaG1LocalNormalizedOrder
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  ResolutionInvariantSpec HironakaG8LocalHistory HironakaG8ProjEquiv
  HironakaCoherentTransformExtension InvDomainTowerAlong
  MarkedIdealEquivalence.MarkedIdeal HironakaActualProjectedNormalizedOrderDetection
  HironakaSharpOriginalProductTraceOrder

/-- Full local equivalence and same carrier propagate normalized ordinary
order to every actual common suffix, even with different native marks. -/
theorem normalized_order_along_local {n kA kB : ℕ} {X Y : CMfd.{0} n}
    (A B : MarkedIdeal n X) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hN : A.N = B.N) (hL : LocWPEquiv A B) (T : BlowupTower X Y) (hT : IsGeoTestTower A T)
    (y : Y) (hy : y ∈ (geoTransformAlong A T).cosupp) :
    (geoTransformAlong B T).d * ordinaryTraceOrder (geoTransformAlong A T).N (geoTransformAlong A T).ideal y =
      (geoTransformAlong A T).d * ordinaryTraceOrder (geoTransformAlong B T).N (geoTransformAlong B T).ideal y := by
  have hTB := (hL.wEquiv.2 T).1.mp hT
  have hAT := isInvDomain_geoTransformAlong hA T hT
  have hBT := isInvDomain_geoTransformAlong hB T hTB
  have hStage := hL.geoTransformAlong T hT
  have hNT := geoTransformAlong_N_eq_of_N_eq hN T
  have hET := E_geoTransformAlong_eq hL.wEquiv.1 T
  have hyB : y ∈ (geoTransformAlong B T).cosupp := ((hL.wEquiv.2 T).2 hT) ▸ hy
  exact (normalized_ordinary_order_of_projected_wEquiv _ _ hAT hBT y hy hyB hNT.symm hET.symm
    hStage.projEquiv.projectionTest_wEquiv).2.2
end
end Hironaka.HironakaG1LocalNormalizedOrder
