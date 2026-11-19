import Hironaka.Resolution.HironakaActualOldDivisorExponentTransport
import Hironaka.Invariant.MemberInterTowerAlong

set_option autoImplicit false

/-! An actual old boundary exponent persists along its literal strict trace
through an arbitrary subsequent test tower. -/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG11OldBoundaryExponentHistory
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal DivisorExponentAlong MemberInterTowerAlong
  ResolutionInvariantSpec HironakaActualOldDivisorExponentTransport

/-- At every point of the transformed carrier and strict old member, the
exponent is that at its projection before the test history. -/
theorem old_exponent_along_test_history
    {n : ℕ} {X Y : CMfd.{0} n} (M : MarkedIdeal n X) {k : ℕ}
    (hM : IsInvDomain k M) (i : Fin M.E.length)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T) {y : Y}
    (hyN : y ∈ (geoTransformAlong M T).N)
    (hyD : y ∈ strictAlong T (M.E.get i)) :
    divExpAlong n (geoTransformAlong M T).N (geoTransformAlong M T).ideal
      (strictAlong T (M.E.get i)) y = divExpAlong n M.N M.ideal (M.E.get i) (T.proj y) := by
  induction T with
  | refl => simp [geoTransformAlong,strictAlong] 
  | @step Z W T C π hπ ih =>
    have hprev := hT.1
    have hC := hT.2
    let j : Fin (geoTransformAlong M T).E.length :=
      Fin.castLE (length_E_le_length_E_geoTransformAlong M T) i
    have hj : (geoTransformAlong M T).E.get j = strictAlong T (M.E.get i) :=
      get_E_geoTransformAlong M T i
    have hNprev : π y ∈ (geoTransformAlong M T).N := by
      apply geoStrictTransform_subset_preimage hπ.contMDiff.continuous
        (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM.isWellFormed T hprev).isClosedSubmanifold_N.1
      exact hyN
    have hDprev : π y ∈ strictAlong T (M.E.get i) := by
      apply geoStrictTransform_subset_preimage hπ.contMDiff.continuous (isClosed_strictAlong T
        (hM.isWellFormed.isSNCDivisor.1 _ (List.get_mem _ _)))
      exact hyD
    change y ∈ geoStrictTransform π C (strictAlong T (M.E.get i)) at hyD
    have hstep := original_history_old_exponent M hM T hprev hC hπ j hyN (by simpa only [hj] using hyD)
    rw [hj] at hstep
    exact hstep.trans (ih hprev hNprev hDprev)

end Hironaka.HironakaG11OldBoundaryExponentHistory
