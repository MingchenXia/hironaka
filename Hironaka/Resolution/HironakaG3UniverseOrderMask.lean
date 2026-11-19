import Hironaka.Resolution.HironakaG3UniverseNonmonomialOrder
import Hironaka.Resolution.HironakaG3UniverseMarkedDomain
import Hironaka.Invariant.NonmonomialOrderTail
set_option autoImplicit false
open Set Function
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG3UniverseOrderMask
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec HironakaSmoothSubmersionCoefficientIdeals
  HironakaG3UniverseLiftManifold HironakaG3UniverseMarkedDomain HironakaG3UniverseLiftedNmOrd
  G3UniverseLiftedTower HironakaG3UniverseLiftedMarkedHistory NonmonomialOrderLocal NonmonomialOrderTail
noncomputable section

/-- The literal order-mask open of a domain record is the inverse image under the universe lift. -/
theorem ordMask_lifted_record {n k : ℕ} (hn : 0 < n) (X : CMfd.{0} n)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (o : ℕ) :
    (ordMask (M := liftCMfd.{u} X) (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) o : Set (liftCMfd.{u} X)) =
      (liftDiffeomorph.{u} X).symm ⁻¹' (ordMask M o : Set X) := by
  have hL : IsInvDomain k (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) :=
    transported_markedPullback_domain X (Homeomorph.ulift.symm : X ≃ₜ ULift.{u} X) M hM
  ext y
  change y ∈ ordMask (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) o ↔
    (liftDiffeomorph.{u} X).symm y ∈ ordMask M o
  rw [mem_ordMask_iff hn hL.isWellFormed hL.isNonzeroAlongAt,
    mem_ordMask_iff hn hM.isWellFormed hM.isNonzeroAlongAt]
  by_cases hy : (liftDiffeomorph.{u} X).symm y ∈ M.N
  · have hyL : y ∈ (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M).N := hy
    rw [mem_ordGe_iff hL.isWellFormed hL.isNonzeroAlongAt hyL,
      mem_ordGe_iff hM.isWellFormed hM.isNonzeroAlongAt hy,
      nmOrd_lifted_record hn X M hM y]
  · have hyL : y ∉ (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M).N := hy
    have hnotL : y ∉ ordGe (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (o+1) :=
      fun h => hyL (ordGe_subset_N _ _ h)
    have hnotR : (liftDiffeomorph.{u} X).symm y ∉ ordGe M (o+1) :=
      fun h => hy (ordGe_subset_N _ _ h)
    exact iff_of_true hnotL hnotR

/-- The literal order mask at a lifted actual test endpoint is the corresponding inverse image. -/
theorem ordMask_lifted_test_endpoint {n k : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (T : BlowupTower X Y) (hT : IsGeoTestTower M T) (o : ℕ) :
    (ordMask (geoTransformAlong (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T)) o : Set (liftCMfd.{u} Y)) =
      (liftDiffeomorph.{u} Y).symm ⁻¹' (ordMask (geoTransformAlong M T) o : Set Y) := by
  rw [liftTower_geoTransformAlong M hM.isWellFormed T hT]
  exact ordMask_lifted_record hn Y _ (InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT) o
end
end Hironaka.HironakaG3UniverseOrderMask
