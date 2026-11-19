import Hironaka.Resolution.HironakaG3UniverseNonmonomialOrder
import Hironaka.Resolution.HironakaG3UniverseGammaDiffeo
import Hironaka.Invariant.CanonicalCentres
set_option autoImplicit false
open Set Function
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG3UniverseMonomialLeaf
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec CanonicalCentres
  HironakaSmoothSubmersionCoefficientIdeals HironakaG3UniverseLiftManifold
  G3UniverseLiftedTower HironakaG3UniverseLiftedNmOrd HironakaG3UniverseGammaDiffeo NonmonomialOrderLocal
noncomputable section

/-- At a zero-nonmonomial-order point, actual positive-depth invariant values agree under the literal lift. -/
theorem invFamily_succ_lifted_zero_nmOrd {n k r : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (y : liftCMfd.{u} Y) (hzero : nmOrd (M := Y) (geoTransformAlong M T) ((liftDiffeomorph.{u} Y).symm y) = 0) :
    (invFamily.{u} hn (r+1)).inv (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)
      (liftTower.{u} T) y =
    (invFamily.{0} hn (r+1)).inv M T ((liftDiffeomorph.{u} Y).symm y) := by
  have hord := nmOrd_lifted_test_endpoint hn M hM T hT y
  have hzero' : nmOrd (M := liftCMfd.{u} Y)
      (geoTransformAlong (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T)) y = 0 :=
    hord.trans hzero
  have hgamma := gammaAlong_liftTower M hM.isWellFormed T hT y
  simp only [invFamily_succ, generalStep_inv, GeneralValue.genInv, GeneralValue.genSecond,
    hzero',hzero,if_pos,hgamma]
  rfl
end
end Hironaka.HironakaG3UniverseMonomialLeaf
