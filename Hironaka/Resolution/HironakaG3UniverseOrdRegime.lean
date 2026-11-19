import Hironaka.Resolution.HironakaG3UniverseNonmonomialOrder
import Hironaka.Resolution.HironakaG3UniverseLiftedTestHistory
import Hironaka.Invariant.NonmonomialOrderRegime
set_option autoImplicit false
open Set Function
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG3UniverseOrdRegime
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec
  HironakaSmoothSubmersionCoefficientIdeals HironakaG3UniverseLiftManifold G3UniverseLiftedTower
  HironakaG3UniverseLiftedMarkedHistory HironakaG3UniverseLiftedNmOrd G3UniverseMarkedCosupport
  NonmonomialOrderRegime StepOneRegime
noncomputable section

/-- The actual order regime is preserved at a lifted test-tower endpoint. -/
theorem ordRegime_liftTower_iff {n k : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (o : ℕ) (y : liftCMfd.{u} Y) :
    OrdRegime (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) o (liftTower.{u} T) y ↔
      OrdRegime M o T ((liftDiffeomorph.{u} Y).symm y) := by
  change (y ∈ (geoTransformAlong (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)
    (liftTower.{u} T)).cosupp ∧ _ = _) ↔ _
  have hwf := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM.isWellFormed T hT
  rw [liftTower_geoTransformAlong M hM.isWellFormed T hT,
    markedPullback_cosupp_diffeo (liftDiffeomorph.{u} Y).symm _ hwf.isCoherent]
  rw [← liftTower_geoTransformAlong M hM.isWellFormed T hT,
    nmOrd_lifted_test_endpoint hn M hM T hT y]
  rfl

/-- The actual numeric order-regime run is preserved along a literal lifted test tower. -/
theorem regimeRun_ordRegime_liftTower {n k : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (o : ℕ) :
    {Y : CMfd.{0} n} → (T : BlowupTower X Y) → IsGeoTestTower M T → ∀ y : liftCMfd.{u} Y,
      regimeRun (OrdRegime (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) o) (liftTower.{u} T) y =
        regimeRun (OrdRegime M o) T ((liftDiffeomorph.{u} Y).symm y)
  | _, .refl, _, _ => rfl
  | _, .step T C π hπ, hT, y => by
    classical
    let z := (liftDiffeomorph.{u} _) (π ((liftDiffeomorph.{u} _).symm y))
    have hreg := ordRegime_liftTower_iff hn M hM T hT.1 o z
    have hr := regimeRun_ordRegime_liftTower hn M hM o T hT.1 z
    simp only [liftTower, regimeRun_step]
    change (if OrdRegime (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) o (liftTower.{u} T) z then
      regimeRun (OrdRegime (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) o) (liftTower.{u} T) z + 1 else 0) = _
    simpa only [z, Diffeomorph.symm_apply_apply] using (show
      (if OrdRegime (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) o (liftTower.{u} T) z then
        regimeRun (OrdRegime (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) o) (liftTower.{u} T) z + 1 else 0) =
      (if OrdRegime M o T ((liftDiffeomorph.{u} _).symm z) then
        regimeRun (OrdRegime M o) T ((liftDiffeomorph.{u} _).symm z) + 1 else 0) from by rw [hreg,hr])
end
end Hironaka.HironakaG3UniverseOrdRegime
