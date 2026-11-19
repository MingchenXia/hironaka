import Hironaka.Resolution.HironakaG3UniverseContactRecord
import Hironaka.Resolution.HironakaG3UniverseOpenLiftRecord
import Hironaka.Resolution.HironakaG3UniverseLiftRestrict
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.G3UniverseContactTail
open Set Function TopologicalSpace Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdeals MarkedIdeals.MarkedIdeal StepOneValue StepOneLowerDomain
  HironakaSmoothSubmersionCoefficientIdeals HironakaG3UniverseLiftManifold G3UniverseLiftedTower
  G3UniverseChartTowerTransport G3UniverseOpenDiffeo G3UniverseOpenLiftRecord G3UniverseLiftRestrict
  G3UniverseContactRecord ContactStageKept GermIdealPullbackCalculus
open scoped Topology Manifold ContDiff
noncomputable section

/-- Actual contact record and physical restricted tail share one lifted base map. -/
theorem contact_record_and_tail_lift {n : ℕ} {X Y Z : CMfd.{0} n} (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (T₀ : BlowupTower X Y) (hT₀ : IsGeoTestTower (barMarked M) T₀)
    (T₁ : BlowupTower Y Z) (w : X → ℂ) (W : Opens Y) :
    let e := (liftDiffeomorph.{u} Y).symm
    let W' := preimageOpens e W
    let β := baseLiftDiffeo e W
    let K := contactMarkedKept M w T₀ W
    contactMarkedKept (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)
      (w ∘ (liftDiffeomorph.{u} X).symm) (liftTower.{u} T₀) W' =
      markedPullback (m := n) β (markedPullback (m := n) (liftDiffeomorph.{u} (CMfd.of (n := n) W)).symm K) ∧
    IsTowerIso β (restrict W' (liftTower.{u} T₁)) (liftTower.{u} (restrict W T₁))
      (lifted_restrictEndpoint T₁ W) := by
  have hc : (contactMarkedKept M w T₀ W).ideal.IsCoherent := by
    change (GermIdeal.pullback (m := n) (Subtype.val : W → Y) _).IsCoherent
    exact isCoherent_pullback contMDiff_subtype_val (isCoherent_restrictedCoeff M hM.isCoherent hM.isClosedSubmanifold_N w T₀ hT₀)
  constructor
  · rw [contactMarkedKept_liftTower M hM T₀ hT₀ w W]
    exact openPullback_factors_lift (liftDiffeomorph.{u} Y).symm W (contactMarkedKept M w T₀ W) hc
  · exact liftTower_restrict_isTowerIso W T₁
end
end Hironaka.G3UniverseContactTail

