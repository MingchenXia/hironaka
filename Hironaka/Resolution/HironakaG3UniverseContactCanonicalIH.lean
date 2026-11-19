import Hironaka.Resolution.HironakaG3UniverseCanonicalIH
import Hironaka.Resolution.HironakaG3UniverseContactTail
import Hironaka.Resolution.HironakaG3UniverseLiftThenIso
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.G3UniverseContactLowerIH
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal StepOneValue ResolutionInvariantSpec CanonicalCentres
  HironakaSmoothSubmersionCoefficientIdeals HironakaG3UniverseLiftManifold G3UniverseLiftedTower
  G3UniverseChartTowerTransport G3UniverseOpenDiffeo G3UniverseLiftRestrict
  G3UniverseContactTail G3UniverseLiftThenIso HironakaG3UniverseCanonicalValues ContactStageKept
  HironakaG3UniverseMarkedDomain G3UniverseCanonicalIH
noncomputable section

/-- Conditional lower induction transports an explicit-direction contact record and its actual restricted tail. -/
theorem contact_lower_canonical_and_values_of_canonical_IH {n r : ℕ} (hn : 0 < n) {X Y Z : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (T₀ : BlowupTower X Y)
    (hT₀ : IsGeoTestTower (barMarked M) T₀) (T₁ : BlowupTower Y Z) (w : X → ℂ) (W : Opens Y)
    (hD : IsInvDomain r (contactMarkedKept M w T₀ W))
    (hcan : IsCanonical (contactMarkedKept M w T₀ W) ((invFamily.{0} hn r).inv (contactMarkedKept M w T₀ W)) (restrict W T₁))
    (hIH : CanonicalLiftValueIH.{u} hn r) :
    let e := (liftDiffeomorph.{u} Y).symm
    let W' := preimageOpens e W
    let K' := contactMarkedKept (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)
      (w ∘ (liftDiffeomorph.{u} X).symm) (liftTower.{u} T₀) W'
    let Q := restrict W' (liftTower.{u} T₁)
    IsInvDomain r K' ∧ IsCanonical K' ((invFamily.{u} hn r).inv K') Q ∧
    ∀ p : openPreimage (liftTower.{u} T₁) W',
      (liftDiffeomorph.{u} _).symm (lifted_restrictEndpoint T₁ W p) ∈
        (geoTransformAlong (contactMarkedKept M w T₀ W) (restrict W T₁)).cosupp →
      (invFamily.{u} hn r).inv K' Q p = (invFamily.{0} hn r).inv (contactMarkedKept M w T₀ W) (restrict W T₁)
          ((liftDiffeomorph.{u} _).symm (lifted_restrictEndpoint T₁ W p)) := by
  let e := (liftDiffeomorph.{u} Y).symm
  let W' := preimageOpens e W
  have hg := contact_record_and_tail_lift M hM T₀ hT₀ T₁ w W
  have hprefix := prefix_values_of_canonical_IH hn hIH (contactMarkedKept M w T₀ W) hD (restrict W T₁) hcan
  have hfinal := hIH (contactMarkedKept M w T₀ W) hD (restrict W T₁) hcan
  have htest := (invFamily.{0} hn r).isInvValue.isGeoTestTower_of_isCanonical hD (restrict W T₁) hcan
  have hIH := canonical_and_values_of_lift_then_iso hn (contactMarkedKept M w T₀ W) hD (restrict W T₁) htest hcan hprefix hfinal
    (baseLiftDiffeo e W) (restrict W' (liftTower.{u} T₁)) (lifted_restrictEndpoint T₁ W) hg.2
  have hdomL := transported_markedPullback_domain (CMfd.of (n := n) W)
    (Homeomorph.ulift.symm : (CMfd.of (n := n) W) ≃ₜ ULift.{u} (CMfd.of (n := n) W))
    (contactMarkedKept M w T₀ W) hD
  have hdomQ := InvDomainTowerAlong.isInvDomain_pullback (baseLiftDiffeo e W) hdomL
  dsimp only
  rw [hg.1]
  exact ⟨hdomQ, hIH⟩
end
end Hironaka.G3UniverseContactLowerIH
