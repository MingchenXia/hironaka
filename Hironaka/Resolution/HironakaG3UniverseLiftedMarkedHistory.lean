import Hironaka.Resolution.HironakaG3UniverseMarkedEndpointTransform
import Hironaka.Resolution.HironakaG3UniverseLiftedTower
import Hironaka.MarkedIdeal.MarkedIdealOpenBiholomorphism
import Hironaka.MarkedIdeal.HadamardBridgeAlong
set_option autoImplicit false
open Set Function
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG3UniverseLiftedMarkedHistory
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal HironakaSmoothSubmersionCoefficientIdeals
  HironakaG3UniverseLiftManifold G3UniverseLiftedTower HironakaG3UniverseMarkedStageTransform
noncomputable section

/-- The actual transformed marked record of a lifted test tower is its literal pullback. -/
theorem liftTower_geoTransformAlong {n : ℕ} {X : CMfd.{0} n} (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) :
    {Y : CMfd.{0} n} → (T : BlowupTower X Y) → IsGeoTestTower M T →
    geoTransformAlong (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T) =
      markedPullback (m := n) (liftDiffeomorph.{u} Y).symm (geoTransformAlong M T)
  | _, .refl, _ => rfl
  | _, .step T C π hπ, hT => by
    have hwf := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM T hT.1
    have hc := HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre
      hwf.isClosedSubmanifold_N hwf.isCoherent hT.2 hπ
    have hC := VanishingIdealCoherent.isCoherent_vanishingIdeal hπ.1
    change (geoTransformAlong (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)
      (liftTower.{u} T)).geoTransform ((liftDiffeomorph.{u} _).symm ⁻¹' C)
        ((liftDiffeomorph.{u} _) ∘ π ∘ (liftDiffeomorph.{u} _).symm) = _
    rw [liftTower_geoTransformAlong M hM T hT.1]
    exact geoTransform_conjugate_diffeos (liftDiffeomorph.{u} _).symm
      (liftDiffeomorph.{u} _).symm (geoTransformAlong M T) hwf.isCoherent C hC hπ.contMDiff hc
end
end Hironaka.HironakaG3UniverseLiftedMarkedHistory
