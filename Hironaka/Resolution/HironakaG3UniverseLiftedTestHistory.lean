import Hironaka.Resolution.HironakaG3UniverseLiftedMarkedHistory
import Hironaka.Resolution.HironakaG3UniverseLiftedAdmissibility
set_option autoImplicit false
open Set Function
open scoped Manifold ContDiff
universe u
namespace Hironaka.HironakaG3UniverseLiftedTestHistory
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal HironakaSmoothSubmersionCoefficientIdeals
  HironakaG3UniverseLiftManifold G3UniverseLiftedTower HironakaG3UniverseLiftedMarkedHistory
  HironakaG3UniverseLiftedAdmissibility
noncomputable section

/-- Every supplied actual original test tower remains a test tower after the literal lift. -/
theorem liftTower_isGeoTestTower {n : ℕ} {X : CMfd.{0} n} (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) :
    {Y : CMfd.{0} n} → (T : BlowupTower X Y) → IsGeoTestTower M T →
    IsGeoTestTower (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T)
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hT => by
    refine ⟨liftTower_isGeoTestTower M hM T hT.1,?_⟩
    rw [liftTower_geoTransformAlong M hM T hT.1]
    have hwf := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM T hT.1
    exact lifted_admissibleCentre _ (geoTransformAlong M T) hwf.isCoherent C hT.2
end
end Hironaka.HironakaG3UniverseLiftedTestHistory

namespace Hironaka.HironakaG3UniverseLiftedTestHistory
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal HironakaSmoothSubmersionCoefficientIdeals
  HironakaG3UniverseLiftManifold G3UniverseLiftedTower HironakaG3UniverseLiftedMarkedHistory
  G3UniverseMarkedCosupport
noncomputable section

/-- A supplied actual resolving test tower remains resolving under its literal lift. -/
theorem liftTower_isGeoResolution {n : ℕ} {X Y : CMfd.{0} n} (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (T : BlowupTower X Y) (hT : IsGeoResolution M T) :
    IsGeoResolution (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T) := by
  refine ⟨liftTower_isGeoTestTower M hM T hT.1,?_⟩
  rw [liftTower_geoTransformAlong M hM T hT.1]
  have hwf := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM T hT.1
  rw [markedPullback_cosupp_diffeo (liftDiffeomorph.{u} Y).symm (geoTransformAlong M T) hwf.isCoherent, hT.2]
  exact preimage_empty
end
end Hironaka.HironakaG3UniverseLiftedTestHistory
