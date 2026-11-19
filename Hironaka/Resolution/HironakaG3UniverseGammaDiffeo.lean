import Hironaka.Resolution.HironakaG3UniverseLiftedMarkedHistory
import Hironaka.MarkedIdeal.MarkedIdealOpenBiholomorphism
import Hironaka.Resolution.HironakaG3UniverseSubmersionConjugate
import Hironaka.Resolution.HironakaSmoothSubmersionRelativeMonomial
set_option autoImplicit false
open Set Function
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaG3UniverseGammaDiffeo
open Hironaka.HolomorphicIdealSheaves BlowupTowers MarkedIdeals
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionRelativeMonomial
  MonomialCaseAlong G3UniverseSubmersionConjugate Hironaka.BlowupSequences
  MarkedIdeals.MarkedIdeal HironakaG3UniverseLiftManifold G3UniverseLiftedTower
  HironakaG3UniverseLiftedMarkedHistory
noncomputable section

/-- Literal gamma is preserved by a cross-universe biholomorphism. -/
theorem gammaAlong_markedPullback_diffeo {n : ℕ} {X : CMfd.{u} n} {Y : CMfd.{v} n}
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (M : MarkedIdeal n X) (hM : M.ideal.IsCoherent) (y : Y) :
    gammaAlong n (markedPullback (m := n) e M).N (markedPullback (m := n) e M).ideal
      (markedPullback (m := n) e M).E M.d y = gammaAlong n M.N M.ideal M.E M.d (e y) := by
  exact gammaAlong_same_dimension_preimage_eq (diffeo_isSubmersion e) hM rfl M.N M.E M.d y

/-- The actual relative gamma values at a lifted test-tower endpoint agree. -/
theorem gammaAlong_liftTower {n : ℕ} {X Y : CMfd.{0} n} (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (y : liftCMfd.{u} Y) :
    let L := geoTransformAlong (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T)
    let R := geoTransformAlong M T
    gammaAlong n L.N L.ideal L.E L.d y =
      gammaAlong n R.N R.ideal R.E R.d ((liftDiffeomorph.{u} Y).symm y) := by
  dsimp only
  rw [liftTower_geoTransformAlong M hM T hT]
  have hwf := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM T hT
  exact gammaAlong_markedPullback_diffeo (liftDiffeomorph.{u} Y).symm _ hwf.isCoherent y
end
end Hironaka.HironakaG3UniverseGammaDiffeo
