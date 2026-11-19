import Hironaka.Resolution.HironakaG3UniverseStepOneSpecialActual
import Hironaka.Resolution.HironakaG3UniverseStrictAlong
import Hironaka.Resolution.HironakaG3UniverseRestrictedRecord
import Hironaka.Invariant.ContactStageKept
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.G3UniverseContactRecord
open Set Function TopologicalSpace Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal StepOneValue StepOneLowerDomain
  HironakaSmoothSubmersionCoefficientIdeals HironakaG3UniverseLiftManifold G3UniverseLiftedTower
  G3UniverseBarMarked G3UniverseStepOneSpecial G3UniverseStrictAlong G3UniverseRestrictedRecord
  G3UniverseOpenDiffeo HomogenizedIdealAlong ContactStageKept CoefficientIdealRestriction
open HomogenizedGlueingTower (strictAlong)
open MarkedIdealOperationsAlong.MarkedIdeal
open scoped Topology Manifold ContDiff
noncomputable section

/-- The actual restricted contact record for an explicitly transported function. -/
theorem contactMarkedKept_liftTower {n : ℕ} {X Y : CMfd.{0} n} (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked M) T)
    (w : X → ℂ) (W : Opens Y) :
    contactMarkedKept (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)
      (w ∘ (liftDiffeomorph.{u} X).symm) (liftTower.{u} T)
      (preimageOpens (liftDiffeomorph.{u} Y).symm W) =
    markedPullback (m := n) (preimageDiffeo (liftDiffeomorph.{u} Y).symm W).symm
      (contactMarkedKept M w T W) := by
  let eX := (liftDiffeomorph.{u} X).symm
  let eY := (liftDiffeomorph.{u} Y).symm
  let J := geoTransformAlong (barMarked M) T
  let J' := geoTransformAlong (barMarked (markedPullback (m := n) eX M)) (liftTower.{u} T)
  let S := strictAlong T (M.N ∩ {x | w x = 0})
  let S' := strictAlong (liftTower.{u} T) ((markedPullback (m := n) eX M).N ∩ {x | (w ∘ eX) x = 0})
  let K := withN (coeffMarkedAlong J) S
  let K' := withN (coeffMarkedAlong J') S'
  have hb := coeffHomMarked_pullback_diffeo eX M hM.isCoherent hM.isClosedSubmanifold_N
  have hj : J' = markedPullback (m := n) eY J := bar_history_of_base M hM T hT hb
  have hwf : J.IsWellFormed := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (StepOneLowerDomain.isWellFormed_barMarked M hM) T hT
  have hcoeff : coeffMarkedAlong J' = markedPullback (m := n) eY (coeffMarkedAlong J) := by
    rw [hj]
    exact (coeffMarked_pullback_diffeo eY J hwf.isCoherent hwf.isClosedSubmanifold_N).symm
  have hs : S' = eY ⁻¹' S := by
    dsimp [S',S]
    change strictAlong (liftTower.{u} T) (eX ⁻¹' (M.N ∩ {x | w x = 0})) = _
    exact strictAlong_liftTower (M.N ∩ {x | w x = 0}) T
  have hk : K' = markedPullback (m := n) eY K := by
    dsimp [K',K]
    rw [hcoeff]
    exact MarkedIdealOperationsTransform.MarkedIdeal.ext_of hs rfl rfl rfl
  have hc : K.ideal.IsCoherent := isCoherent_coeffMarkedAlong hwf.isCoherent hwf.isClosedSubmanifold_N
  change MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : preimageOpens eY W → liftCMfd.{u} Y) K' =
    markedPullback (m := n) (preimageDiffeo eY W).symm (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : W → Y) K)
  rw [hk]
  exact markedPullback_restrict_diffeo eY K hc W
end
end Hironaka.G3UniverseContactRecord

