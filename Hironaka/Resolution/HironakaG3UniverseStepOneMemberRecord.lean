import Hironaka.Resolution.HironakaG3UniverseMemberRestrict
import Hironaka.Resolution.HironakaG3UniverseRestrictedRecord
import Hironaka.Resolution.HironakaG3UniverseStepOneSpecialActual
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.G3UniverseStepOneMemberRecord
open Set Function TopologicalSpace Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal StepOneValue StepOneLowerDomain
  HironakaSmoothSubmersionCoefficientIdeals HironakaG3UniverseLiftManifold G3UniverseLiftedTower
  G3UniverseBarMarked G3UniverseStepOneSpecial G3UniverseStepOneSpecialActual G3UniverseStepOneLevel
  G3UniverseOpenDiffeo G3UniverseMemberRestrict G3UniverseRestrictedRecord InvDomainMemberRestriction
  InvDomainRebase
open scoped Topology Manifold ContDiff
noncomputable section

/-- Actual positive-level mask and restricted lower member record on that same literal open. -/
theorem lowerMember_liftTower {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n} (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked M) T)
    (y : liftCMfd.{u} Y) :
    let e := (liftDiffeomorph.{u} Y).symm
    let A := maskA M T (e y)
    let J := geoTransformAlong (barMarked M) T
    let J' := geoTransformAlong (barMarked (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)) (liftTower.{u} T)
    let K := memberRestrict J (membersThrough J.E (origMembers M T) (e y))
    let K' := memberRestrict J' (membersThrough J'.E
      (origMembers (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T)) y)
    maskA (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T) y = preimageOpens e A ∧
    MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : preimageOpens e A → liftCMfd.{u} Y) K' =
      markedPullback (m := n) (preimageDiffeo e A).symm
        (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : A → Y) K) := by
  let e := (liftDiffeomorph.{u} Y).symm
  let A := maskA M T (e y)
  let J := geoTransformAlong (barMarked M) T
  let J' := geoTransformAlong (barMarked (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)) (liftTower.{u} T)
  let K := memberRestrict J (membersThrough J.E (origMembers M T) (e y))
  let K' := memberRestrict J' (membersThrough J'.E
      (origMembers (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T)) y)
  have hbar := coeffHomMarked_pullback_diffeo (liftDiffeomorph.{u} X).symm M hM.isCoherent hM.isClosedSubmanifold_N
  have hj : J' = markedPullback (m := n) e J := bar_history_of_base M hM T hT hbar
  have hE := origMembers_liftTower_barTest M hM T hT
  have hwf : J.IsWellFormed := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (StepOneLowerDomain.isWellFormed_barMarked M hM) T hT
  have hd : 1 ≤ J.d := by
    dsimp [J]
    rw [d_geoTransformAlong]
    exact ContactIndependenceAlong.one_le_coeffMarkedAlong_d _
  have hk : K' = markedPullback (m := n) e K := by
    dsimp [K',K]
    rw [hj,hE]
    exact (pullback_diffeo_memberRestrict_membersThrough e hwf hd (origMembers M T) y).symm
  have hc : K.ideal.IsCoherent := (isWellFormed_memberRestrict hn hwf _).isCoherent
  constructor
  · exact maskA_liftTower M hM T hT y
  · change MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : preimageOpens e A → liftCMfd.{u} Y) K' = _
    rw [hk]
    exact markedPullback_restrict_diffeo e K hc A
end
end Hironaka.G3UniverseStepOneMemberRecord

