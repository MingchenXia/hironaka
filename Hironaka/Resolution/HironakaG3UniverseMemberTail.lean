import Hironaka.Resolution.HironakaG3UniverseStepOneMemberRecord
import Hironaka.Resolution.HironakaG3UniverseOpenLiftRecord
import Hironaka.Resolution.HironakaG3UniverseLiftRestrict
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.G3UniverseMemberTail
open Set Function TopologicalSpace Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdeals MarkedIdeals.MarkedIdeal StepOneValue StepOneLowerDomain
  HironakaSmoothSubmersionCoefficientIdeals HironakaG3UniverseLiftManifold G3UniverseLiftedTower
  G3UniverseChartTowerTransport G3UniverseOpenDiffeo G3UniverseOpenLiftRecord G3UniverseLiftRestrict
  G3UniverseStepOneMemberRecord InvDomainMemberRestriction InvDomainRebase GermIdealPullbackCalculus
open scoped Topology Manifold ContDiff
noncomputable section

/-- Actual lower member record and physical restricted tail share one lifted base map. -/
theorem member_record_and_tail_lift {n : ℕ} (hn : 0 < n) {X Y Z : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (T₀ : BlowupTower X Y)
    (hT₀ : IsGeoTestTower (barMarked M) T₀) (T₁ : BlowupTower Y Z) (y : liftCMfd.{u} Y) :
    let e := (liftDiffeomorph.{u} Y).symm
    let A := maskA M T₀ (e y)
    let A' := preimageOpens e A
    let β := baseLiftDiffeo e A
    let J := geoTransformAlong (barMarked M) T₀
    let J' := geoTransformAlong (barMarked (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)) (liftTower.{u} T₀)
    let K := memberRestrict J (membersThrough J.E (origMembers M T₀) (e y))
    let K' := memberRestrict J' (membersThrough J'.E
      (origMembers (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T₀)) y)
    let R := MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : A → Y) K
    maskA (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T₀) y = A' ∧
    MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : A' → liftCMfd.{u} Y) K' =
      markedPullback (m := n) β (markedPullback (m := n) (liftDiffeomorph.{u} (CMfd.of (n := n) A)).symm R) ∧
    IsTowerIso β (restrict A' (liftTower.{u} T₁)) (liftTower.{u} (restrict A T₁))
      (lifted_restrictEndpoint T₁ A) := by
  let e := (liftDiffeomorph.{u} Y).symm
  let A := maskA M T₀ (e y)
  let J := geoTransformAlong (barMarked M) T₀
  let K := memberRestrict J (membersThrough J.E (origMembers M T₀) (e y))
  have hwf : J.IsWellFormed := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (StepOneLowerDomain.isWellFormed_barMarked M hM) T₀ hT₀
  have hc : K.ideal.IsCoherent := (isWellFormed_memberRestrict hn hwf _).isCoherent
  have hcR : (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : A → Y) K).ideal.IsCoherent := by
    exact isCoherent_pullback contMDiff_subtype_val hc
  have hrec := lowerMember_liftTower hn M hM T₀ hT₀ y
  refine ⟨hrec.1, ?_, liftTower_restrict_isTowerIso A T₁⟩
  rw [hrec.2]
  exact openPullback_factors_lift e A _ hcR
end
end Hironaka.G3UniverseMemberTail

