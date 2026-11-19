import Hironaka.Resolution.HironakaG3UniverseCanonicalIH
import Hironaka.Resolution.HironakaG3UniverseMemberTail
import Hironaka.Resolution.HironakaG3UniverseLiftThenIso
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.G3UniverseMemberLowerIH
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal StepOneValue ResolutionInvariantSpec CanonicalCentres
  HironakaSmoothSubmersionCoefficientIdeals HironakaG3UniverseLiftManifold G3UniverseLiftedTower
  G3UniverseChartTowerTransport G3UniverseOpenDiffeo G3UniverseLiftRestrict
  G3UniverseMemberTail G3UniverseLiftThenIso HironakaG3UniverseCanonicalValues
  InvDomainMemberRestriction InvDomainRebase HironakaG3UniverseMarkedDomain G3UniverseCanonicalIH
noncomputable section

/-- The actual original positive-level lower member record. -/
def originalLowerMember {n : ℕ} {X Y : CMfd.{0} n} (M : MarkedIdeal n X)
    (T₀ : BlowupTower X Y) (y : liftCMfd.{u} Y) : MarkedIdeal n (CMfd.of (n := n)
      (maskA M T₀ ((liftDiffeomorph.{u} Y).symm y))) :=
  let e := (liftDiffeomorph.{u} Y).symm
  let A := maskA M T₀ (e y)
  let J := geoTransformAlong (barMarked M) T₀
  let K := memberRestrict J (membersThrough J.E (origMembers M T₀) (e y))
  MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : A → Y) K

/-- The corresponding actual lifted record on the literal inverse-image open. -/
def liftedLowerMember {n : ℕ} {X Y : CMfd.{0} n} (M : MarkedIdeal n X)
    (T₀ : BlowupTower X Y) (y : liftCMfd.{u} Y) : MarkedIdeal n (CMfd.of (n := n)
      (preimageOpens (liftDiffeomorph.{u} Y).symm (maskA M T₀ ((liftDiffeomorph.{u} Y).symm y)))) :=
  let e := (liftDiffeomorph.{u} Y).symm
  let A := maskA M T₀ (e y)
  let J' := geoTransformAlong (barMarked (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)) (liftTower.{u} T₀)
  let K' := memberRestrict J' (membersThrough J'.E
    (origMembers (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T₀)) y)
  MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : preimageOpens e A → liftCMfd.{u} Y) K'

/-- Conditional lower induction transports the actual member record and its restricted tail. -/
theorem member_lower_canonical_and_values_of_canonical_IH {n r : ℕ} (hn : 0 < n) {X Y Z : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (T₀ : BlowupTower X Y)
    (hT₀ : IsGeoTestTower (barMarked M) T₀) (T₁ : BlowupTower Y Z) (y : liftCMfd.{u} Y)
    (hD : IsInvDomain r (originalLowerMember M T₀ y))
    (hcan : IsCanonical (originalLowerMember M T₀ y) ((invFamily.{0} hn r).inv (originalLowerMember M T₀ y))
      (restrict (maskA M T₀ ((liftDiffeomorph.{u} Y).symm y)) T₁))
    (hIH : CanonicalLiftValueIH.{u} hn r) :
    let A := maskA M T₀ ((liftDiffeomorph.{u} Y).symm y)
    let A' := preimageOpens (liftDiffeomorph.{u} Y).symm A
    let Q := restrict A' (liftTower.{u} T₁)
    IsInvDomain r (liftedLowerMember M T₀ y) ∧
    IsCanonical (liftedLowerMember M T₀ y) ((invFamily.{u} hn r).inv (liftedLowerMember M T₀ y)) Q ∧
    ∀ p : openPreimage (liftTower.{u} T₁) A',
      (liftDiffeomorph.{u} _).symm (lifted_restrictEndpoint T₁ A p) ∈
        (geoTransformAlong (originalLowerMember M T₀ y) (restrict A T₁)).cosupp →
      (invFamily.{u} hn r).inv (liftedLowerMember M T₀ y) Q p =
        (invFamily.{0} hn r).inv (originalLowerMember M T₀ y) (restrict A T₁)
          ((liftDiffeomorph.{u} _).symm (lifted_restrictEndpoint T₁ A p)) := by
  let e := (liftDiffeomorph.{u} Y).symm
  let A := maskA M T₀ (e y)
  let A' := preimageOpens e A
  have hg := member_record_and_tail_lift hn M hM T₀ hT₀ T₁ y
  have hprefix := prefix_values_of_canonical_IH hn hIH (originalLowerMember M T₀ y) hD (restrict A T₁) hcan
  have hfinal := hIH (originalLowerMember M T₀ y) hD (restrict A T₁) hcan
  have htest := (invFamily.{0} hn r).isInvValue.isGeoTestTower_of_isCanonical hD (restrict A T₁) hcan
  have hIH := canonical_and_values_of_lift_then_iso hn (originalLowerMember M T₀ y) hD (restrict A T₁) htest hcan hprefix hfinal
    (baseLiftDiffeo e A) (restrict A' (liftTower.{u} T₁)) (lifted_restrictEndpoint T₁ A) hg.2.2
  have hdomL := transported_markedPullback_domain (CMfd.of (n := n) A)
    (Homeomorph.ulift.symm : (CMfd.of (n := n) A) ≃ₜ ULift.{u} (CMfd.of (n := n) A))
    (originalLowerMember M T₀ y) hD
  have hdomQ := InvDomainTowerAlong.isInvDomain_pullback (baseLiftDiffeo e A) hdomL
  have hrec : liftedLowerMember M T₀ y =
      markedPullback (m := n) (baseLiftDiffeo e A)
        (markedPullback (m := n) (liftDiffeomorph.{u} (CMfd.of (n := n) A)).symm (originalLowerMember M T₀ y)) := hg.2.1
  rw [hrec]
  exact ⟨hdomQ, hIH⟩
end
end Hironaka.G3UniverseMemberLowerIH
