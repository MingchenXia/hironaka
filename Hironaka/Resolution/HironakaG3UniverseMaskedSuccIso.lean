import Hironaka.Resolution.HironakaG3UniversePositiveParts
import Hironaka.Resolution.HironakaG3UniverseStepOneSuccIso
import Hironaka.Resolution.HironakaG3UniverseLiftRestrict
import Hironaka.Resolution.HironakaG3UniverseOpenLiftRecord
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.G3UniverseMaskedSuccIso
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms
 BlowupTowerIsomorphism MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec CanonicalCentres
 HironakaSmoothSubmersionCoefficientIdeals HironakaG3UniverseLiftManifold G3UniverseLiftedTower
 HironakaG3UniverseLiftedMarkedHistory HironakaG3UniverseMarkedDomain G3UniverseOpenDiffeo
 G3UniverseChartTowerTransport G3UniverseLiftRestrict G3UniverseOpenLiftRecord
 G3UniverseMaskCompanion G3UniverseStepOneSuccIso G3UniverseCanonicalIH NonmonomialOrderTail GeneralValue HomogenizedIdealAlong
noncomputable section

/-- At a canonical maximal-order companion tail, the literal restricted lifted tail has the same Step One at the supplied lower depth value. -/
theorem masked_succ_lift_then_iso {n k r : ℕ} (hn : 0 < n) (hIH : CanonicalLiftValueIH.{u} hn r) {X Y Z : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (T₀ : BlowupTower X Y)
    (hT₀ : IsGeoTestTower M T₀) (T₁ : BlowupTower Y Z) (o : ℕ)
    (hdom : IsInvDomain (r + 1) (compAt M o T₀))
    (hmax : IsMaximalOrderAlong (compAt M o T₀).N (compAt M o T₀).ideal (compAt M o T₀).d)
    (hcan : IsCanonical (compAt M o T₀) (Seq.StepOneValueMasked.stepOneInvM (invFamily.{0} hn r) (compAt M o T₀))
      (restrict (ordMask (geoTransformAlong M T₀) o) T₁)) :
    let e := (liftDiffeomorph.{u} Y).symm
    let U := ordMask (geoTransformAlong M T₀) o
    let U' := preimageOpens e U
    ∀ p : openPreimage (liftTower.{u} T₁) U',
      (liftDiffeomorph.{u} _).symm (lifted_restrictEndpoint T₁ U p) ∈
        (geoTransformAlong (compAt M o T₀) (restrict U T₁)).cosupp →
      Seq.StepOneValueMasked.stepOneInvM (invFamily.{u} hn r)
        (CompanionRebase.companionOf n
          (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U' → liftCMfd.{u} Y)
            (geoTransformAlong (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T₀))) o)
        (restrict U' (liftTower.{u} T₁)) p =
      Seq.StepOneValueMasked.stepOneInvM (invFamily.{0} hn r) (compAt M o T₀) (restrict U T₁)
        ((liftDiffeomorph.{u} _).symm (lifted_restrictEndpoint T₁ U p)) := by
  dsimp only
  intro p hp
  let e := (liftDiffeomorph.{u} Y).symm
  let U := ordMask (geoTransformAlong M T₀) o
  let U' := preimageOpens e U
  have hD := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T₀ hT₀
  have hc := (companion_lifted_mask hn Y (geoTransformAlong M T₀) hD o).2
  have hrec : CompanionRebase.companionOf n
      (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U' → liftCMfd.{u} Y)
        (geoTransformAlong (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T₀))) o =
      markedPullback (m := n) (baseLiftDiffeo e U)
        (markedPullback (m := n) (liftDiffeomorph.{u} (CMfd.of (n := n) U)).symm (compAt M o T₀)) := by
    rw [liftTower_geoTransformAlong M hM.isWellFormed T₀ hT₀]
    change _ = markedPullback (m := n) (baseLiftDiffeo e U)
      (markedPullback (m := n) (liftDiffeomorph.{u} (CMfd.of (n := n) U)).symm
        (CompanionRebase.companionOf n (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → Y) (geoTransformAlong M T₀)) o))
    rw [hc]
    exact openPullback_factors_lift e U _ hdom.isWellFormed.isCoherent
  rw [hrec]
  exact stepOne_succ_lift_then_iso hn hIH (compAt M o T₀) hdom hmax (restrict U T₁) hcan
    (baseLiftDiffeo e U) (restrict U' (liftTower.{u} T₁)) (lifted_restrictEndpoint T₁ U)
    (liftTower_restrict_isTowerIso U T₁) p hp
/-- The same comparison at a corresponding point on any literally equal lifted open. -/
theorem masked_succ_lift_then_iso_of_open_eq {n k r : ℕ} (hn : 0 < n) (hIH : CanonicalLiftValueIH.{u} hn r) {X Y Z : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (T₀ : BlowupTower X Y)
    (hT₀ : IsGeoTestTower M T₀) (T₁ : BlowupTower Y Z) (o : ℕ)
    (hdom : IsInvDomain (r + 1) (compAt M o T₀))
    (hmax : IsMaximalOrderAlong (compAt M o T₀).N (compAt M o T₀).ideal (compAt M o T₀).d)
    (hcan : IsCanonical (compAt M o T₀) (Seq.StepOneValueMasked.stepOneInvM (invFamily.{0} hn r) (compAt M o T₀))
      (restrict (ordMask (geoTransformAlong M T₀) o) T₁))
    (V : Opens (liftCMfd.{u} Y)) (hV : V = preimageOpens (liftDiffeomorph.{u} Y).symm (ordMask (geoTransformAlong M T₀) o))
    (y : Z) (hy : T₁.proj y ∈ ordMask (geoTransformAlong M T₀) o)
    (hyV : (liftTower.{u} T₁).proj ((liftDiffeomorph.{u} Z) y) ∈ V)
    (hcos : (⟨y,hy⟩ : openPreimage T₁ (ordMask (geoTransformAlong M T₀) o)) ∈
      (geoTransformAlong (compAt M o T₀) (restrict (ordMask (geoTransformAlong M T₀) o) T₁)).cosupp) :
      Seq.StepOneValueMasked.stepOneInvM (invFamily.{u} hn r)
        (CompanionRebase.companionOf n
          (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : V → liftCMfd.{u} Y)
            (geoTransformAlong (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T₀))) o)
        (restrict V (liftTower.{u} T₁)) ⟨(liftDiffeomorph.{u} Z) y,hyV⟩ =
      Seq.StepOneValueMasked.stepOneInvM (invFamily.{0} hn r) (compAt M o T₀) (restrict (ordMask (geoTransformAlong M T₀) o) T₁) ⟨y,hy⟩ := by
  subst V
  let U := ordMask (geoTransformAlong M T₀) o
  let p : openPreimage (liftTower.{u} T₁) (preimageOpens (liftDiffeomorph.{u} Y).symm U) :=
    ⟨(liftDiffeomorph.{u} Z) y,hyV⟩
  have hp : (liftDiffeomorph.{u} _).symm (lifted_restrictEndpoint T₁ U p) = (⟨y,hy⟩ : openPreimage T₁ U) := by
    apply Subtype.ext
    rfl
  have hv := masked_succ_lift_then_iso hn hIH M hM T₀ hT₀ T₁ o hdom hmax hcan p (by rw [hp]; exact hcos)
  rw [hp] at hv
  exact hv
end
end Hironaka.G3UniverseMaskedSuccIso
