import Hironaka.Resolution.HironakaG3UniverseNonspecialZeroStepOneGeneral
import Hironaka.Resolution.HironakaG3UniverseHigherPositiveStepValueGeneric
import Hironaka.Resolution.HironakaG3UniverseStepOneSpecialActual
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.G3UniverseStepOneLocalBridgeGeneral
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal StepOneValue ResolutionInvariantSpec CanonicalCentres HomogenizedIdealAlong
  HironakaSmoothSubmersionCoefficientIdeals HironakaG3UniverseLiftManifold G3UniverseLiftedTower G3UniverseCanonicalIH
  G3UniverseStepOneSpecialActual G3UniverseNonspecialZeroStepOneGeneral G3UniverseHigherPositiveStepValueGeneric
noncomputable section

/-- Given lower-depth canonical-lift value agreement, actual Step One values agree along canonical original and lifted histories on the bar cosupport. -/
theorem stepOne_lifted_canonical_of_IH {n r : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain (r + 1) M)
    (hmax : IsMaximalOrderAlong M.N M.ideal M.d) (hIH : CanonicalLiftValueIH.{u} hn r) (T : BlowupTower X Y)
    (hcan : IsCanonical M (Seq.StepOneValueMasked.stepOneInvM (invFamily.{0} hn r) M) T)
    (hcanL : IsCanonical (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily.{u} hn r)
        (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)) (liftTower.{u} T))
    (y : Y) (hy : y ∈ (geoTransformAlong (barMarked M) T).cosupp) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily.{u} hn r)
      (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T) ((liftDiffeomorph.{u} Y) y) =
      Seq.StepOneValueMasked.stepOneInvM (invFamily.{0} hn r) M T y := by
  by_cases hs : IsSpecial M T y
  · have hT := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical (k := r + 1) (invFamily.{0} hn r) M hM hmax hn T hcan).1
    simpa only [Diffeomorph.symm_apply_apply] using
      stepOneInvM_lifted_special (r := r) hn M hM.isWellFormed T hT ((liftDiffeomorph.{u} Y) y) (by simpa only [Diffeomorph.symm_apply_apply] using hs)
  · by_cases hzero : level M T y = 0
    · exact stepOne_lifted_nonspecial_zero_of_IH hn M hM hmax hIH T hcan hcanL y hy hs hzero
    · exact stepOne_lifted_positive_level_of_IH hn M hM hmax hIH T hcan y hy hs (Nat.pos_of_ne_zero hzero)
end
end Hironaka.G3UniverseStepOneLocalBridgeGeneral
