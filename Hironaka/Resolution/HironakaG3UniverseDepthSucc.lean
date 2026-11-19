import Hironaka.Resolution.HironakaG3UniverseMaskedSuccIso
import Hironaka.Resolution.HironakaG3UniverseMonomialLeaf
import Hironaka.Resolution.HironakaG3UniverseCanonicalIH
import Hironaka.Invariant.GeneralCanonicalTail
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.G3UniverseDepthSucc
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms
 BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec CanonicalCentres
 HironakaSmoothSubmersionCoefficientIdeals HironakaG3UniverseLiftManifold G3UniverseLiftedTower
 HironakaG3UniverseLiftedMarkedHistory HironakaG3UniverseMarkedDomain G3UniverseOpenDiffeo
 G3UniverseChartTowerTransport G3UniverseLiftRestrict G3UniverseMaskedSuccIso G3UniversePositiveInvariant
 HironakaG3UniverseMonomialLeaf HironakaG3UniverseOrderMask G3UniverseCanonicalIH
 HironakaG3UniverseCanonicalValues NonmonomialOrderTail NonmonomialOrderLocal
 NonmonomialOrderRegime GeneralValue StepOneRegime HomogenizedIdealAlong
noncomputable section

/-- The actual canonical companion data provides the lower-depth masked value comparison. -/
theorem masked_succ_of_lower_data {n r : ℕ} (hn : 0 < n) (hIH : CanonicalLiftValueIH.{u} hn r) {X Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain (r + 1) M) (T : BlowupTower X Y) (hT : IsGeoTestTower M T) (y : Y)
    (hdata : GenLowerData (fun {A} J {B} Q z => Seq.StepOneValueMasked.stepOneInvM (X := A) (invFamily.{0} hn r) J (Y := B) Q z)
      (r + 1) M (nmOrd (geoTransformAlong M T) y)
      (head T (regimeRun (OrdRegime M (nmOrd (geoTransformAlong M T) y)) T y))
      (tail T (regimeRun (OrdRegime M (nmOrd (geoTransformAlong M T) y)) T y)) y) :
    LiftedMaskedStepValuesAgree.{u} hn r M T y := by
  let o := nmOrd (geoTransformAlong M T) y
  let j := regimeRun (OrdRegime M o) T y
  let T₀ := head T j
  let T₁ := tail T j
  let U := ordMask (geoTransformAlong M T₀) o
  let e := (liftDiffeomorph.{u} (split T j).1).symm
  let U' := preimageOpens e U
  obtain ⟨hmem,hdom,hmax,hcan,hcos⟩ := hdata
  have hT₀ : IsGeoTestTower M T₀ := ((isGeoTestTower_iff_head_tail M T j).mp hT).1
  have hU : ordMask (geoTransformAlong (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T₀)) o = U' := by
    apply Opens.ext
    exact ordMask_lifted_test_endpoint hn M hM T₀ hT₀ o
  unfold LiftedMaskedStepValuesAgree
  dsimp only
  change ∀ (h₀ : T₁.proj y ∈ U) (hᵤ : (liftTower.{u} T₁).proj ((liftDiffeomorph.{u} Y) y) ∈
    ordMask (geoTransformAlong (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T₀)) o), _
  intro h₀ hᵤ
  exact masked_succ_lift_then_iso_of_open_eq hn hIH M hM T₀ hT₀ T₁ o hdom hmax hcan
    (ordMask (geoTransformAlong (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M) (liftTower.{u} T₀)) o)
    hU y h₀ hᵤ (by simpa only using hcos)

/-- At every actual canonical cosupport point the successor-depth invariant has the same value on literal lift. -/
theorem invFamily_succ_lifted_canonical {n r : ℕ} (hn : 0 < n) (hIH : CanonicalLiftValueIH.{u} hn r) {X Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain (r + 1) M) (T : BlowupTower X Y)
    (hcan : IsCanonical M ((invFamily.{0} hn (r + 1)).inv M) T) (y : Y)
    (hy : y ∈ (geoTransformAlong M T).cosupp) :
    (invFamily.{u} hn (r + 1)).inv (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)
      (liftTower.{u} T) ((liftDiffeomorph.{u} Y) y) = (invFamily.{0} hn (r + 1)).inv M T y := by
  have hT := (invFamily.{0} hn (r + 1)).isInvValue.isGeoTestTower_of_isCanonical hM T hcan
  by_cases hzero : nmOrd (geoTransformAlong M T) y = 0
  · simpa only [Diffeomorph.symm_apply_apply] using
      invFamily_succ_lifted_zero_nmOrd (r := r) hn M hM T hT ((liftDiffeomorph.{u} Y) y) (by simpa only [Diffeomorph.symm_apply_apply] using hzero)
  · have hgen : IsCanonical M (genInv (fun {A} J {B} Q z => Seq.StepOneValueMasked.stepOneInvM
        (X := A) (invFamily.{0} hn r) J (Y := B) Q z) M) T := by
      exact hcan
    have hdata := GeneralCanonicalTail.hasGenLowerData_of_isCanonical
      (fun {A} J {B} Q z => Seq.StepOneValueMasked.stepOneInvM (X := A) (invFamily.{0} hn r) J (Y := B) Q z)
      (StepOneSeq.isMaxOrderValue_stepOneInvM (k := r + 1) (invFamily.{0} hn r) hn) hn hM T hT hgen
    have hmasked := masked_succ_of_lower_data hn hIH M hM T hT y (hdata y hy _ rfl (Nat.one_le_iff_ne_zero.mpr hzero))
    exact invFamily_succ_lifted_positive_of_masked_values (r := r) hn M hM T hT y hzero hmasked

/-- The canonical-history induction hypothesis is proved at the successor depth. -/
theorem canonicalLiftValueIH_succ {n r : ℕ} (hn : 0 < n) (hIH : CanonicalLiftValueIH.{u} hn r) : CanonicalLiftValueIH.{u} hn (r + 1) := by
  intro X Y M hM T hcan z hz
  have h := invFamily_succ_lifted_canonical hn hIH M hM T hcan ((liftDiffeomorph.{u} Y).symm z) hz
  rw [(liftDiffeomorph.{u} Y).apply_symm_apply z] at h
  exact h

/-- An actual successor-depth canonical tower remains canonical under its literal universe lift. -/
theorem liftTower_isCanonical_succ {n r : ℕ} (hn : 0 < n) (hIH : CanonicalLiftValueIH.{u} hn r) {X Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain (r + 1) M) (T : BlowupTower X Y)
    (hcan : IsCanonical M ((invFamily.{0} hn (r + 1)).inv M) T) :
    IsCanonical (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)
      ((invFamily.{u} hn (r + 1)).inv (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M))
      (liftTower.{u} T) := by
  have hT := (invFamily.{0} hn (r + 1)).isInvValue.isGeoTestTower_of_isCanonical hM T hcan
  exact liftTower_isCanonical_of_values hn M hM.isWellFormed T hT hcan
    (prefix_values_of_canonical_IH hn (canonicalLiftValueIH_succ hn hIH) M hM T hcan)

/-- Canonical-history values lift at every recursive depth. -/
theorem canonicalLiftValueIH_all {n : ℕ} (hn : 0 < n) : ∀ r : ℕ, CanonicalLiftValueIH.{u} hn r
  | 0 => by
    intro M hM T hcan z hz
    rfl
  | r + 1 => canonicalLiftValueIH_succ hn (canonicalLiftValueIH_all hn r)

/-- Corresponding points on any supplied canonical history have equal recursive values. -/
theorem invFamily_lifted_canonical_all {n r : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain r M) (T : BlowupTower X Y)
    (hcan : IsCanonical M ((invFamily.{0} hn r).inv M) T) (y : Y)
    (hy : y ∈ (geoTransformAlong M T).cosupp) :
    (invFamily.{u} hn r).inv (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)
      (liftTower.{u} T) ((liftDiffeomorph.{u} Y) y) = (invFamily.{0} hn r).inv M T y := by
  have h := canonicalLiftValueIH_all.{u} hn r M hM T hcan ((liftDiffeomorph.{u} Y) y) (by simpa using hy)
  simpa using h

/-- Every supplied recursive canonical history remains canonical under literal lift. -/
theorem liftTower_isCanonical_all {n r : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain r M) (T : BlowupTower X Y)
    (hcan : IsCanonical M ((invFamily.{0} hn r).inv M) T) :
    IsCanonical (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M)
      ((invFamily.{u} hn r).inv (markedPullback (m := n) (liftDiffeomorph.{u} X).symm M))
      (liftTower.{u} T) := by
  have hT := (invFamily.{0} hn r).isInvValue.isGeoTestTower_of_isCanonical hM T hcan
  exact liftTower_isCanonical_of_values hn M hM.isWellFormed T hT hcan
    (prefix_values_of_canonical_IH hn (canonicalLiftValueIH_all hn r) M hM T hcan)

end
end Hironaka.G3UniverseDepthSucc
