import Hironaka.Resolution.HironakaG8PowerCompanionStepSkeleton
import Hironaka.Resolution.HironakaG8PowerActualCompanionStep
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8PowerCompanionMasks
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism BlowupTowers BlowupTowerTransforms
  ResolutionInvariantSpec NonmonomialOrderLocal NonmonomialOrderTail CompanionRebase CompanionReductionAlong
  HironakaActualPowerBoundaryExponents HironakaG8PowerCompanionLocal
  HironakaG8PowerCompanionStepSkeleton HironakaG8PowerActualCompanionStep HironakaG8MemberLoci StepOneValue

/-- The literal positive-level Step 1 masks coincide for an original
companion and its positive whole-power recoding. -/
theorem maskA_power_companions {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M) {e o : ℕ} (he : 1 ≤ e) (ho : 1 ≤ o)
    (hb : ∀ x ∈ M.cosupp, x ∉ ordGe M (o+1))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (companionOf n M o) T) (y : Y) :
    maskA (companionOf n M o) T y = maskA (companionOf n (powerMarked M e) (e*o)) T y := by
  have hW := (locWPEquiv_companionOf_powerMarked hn M hM he ho hb).wEquiv
  have hOrig := origMembers_eq_of_E_eq hW.1 T
  have hl : ∀ z : Y, level (companionOf n M o) T z = level (companionOf n (powerMarked M e) (e*o)) T z :=
    fun z => (power_companion_step_skeleton hn M hM he ho hb T hT z).1
  have hs : ∀ z : Y, IsSpecial (companionOf n M o) T z ↔
      IsSpecial (companionOf n (powerMarked M e) (e*o)) T z :=
    fun z => (power_companion_step_skeleton hn M hM he ho hb T hT z).2
  unfold maskA
  congr 1
  apply congrArg interior
  ext z
  simp only [mem_ofPred_eq, hOrig, hl, hs]

/-- The positive-level lower masks agree, without assuming equality of the
independently chosen tangent-direction masks at level zero. -/
theorem lowerMask_succ_power_companions {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M) {e o : ℕ} (he : 1 ≤ e) (ho : 1 ≤ o)
    (hb : ∀ x ∈ M.cosupp, x ∉ ordGe M (o+1))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (companionOf n M o) T) (y : Y) (s : ℕ) :
    lowerMask (companionOf n M o) (s+1) T y =
      lowerMask (companionOf n (powerMarked M e) (e*o)) (s+1) T y :=
  maskA_power_companions hn M hM he ho hb T hT y

/-- The actual original and recoded masked companions have the same
positive-level lower open at every literal controlled companion prefix. -/
theorem lowerMask_succ_actual_masked_companions {n : ℕ} (hn : 0 < n) {X Y Z : CMfd.{0} n}
    {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M) {e o : ℕ} (he : 1 ≤ e) (ho : 1 ≤ o)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T) :
    let W := ordMask (geoTransformAlong M T) o
    let A := MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → Y) (geoTransformAlong M T)
    let B := MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → Y)
      (geoTransformAlong (powerMarked M e) T)
    ∀ (S : BlowupTower (CMfd.of (n := n) W) Z), IsGeoTestTower (companionOf n A o) S →
      ∀ (z : Z) (s : ℕ), lowerMask (companionOf n A o) (s+1) S z =
        lowerMask (companionOf n B (e*o)) (s+1) S z := by
  let W := ordMask (geoTransformAlong M T) o
  let A := MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → Y) (geoTransformAlong M T)
  let B := MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → Y)
    (geoTransformAlong (powerMarked M e) T)
  change ∀ (S : BlowupTower (CMfd.of (n := n) W) Z), IsGeoTestTower (companionOf n A o) S →
    ∀ (z : Z) (s : ℕ), lowerMask (companionOf n A o) (s+1) S z =
      lowerMask (companionOf n B (e*o)) (s+1) S z
  intro S hS z s
  have hW := (masked_companion_local_original_power_history hn M hM he ho T hT).wEquiv
  have hOrig := origMembers_eq_of_E_eq hW.1 S
  change origMembers (companionOf n A o) S = origMembers (companionOf n B (e*o)) S at hOrig
  have hl : ∀ x : Z, level (companionOf n A o) S x = level (companionOf n B (e*o)) S x :=
    fun x => (actual_masked_companion_step_skeleton hn M hM he ho T hT S hS x).1
  have hs : ∀ x : Z, IsSpecial (companionOf n A o) S x ↔ IsSpecial (companionOf n B (e*o)) S x :=
    fun x => (actual_masked_companion_step_skeleton hn M hM he ho T hT S hS x).2
  change maskA (companionOf n A o) S z = maskA (companionOf n B (e*o)) S z
  unfold maskA
  congr 1
  apply congrArg interior
  ext x
  simp only [mem_ofPred_eq, hOrig, hl, hs]

end
end Hironaka.HironakaG8PowerCompanionMasks
