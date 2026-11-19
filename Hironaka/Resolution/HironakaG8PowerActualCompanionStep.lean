import Hironaka.Resolution.HironakaG8PowerCompanionLocal
import Hironaka.Resolution.HironakaG8MemberLoci
import Hironaka.Invariant.StepOneSeq
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8PowerActualCompanionStep
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism BlowupTowers BlowupTowerTransforms
  ResolutionInvariantSpec NonmonomialOrderLocal NonmonomialOrderTail CompanionRebase CompanionReductionAlong
  HironakaActualPowerBoundaryExponents HironakaActualOriginalPowerTransform
  HironakaG8PowerCompanionLocal HironakaG8MemberLoci HironakaG11InvBMClass StepOneValue StepOneRegime

/-- Actual original and recoded masked companions have matching native Step 1
levels and special loci along each controlled companion suffix. -/
theorem actual_masked_companion_step_skeleton {n : ℕ} (hn : 0 < n) {X Y Z : CMfd.{0} n}
    {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M) {e o : ℕ} (he : 1 ≤ e) (ho : 1 ≤ o)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T) :
    let W := ordMask (geoTransformAlong M T) o
    let A := MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → Y) (geoTransformAlong M T)
    let B := MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → Y)
      (geoTransformAlong (powerMarked M e) T)
    ∀ (S : BlowupTower (CMfd.of (n := n) W) Z), IsGeoTestTower (companionOf n A o) S → ∀ z : Z,
      level (companionOf n A o) S z = level (companionOf n B (e*o)) S z ∧
      (IsSpecial (companionOf n A o) S z ↔ IsSpecial (companionOf n B (e*o)) S z) := by
  let W := ordMask (geoTransformAlong M T) o
  let A := MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → Y) (geoTransformAlong M T)
  let B := MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → Y)
    (geoTransformAlong (powerMarked M e) T)
  have hC := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT
  obtain ⟨hPT,hEq⟩ := original_power_transform M hM e he T hT
  have hP := InvDomainTowerAlong.isInvDomain_geoTransformAlong (powerMarked_isInvDomain M hM he) T hPT
  have hA := InvDomainTowerAlong.isInvDomain_pullback_val W hC
  have hB := InvDomainTowerAlong.isInvDomain_pullback_val W hP
  have hCompA := InvDomainCompanion.isInvDomain_companionAlong (X := CMfd.of (n := n) W) hn hA ho
  have hCompB := InvDomainCompanion.isInvDomain_companionAlong (X := CMfd.of (n := n) W) hn hB (Nat.mul_pos he ho)
  have hL := masked_companion_local_original_power_history hn M hM he ho T hT
  have hW := hL.wEquiv
  have hN : A.N = B.N := by
    change (Subtype.val : W → Y) ⁻¹' (geoTransformAlong M T).N =
      (Subtype.val : W → Y) ⁻¹' (geoTransformAlong (powerMarked M e) T).N
    rw [hEq.N_eq]
    rfl
  have hdim : SameCarrierDim (companionOf n A o) (companionOf n B (e*o)) := by
    apply SameCarrierDim.of_N_eq
    simp only [companionOf, companionAlong_N, hN]
  change ∀ (S : BlowupTower (CMfd.of (n := n) W) Z), IsGeoTestTower (companionOf n A o) S → ∀ z : Z,
    level (companionOf n A o) S z = level (companionOf n B (e*o)) S z ∧
      (IsSpecial (companionOf n A o) S z ↔ IsSpecial (companionOf n B (e*o)) S z)
  intro S hS z
  exact ⟨level_eq_of_E_eq hW.1 S z, isSpecial_iff_of_wEquiv hn hCompA hCompB hW hdim S hS z⟩


/-- The actual masked companions have the same native Step 1 run index along
any literal controlled companion suffix. -/
theorem actual_masked_companion_step_run {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M) {e o : ℕ} (he : 1 ≤ e) (ho : 1 ≤ o)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T) (s : ℕ) :
    let W := ordMask (geoTransformAlong M T) o
    let A := MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → Y) (geoTransformAlong M T)
    let B := MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → Y)
      (geoTransformAlong (powerMarked M e) T)
    ∀ {Z : CMfd.{0} n} (S : BlowupTower (CMfd.of (n := n) W) Z),
      IsGeoTestTower (companionOf n A o) S → ∀ z : Z,
      regimeRun (stepRegime (companionOf n A o) s) S z =
        regimeRun (stepRegime (companionOf n B (e*o)) s) S z := by
  let W := ordMask (geoTransformAlong M T) o
  let A := MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → Y) (geoTransformAlong M T)
  let B := MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → Y)
    (geoTransformAlong (powerMarked M e) T)
  change ∀ {Z : CMfd.{0} n} (S : BlowupTower (CMfd.of (n := n) W) Z),
    IsGeoTestTower (companionOf n A o) S → ∀ z : Z,
      regimeRun (stepRegime (companionOf n A o) s) S z =
        regimeRun (stepRegime (companionOf n B (e*o)) s) S z
  intro Z S
  induction S with
  | refl => intro _ _; rfl
  | step S C π hπ ih =>
    intro hS z
    have hST := ((isGeoTestTower_step_iff (companionOf n A o) S C π hπ).mp hS).1
    obtain ⟨hl,hsp⟩ := actual_masked_companion_step_skeleton hn M hM he ho T hT S hST (π z)
    have hiff : stepRegime (companionOf n A o) s S (π z) ↔
        stepRegime (companionOf n B (e*o)) s S (π z) := by
      unfold stepRegime
      rw [hl,hsp]
    rw [regimeRun_step, regimeRun_step, ih hST (π z)]
    by_cases h : stepRegime (companionOf n A o) s S (π z)
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]

/-- On the special branch of each literal masked companion suffix, the native
Step 1 values are equal for any lower invariant. -/
theorem actual_masked_companion_stepOne_special {n : ℕ} (hn : 0 < n) {X Y Z : CMfd.{0} n}
    {k r : ℕ} {Λ : Type} [LinearOrder Λ] (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n r Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) {e o : ℕ} (he : 1 ≤ e) (ho : 1 ≤ o)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T) :
    let W := ordMask (geoTransformAlong M T) o
    let A := MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → Y) (geoTransformAlong M T)
    let B := MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → Y)
      (geoTransformAlong (powerMarked M e) T)
    ∀ (S : BlowupTower (CMfd.of (n := n) W) Z), IsGeoTestTower (companionOf n A o) S → ∀ z : Z,
      IsSpecial (companionOf n A o) S z →
      Seq.StepOneValueMasked.stepOneInvM R (companionOf n A o) S z =
        Seq.StepOneValueMasked.stepOneInvM R (companionOf n B (e*o)) S z := by
  let W := ordMask (geoTransformAlong M T) o
  let A := MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → Y) (geoTransformAlong M T)
  let B := MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → Y)
    (geoTransformAlong (powerMarked M e) T)
  change ∀ (S : BlowupTower (CMfd.of (n := n) W) Z), IsGeoTestTower (companionOf n A o) S → ∀ z : Z,
    IsSpecial (companionOf n A o) S z →
    Seq.StepOneValueMasked.stepOneInvM R (companionOf n A o) S z =
      Seq.StepOneValueMasked.stepOneInvM R (companionOf n B (e*o)) S z
  intro S hS z hs
  obtain ⟨hl, hsp⟩ := actual_masked_companion_step_skeleton hn M hM he ho T hT S hS z
  change Seq.StepOneValueMasked.stepOneInvL R (companionOf n A o) _ S z =
    Seq.StepOneValueMasked.stepOneInvL R (companionOf n B (e*o)) _ S z
  rw [Seq.StepOneValueMasked.stepOneInvL_of_isSpecial R _ _ S hs,
    Seq.StepOneValueMasked.stepOneInvL_of_isSpecial R _ _ S (hsp.mp hs), hl]

end
end Hironaka.HironakaG8PowerActualCompanionStep
