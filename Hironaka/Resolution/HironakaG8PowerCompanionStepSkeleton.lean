import Hironaka.Resolution.HironakaG8PowerCompanionLocal
import Hironaka.Resolution.HironakaG8MemberLoci
import Hironaka.Invariant.StepOneSeq
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8PowerCompanionStepSkeleton
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  ResolutionInvariantSpec NonmonomialOrderLocal CompanionRebase CompanionReductionAlong
  HironakaActualPowerBoundaryExponents HironakaG8PowerCompanionLocal HironakaG8MemberLoci
  HironakaG11InvBMClass StepOneValue StepOneRegime ResolutionInvariantSeq

/-- The native Step 1 level and special locus agree along every controlled
companion test for an original record and its positive whole power. -/
theorem power_companion_step_skeleton {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M) {e o : ℕ} (he : 1 ≤ e) (ho : 1 ≤ o)
    (hb : ∀ x ∈ M.cosupp, x ∉ ordGe M (o+1))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (companionOf n M o) T) (y : Y) :
    level (companionOf n M o) T y = level (companionOf n (powerMarked M e) (e*o)) T y ∧
    (IsSpecial (companionOf n M o) T y ↔ IsSpecial (companionOf n (powerMarked M e) (e*o)) T y) := by
  have hP := powerMarked_isInvDomain M hM he
  have hA := InvDomainCompanion.isInvDomain_companionAlong hn hM ho
  have hB := InvDomainCompanion.isInvDomain_companionAlong hn hP (Nat.mul_pos he ho)
  have hW := (locWPEquiv_companionOf_powerMarked hn M hM he ho hb).wEquiv
  have hdim : SameCarrierDim (companionOf n M o) (companionOf n (powerMarked M e) (e*o)) := by
    apply SameCarrierDim.of_N_eq
    simp only [companionOf, companionAlong_N, powerMarked]
  exact ⟨level_eq_of_E_eq hW.1 T y, isSpecial_iff_of_wEquiv hn hA hB hW hdim T hT y⟩

/-- Their native Step 1 level-regime run indices are literally the same. -/
theorem power_companion_step_run {n : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M) {e o : ℕ} (he : 1 ≤ e) (ho : 1 ≤ o)
    (hb : ∀ x ∈ M.cosupp, x ∉ ordGe M (o+1)) (s : ℕ) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), IsGeoTestTower (companionOf n M o) T → ∀ y : Y,
      regimeRun (stepRegime (companionOf n M o) s) T y =
        regimeRun (stepRegime (companionOf n (powerMarked M e) (e*o)) s) T y
  | _, .refl, _, _ => rfl
  | _, .step T C π hπ, hT, z => by
    have hTT := ((isGeoTestTower_step_iff (companionOf n M o) T C π hπ).mp hT).1
    obtain ⟨hl, hs⟩ := power_companion_step_skeleton hn M hM he ho hb T hTT (π z)
    have hiff : stepRegime (companionOf n M o) s T (π z) ↔
        stepRegime (companionOf n (powerMarked M e) (e*o)) s T (π z) := by
      unfold stepRegime
      rw [hl,hs]
    rw [regimeRun_step, regimeRun_step, power_companion_step_run hn M hM he ho hb s T hTT (π z)]
    by_cases h : stepRegime (companionOf n M o) s T (π z)
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]

/-- On native Step 1's special branch, the actual original companion and
its whole-power recoding have exactly equal lower values. -/
theorem power_companion_stepOne_special {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    {k r : ℕ} {Λ : Type} [LinearOrder Λ] (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n r Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) {e o : ℕ} (he : 1 ≤ e) (ho : 1 ≤ o)
    (hb : ∀ x ∈ M.cosupp, x ∉ ordGe M (o+1))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (companionOf n M o) T) {y : Y}
    (hs : IsSpecial (companionOf n M o) T y) :
    Seq.StepOneValueMasked.stepOneInvM R (companionOf n M o) T y =
      Seq.StepOneValueMasked.stepOneInvM R (companionOf n (powerMarked M e) (e*o)) T y := by
  obtain ⟨hl, hspecial⟩ := power_companion_step_skeleton hn M hM he ho hb T hT y
  change Seq.StepOneValueMasked.stepOneInvL R (companionOf n M o) _ T y =
    Seq.StepOneValueMasked.stepOneInvL R (companionOf n (powerMarked M e) (e*o)) _ T y
  rw [Seq.StepOneValueMasked.stepOneInvL_of_isSpecial R _ _ T hs,
    Seq.StepOneValueMasked.stepOneInvL_of_isSpecial R _ _ T (hspecial.mp hs),hl]

end
end Hironaka.HironakaG8PowerCompanionStepSkeleton
