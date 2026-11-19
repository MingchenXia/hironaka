import Hironaka.Resolution.HironakaG8PowerOriginalHistory
import Hironaka.Resolution.HironakaG8CompanionEquiv
import Hironaka.Resolution.HironakaG11PresClassTransport

/-! Actual whole-power recoding preserves the original companion's controlled tests. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8PowerCompanionEquiv
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism BlowupTowers BlowupTowerTransforms
  ResolutionInvariantSpec NonmonomialOrderLocal NonmonomialOrderTail CompanionRebase
  HironakaActualPowerBoundaryExponents HironakaActualOriginalPowerTransform
  HironakaG8PowerNonmonomialOrder HironakaG8PowerOriginalHistory HironakaG8CompanionEquiv
  MarkedIdealEquivalence.MarkedIdeal

/-- At a positive order bound, the original companion and the companion of
its positive whole-power recoding have the same controlled test towers and
cosupports. The two companion marks are generally different. -/
theorem wEquiv_companionOf_powerMarked {n : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M) {e o : ℕ} (he : 1 ≤ e) (ho : 1 ≤ o)
    (hbound : ∀ x ∈ M.cosupp, x ∉ ordGe M (o + 1)) :
    WEquiv (companionOf n M o) (companionOf n (powerMarked M e) (e * o)) := by
  have hP := powerMarked_isInvDomain M hM he
  have hep : 1 ≤ e * o := Nat.mul_pos he ho
  have hboundP : ∀ x ∈ (powerMarked M e).cosupp, x ∉ ordGe (powerMarked M e) (e * o + 1) := by
    intro x hx hp
    have hxM : x ∈ M.cosupp := (powerMarked_cosupp M hM he) ▸ hx
    have hxN := M.cosupp_subset_N hxM
    have hxPN : x ∈ (powerMarked M e).N := hxN
    have hp' := (mem_ordGe_iff hP.isWellFormed hP.isNonzeroAlongAt hxPN _).mp hp
    rw [nmOrd_powerMarked hn M hM he hxN] at hp'
    have hgt : o < nmOrd M x := Nat.lt_of_mul_lt_mul_left (by omega : e * o < e * nmOrd M x)
    exact hbound x hxM ((mem_ordGe_iff hM.isWellFormed hM.isNonzeroAlongAt hxN _).mpr (by omega))
  refine wEquiv_of_cosupp_eq ?_ ?_
  · simp only [companionOf, CompanionReductionAlong.companionAlong_E, powerMarked]
  · intro Y T hTA hTP
    obtain ⟨hT, hCA⟩ := cosupp_companionOf_geoTransformAlong hM hn ho hbound T hTA
    obtain ⟨_, hCP⟩ := cosupp_companionOf_geoTransformAlong hP hn hep hboundP T hTP
    have hCurrent := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT
    have hPowered := InvDomainTowerAlong.isInvDomain_geoTransformAlong hP T
      (original_power_transform M hM e he T hT).1
    have hEq := (original_power_transform M hM e he T hT).2
    have hcos := hEq.cosupp_eq.trans (powerMarked_cosupp (geoTransformAlong M T) hCurrent he)
    rw [hCA, hCP]
    ext y
    constructor
    · rintro ⟨hg, hc⟩
      have hcP : y ∈ (geoTransformAlong (powerMarked M e) T).cosupp := hcos.symm ▸ hc
      have hy := (geoTransformAlong M T).cosupp_subset_N hc
      have hyP := (geoTransformAlong (powerMarked M e) T).cosupp_subset_N hcP
      refine ⟨(mem_ordGe_iff hPowered.isWellFormed hPowered.isNonzeroAlongAt hyP _).mpr ?_, hcP⟩
      rw [nmOrd_original_power_history hn M hM he T hT hy]
      exact Nat.mul_le_mul_left e ((mem_ordGe_iff hCurrent.isWellFormed hCurrent.isNonzeroAlongAt hy _).mp hg)
    · rintro ⟨hg, hc⟩
      have hcM : y ∈ (geoTransformAlong M T).cosupp := hcos ▸ hc
      have hy := (geoTransformAlong M T).cosupp_subset_N hcM
      have hyP := (geoTransformAlong (powerMarked M e) T).cosupp_subset_N hc
      have hp := (mem_ordGe_iff hPowered.isWellFormed hPowered.isNonzeroAlongAt hyP _).mp hg
      rw [nmOrd_original_power_history hn M hM he T hT hy] at hp
      exact ⟨(mem_ordGe_iff hCurrent.isWellFormed hCurrent.isNonzeroAlongAt hy _).mpr
        (Nat.le_of_mul_le_mul_left hp (by omega)), hcM⟩

/-- On the genuine common companion mask at any original controlled stage,
the original companion and the recoded original companion have the same
controlled tests. The powered stage is the actual transformed source power. -/
theorem masked_companion_original_power_history {n : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    {e o : ℕ} (he : 1 ≤ e) (ho : 1 ≤ o) (T : BlowupTower X Y)
    (hT : IsGeoTestTower M T) :
    let W := ordMask (geoTransformAlong M T) o
    WEquiv
      (companionOf n (M := CMfd.of (n := n) W) (MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → Y) (geoTransformAlong M T)) o)
      (companionOf n (M := CMfd.of (n := n) W) (MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → Y)
        (geoTransformAlong (powerMarked M e) T)) (e * o)) := by
  let A := geoTransformAlong M T
  let B := geoTransformAlong (powerMarked M e) T
  let W := ordMask A o
  have hA := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT
  obtain ⟨hTP, hEq⟩ := original_power_transform M hM e he T hT
  have hB := InvDomainTowerAlong.isInvDomain_geoTransformAlong (powerMarked_isInvDomain M hM he) T hTP
  have hPA := InvDomainTowerAlong.isInvDomain_pullback_val W hA
  have hbound : ∀ x ∈ (MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → Y) A).cosupp,
      x ∉ ordGe (MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → Y) A) (o + 1) := by
    intro x _ hx
    exact notMem_ordGe_of_mem_ordMask x.2
      ((mem_ordGe_pullback_val_iff hn hA.isWellFormed hA.isNonzeroAlongAt W (o + 1) x).mp hx)
  have hBase := wEquiv_companionOf_powerMarked hn (MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → Y) A)
    hPA he ho hbound
  have hPow := powerMarked_isInvDomain A hA he
  have hRE := ContactRepresentative.restrictEquiv_pullback_val W hEq hB.isWellFormed.isCoherent
    hPow.isWellFormed.isCoherent
  have hPullPow := HironakaG11PresClassTransport.pullback_powerMarked
    (M := Y) (M' := CMfd.of (n := n) W) contMDiff_subtype_val A hA.isWellFormed.isCoherent e
  rw [hPullPow] at hRE
  have hClosed : IsClosed (MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → Y) B).N :=
    hB.isWellFormed.isClosedSubmanifold_N.1.preimage continuous_subtype_val
  have hComp := companionOf_congr hRE hClosed (e * o)
  change WEquiv (companionOf n (M := CMfd.of (n := n) W) (MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → Y) A) o)
    (companionOf n (M := CMfd.of (n := n) W) (MarkedIdeal.pullback (M' := CMfd.of (n := n) W) (Subtype.val : W → Y) B) (e * o))
  rw [hComp]
  exact hBase

end
end Hironaka.HironakaG8PowerCompanionEquiv
