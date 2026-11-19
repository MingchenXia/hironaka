import Hironaka.Resolution.HironakaG8PowerNonmonomialOrder
import Hironaka.Resolution.HironakaActualOriginalPowerTransform
import Hironaka.Resolution.HironakaG8MixedOrderInvariance

/-! Raw order and companion-run clocks for original whole-power recodings. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8PowerOriginalHistory
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  ResolutionInvariantSpec StepOneRegime NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderTransport NonmonomialOrderTail
  HironakaActualPowerBoundaryExponents HironakaActualOriginalPowerTransform
  HironakaG8PowerNonmonomialOrder HironakaG8MixedOrderInvariance CanonicalCentres

/-- The literal original power has scaled native nonmonomial order at every
carrier point of every actual controlled test history. -/
theorem nmOrd_original_power_history {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M) {e : ℕ} (he : 1 ≤ e)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T) {y : Y}
    (hy : y ∈ (geoTransformAlong M T).N) :
    nmOrd (geoTransformAlong (powerMarked M e) T) y = e * nmOrd (geoTransformAlong M T) y := by
  have hC := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT
  obtain ⟨hPT, hEq⟩ := original_power_transform M hM e he T hT
  have hP := InvDomainTowerAlong.isInvDomain_geoTransformAlong (powerMarked_isInvDomain M hM he) T hPT
  have hPow := powerMarked_isInvDomain (geoTransformAlong M T) hC he
  have hOrders := nmOrd_geoTransformAlong_congr hEq hP.isWellFormed.isClosedSubmanifold_N.1
    hP.isWellFormed.isCoherent hPow.isWellFormed.isCoherent (BlowupTower.refl : BlowupTower Y Y) y
  exact hOrders.trans (nmOrd_powerMarked hn (geoTransformAlong M T) hC he hy)

/-- The two genuine companion masks at any original controlled stage agree
as open subsets after rescaling the order. -/
theorem ordMask_original_power_history {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M) {e : ℕ} (he : 1 ≤ e)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T) (o : ℕ) :
    ordMask (geoTransformAlong (powerMarked M e) T) (e * o) =
      ordMask (geoTransformAlong M T) o := by
  have hC := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT
  obtain ⟨hPT, hEq⟩ := original_power_transform M hM e he T hT
  have hP := InvDomainTowerAlong.isInvDomain_geoTransformAlong (powerMarked_isInvDomain M hM he) T hPT
  have hN : (geoTransformAlong (powerMarked M e) T).N = (geoTransformAlong M T).N := hEq.N_eq
  ext y
  change y ∈ ordMask (geoTransformAlong (powerMarked M e) T) (e * o) ↔
    y ∈ ordMask (geoTransformAlong M T) o
  rw [mem_ordMask_iff hn hP.isWellFormed hP.isNonzeroAlongAt,
    mem_ordMask_iff hn hC.isWellFormed hC.isNonzeroAlongAt]
  by_cases hy : y ∈ (geoTransformAlong M T).N
  · have hyp : y ∈ (geoTransformAlong (powerMarked M e) T).N := hN.symm ▸ hy
    rw [mem_ordGe_iff hP.isWellFormed hP.isNonzeroAlongAt hyp,
      mem_ordGe_iff hC.isWellFormed hC.isNonzeroAlongAt hy,
      nmOrd_original_power_history hn M hM he T hT hy]
    have hepos : 0 < e := by omega
    constructor <;> intro h hle
    · apply h
      have := Nat.mul_le_mul_left e hle
      simp only [Nat.mul_add, Nat.mul_one] at this
      omega
    · apply h
      have hc : e * o < e * nmOrd (geoTransformAlong M T) y := by omega
      exact Nat.lt_of_mul_lt_mul_left hc
  · have hyp : y ∉ (geoTransformAlong (powerMarked M e) T).N := by simpa [hN] using hy
    constructor <;> intro _ h
    · exact hy h.1
    · exact hyp h.1

/-- Positive powers preserve the companion run's physical starting index,
with the raw nonmonomial order rescaled. -/
theorem regimeRun_original_power_history {n : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M) {e : ℕ} (he : 1 ≤ e) (o : ℕ) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), IsGeoTestTower M T → ∀ y : Y,
      regimeRun (OrdRegime M o) T y = regimeRun (OrdRegime (powerMarked M e) (e * o)) T y
  | _, .refl, _, _ => rfl
  | _, .step T C π hπ, hT, z => by
    have hTT := ((isGeoTestTower_step_iff M T C π hπ).mp hT).1
    have hC := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hTT
    have hEq := (original_power_transform M hM e he T hTT).2
    have hcos := hEq.cosupp_eq.trans (powerMarked_cosupp (geoTransformAlong M T) hC he)
    have hiff : OrdRegime M o T (π z) ↔ OrdRegime (powerMarked M e) (e * o) T (π z) := by
      show (π z ∈ (geoTransformAlong M T).cosupp ∧ nmOrd (geoTransformAlong M T) (π z) = o) ↔
        (π z ∈ (geoTransformAlong (powerMarked M e) T).cosupp ∧
          nmOrd (geoTransformAlong (powerMarked M e) T) (π z) = e * o)
      constructor
      · rintro ⟨hc, ho⟩
        exact ⟨hcos.symm ▸ hc, (nmOrd_original_power_history hn M hM he T hTT
          ((geoTransformAlong M T).cosupp_subset_N hc)).trans (congrArg (e * ·) ho)⟩
      · rintro ⟨hc, ho⟩
        have hc' : π z ∈ (geoTransformAlong M T).cosupp := hcos ▸ hc
        have hOrd := nmOrd_original_power_history hn M hM he T hTT
          ((geoTransformAlong M T).cosupp_subset_N hc')
        exact ⟨hc', Nat.eq_of_mul_eq_mul_left (by omega : 0 < e) (hOrd.symm.trans ho)⟩
    rw [regimeRun_step, regimeRun_step, regimeRun_original_power_history hn M hM he o T hTT (π z)]
    by_cases hP : OrdRegime M o T (π z)
    · rw [if_pos hP, if_pos (hiff.mp hP)]
    · rw [if_neg hP, if_neg (fun h => hP (hiff.mpr h))]

/-- The first field of the original canonical invariant along the same
controlled history scales by the positive recoding exponent. -/
theorem canonicalInvariant_fst_original_power_history {n : ℕ} {X Y : CMfd.{0} (n + 1)}
    {k : ℕ} (M : MarkedIdeal (n + 1) X) (hM : IsInvDomain k M) {e : ℕ} (he : 1 ≤ e)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T) {y : Y}
    (hy : y ∈ (geoTransformAlong M T).N) :
    fstEntry ((canonicalInvariant (n + 1)).inv (powerMarked M e) T y) =
      e * fstEntry ((canonicalInvariant (n + 1)).inv M T y) := by
  rw [canonicalInvariant_fst, canonicalInvariant_fst]
  exact nmOrd_original_power_history (Nat.succ_pos n) M hM he T hT hy

end
end Hironaka.HironakaG8PowerOriginalHistory
