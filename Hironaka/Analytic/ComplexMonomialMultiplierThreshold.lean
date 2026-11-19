import Hironaka.Analytic.ActualMultiplierLogarithmicExponent
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

set_option autoImplicit false

/-! # Actual transverse monomial multiplier thresholds -/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace Hironaka.ComplexMonomialMultiplierThreshold

noncomputable section

private theorem density_eq_rpow_of_ne_zero (a : ℕ) (b c : ℝ) {z : ℂ} (hz : z ≠ 0) :
    multiplierDensity (fun w : ℂ => ((2 * b : ℝ) : EReal) *
      ENNReal.log (ENNReal.ofReal ‖w‖)) c (fun w => w ^ a) z =
      ENNReal.ofReal (‖z‖ ^ (2 * (a : ℝ) - 2 * c * b)) := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [multiplierDensity, ENNReal.log_ofReal_of_pos hn, ← EReal.coe_mul,
    multiplierWeight_coe, norm_pow, ← ENNReal.ofReal_mul (sq_nonneg _),
    ← pow_mul, ← Real.rpow_natCast, Real.rpow_def_of_pos hn,
    ← Real.exp_add, Real.rpow_def_of_pos hn]
  congr 2
  push_cast
  ring

private theorem integrableOn_complex_norm_rpow_iff {s R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun z : ℂ => ‖z‖ ^ s) (ball 0 R) volume ↔ -2 < s := by
  have hd : 1 ≤ Module.finrank ℝ ℂ := by norm_num [Complex.finrank_real_complex]
  constructor
  · intro hint
    have hi : IntegrableOn (fun z : ℂ => ‖z‖ ^ (-(-s))) (ball 0 R) volume := by
      simpa only [neg_neg] using hint
    have h := ActualRadialIntegrabilityExponent.exponent_lt_finrank_of_integrableOn_norm_rpow
      volume hR hi
    norm_num [Complex.finrank_real_complex] at h
    linarith
  · intro hs
    have hdim : -s < (Module.finrank ℝ ℂ : ℝ) := by norm_num [Complex.finrank_real_complex]; linarith
    have hm : Measurable (fun z : ℂ => ‖z‖ ^ s) := by fun_prop
    apply integrableOn_ball_of_norm_le_rpow hd hdim (C := 1) (α := -s) (r := R)
      (h_meas := hm.aestronglyMeasurable)
    exact Eventually.of_forall fun z => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) s),
        neg_neg, one_mul] using (le_rfl : ‖z‖ ^ s ≤ ‖z‖ ^ s)

/-- Literal finite weighted mass for a monomial in one complex coordinate. -/
theorem weightedL2On_log_monomial_iff (a : ℕ) (b c : ℝ) {R : ℝ} (hR : 0 < R) :
    WeightedL2On (fun w : ℂ => ((2 * b : ℝ) : EReal) *
      ENNReal.log (ENNReal.ofReal ‖w‖)) c (fun w => w ^ a) (ball 0 R) volume ↔
      c * b < (a : ℝ) + 1 := by
  let s : ℝ := 2 * (a : ℝ) - 2 * c * b
  have hm : Measurable (fun z : ℂ => ‖z‖ ^ s) := by fun_prop
  have hden : multiplierDensity (fun w : ℂ => ((2 * b : ℝ) : EReal) *
      ENNReal.log (ENNReal.ofReal ‖w‖)) c (fun w => w ^ a) =ᵐ[volume]
      (fun z => ENNReal.ofReal (‖z‖ ^ s)) := by
    filter_upwards [volume.ae_ne (0 : ℂ)] with z hz
    exact density_eq_rpow_of_ne_zero a b c hz
  have hball := ae_restrict_of_ae hden (s := ball (0 : ℂ) R)
  have hint_eq := lintegral_congr_ae hball
  have hnonneg : ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) R), 0 ≤ ‖z‖ ^ s :=
    Eventually.of_forall fun z => Real.rpow_nonneg (norm_nonneg z) s
  constructor
  · intro hL2
    have hfinite : (∫⁻ z in ball (0 : ℂ) R, ENNReal.ofReal (‖z‖ ^ s)) < ⊤ := by
      rw [← hint_eq]
      exact hL2.2
    have hint : IntegrableOn (fun z : ℂ => ‖z‖ ^ s) (ball 0 R) volume :=
      ⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnonneg).mpr hfinite⟩
    have hs := (integrableOn_complex_norm_rpow_iff hR).mp hint
    dsimp [s] at hs
    linarith
  · intro hcb
    have hs : -2 < s := by dsimp [s]; linarith
    have hint := (integrableOn_complex_norm_rpow_iff hR).mpr hs
    refine ⟨(hm.ennreal_ofReal.aemeasurable.congr hden.symm).restrict, ?_⟩
    rw [hint_eq]
    exact (hasFiniteIntegral_iff_ofReal hnonneg).mp hint.2

/-- The actual holomorphic multiplier germ has the same strict threshold. -/
theorem multiplierIntegrableAt_log_monomial_iff (a : ℕ) (b : ℝ) {c : ℝ} (hc : 0 < c) :
    MultiplierIntegrableAt (fun w : ℂ => ((2 * b : ℝ) : EReal) *
      ENNReal.log (ENNReal.ofReal ‖w‖)) c (fun w => w ^ a) 0 volume ↔
      c * b < (a : ℝ) + 1 := by
  constructor
  · intro hint
    obtain ⟨U, hU, hzU, -, hL2⟩ := hint.2
    obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hU 0 hzU
    exact (weightedL2On_log_monomial_iff a b c hR).mp (hL2.mono hball)
  · intro hcb
    refine ⟨hc, ball 0 1, isOpen_ball, by simp, ?_, ?_⟩
    · exact (differentiableOn_id).pow a
    · exact (weightedL2On_log_monomial_iff a b c (by norm_num : (0 : ℝ) < 1)).mpr hcb

end
end Hironaka.ComplexMonomialMultiplierThreshold
