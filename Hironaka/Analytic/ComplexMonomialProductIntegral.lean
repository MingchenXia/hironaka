import Hironaka.Analytic.ComplexMonomialMultiplierThreshold
import Hironaka.Analytic.FiniteMultiplierProductIntegral

set_option autoImplicit false

/-! # Actual finite coordinate monomial integrals -/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace Hironaka.ComplexMonomialProductIntegral

noncomputable section

/-- The original logarithmic monomial density is measurable, including its pole. -/
theorem measurable_log_monomial_density (a : ℕ) (b c : ℝ) :
    Measurable (multiplierDensity (fun w : ℂ => ((2 * b : ℝ) : EReal) *
      ENNReal.log (ENNReal.ofReal ‖w‖)) c (fun w => w ^ a)) := by
  unfold multiplierDensity multiplierWeight
  fun_prop

private theorem density_ne_zero_of_ne_zero (a : ℕ) (b c : ℝ) {z : ℂ} (hz : z ≠ 0) :
    multiplierDensity (fun w : ℂ => ((2 * b : ℝ) : EReal) *
      ENNReal.log (ENNReal.ofReal ‖w‖)) c (fun w => w ^ a) z ≠ 0 := by
  rw [multiplierDensity, ENNReal.log_ofReal_of_pos (norm_pos_iff.mpr hz),
    ← EReal.coe_mul, multiplierWeight_coe]
  exact mul_ne_zero
    (ENNReal.ofReal_ne_zero_iff.mpr (pow_pos (norm_pos_iff.mpr (pow_ne_zero a hz)) 2))
    (ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _))

private theorem restricted_volume_ball_ne_zero {R : ℝ} (hR : 0 < R) :
    (volume : Measure ℂ).restrict (ball 0 R) ≠ 0 := by
  have hm : 0 < (volume : Measure ℂ) (ball 0 R) :=
    isOpen_ball.measure_pos volume ⟨0, mem_ball_self hR⟩
  intro hz
  have hmass : (volume : Measure ℂ) (ball 0 R) = 0 := by
    simpa using congrArg (fun μ : Measure ℂ => μ univ) hz
  exact hm.ne' hmass

/-- Actual Haar positivity supplies positive mass without any integral certificate. -/
theorem lintegral_log_monomial_ball_pos (a : ℕ) (b c : ℝ) {R : ℝ} (hR : 0 < R) :
    0 < ∫⁻ z in ball (0 : ℂ) R, multiplierDensity
      (fun w : ℂ => ((2 * b : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal ‖w‖))
      c (fun w => w ^ a) z := by
  apply pos_iff_ne_zero.mpr
  intro hzero
  let : NeZero ((volume : Measure ℂ).restrict (ball 0 R)) :=
    ⟨restricted_volume_ball_ne_zero hR⟩
  have heq := (lintegral_eq_zero_iff'
    (measurable_log_monomial_density a b c).aemeasurable.restrict).mp hzero
  have hne : ∀ᵐ z ∂(volume : Measure ℂ).restrict (ball 0 R), z ≠ 0 :=
    ae_restrict_of_ae (volume.ae_ne (0 : ℂ))
  obtain ⟨z, hz, hz0⟩ := (hne.and heq).exists
  exact density_ne_zero_of_ne_zero a b c hz hz0

/-- The actual finite product mass is finite precisely at every coordinate threshold. -/
theorem lintegral_log_monomial_prod_lt_top_iff {n : ℕ}
    (a : Fin n → ℕ) (b c R : Fin n → ℝ) (hR : ∀ i, 0 < R i) :
    (∫⁻ z : Fin n → ℂ, ∏ i, multiplierDensity
      (fun w : ℂ => ((2 * b i : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal ‖w‖))
      (c i) (fun w => w ^ a i) (z i)
      ∂Measure.pi (fun i : Fin n => (volume : Measure ℂ).restrict (ball 0 (R i)))) < ⊤ ↔
      ∀ i, c i * b i < (a i : ℝ) + 1 := by
  have hf := fun i => measurable_log_monomial_density (a i) (b i) (c i)
  have hnonzero : ∀ i, ∀ᵐ z ∂(volume : Measure ℂ).restrict (ball 0 (R i)),
      multiplierDensity (fun w : ℂ => ((2 * b i : ℝ) : EReal) *
        ENNReal.log (ENNReal.ofReal ‖w‖)) (c i) (fun w => w ^ a i) z ≠ 0 := by
    intro i
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℂ))] with z hz
    exact density_ne_zero_of_ne_zero (a i) (b i) (c i) hz
  rw [FiniteMultiplierProductIntegral.lintegral_fin_prod_lt_top_iff _ _ hf
    (fun i => restricted_volume_ball_ne_zero (hR i)) hnonzero]
  constructor
  · intro hint i
    exact (ComplexMonomialMultiplierThreshold.weightedL2On_log_monomial_iff
      (a i) (b i) (c i) (hR i)).mp ⟨(hf i).aemeasurable.restrict, hint i⟩
  · intro hthreshold i
    exact ((ComplexMonomialMultiplierThreshold.weightedL2On_log_monomial_iff
      (a i) (b i) (c i) (hR i)).mpr (hthreshold i)).2

end
end Hironaka.ComplexMonomialProductIntegral
