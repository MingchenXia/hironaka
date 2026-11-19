import Mathlib.Analysis.SpecialFunctions.Pow.Integral

set_option autoImplicit false

/-! # Actual inverse radial power integrability and the real dimension -/

open Set Metric MeasureTheory

namespace Hironaka.ActualRadialIntegrabilityExponent

noncomputable section

/-- Actual polar transport and the exact positive-interval power criterion
detect the true finite real dimension from ball integrability. -/
theorem exponent_lt_finrank_of_integrableOn_norm_rpow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {a R : ℝ} (hR : 0 < R)
    (hint : IntegrableOn (fun x : E => ‖x‖ ^ (-a)) (ball 0 R) μ) :
    a < (Module.finrank ℝ E : ℝ) := by
  have hd : 1 ≤ Module.finrank ℝ E := Nat.succ_le_iff.mpr Module.finrank_pos
  have hpolar := (integrableOn_fun_norm_addHaar μ
    (f := fun r : ℝ => r ^ (-a)) (r := R)).mp hint
  have hp : IntegrableOn
      (fun r : ℝ => r ^ (((Module.finrank ℝ E - 1 : ℕ) : ℝ) - a)) (Ioo 0 R) := by
    refine hpolar.congr_fun (fun r hr => ?_) measurableSet_Ioo
    simp only [smul_eq_mul, ← Real.rpow_natCast]
    simpa only [sub_eq_add_neg] using
      (Real.rpow_add hr.1 (((Module.finrank ℝ E - 1 : ℕ) : ℝ)) (-a)).symm
  have hlt := (intervalIntegral.integrableOn_Ioo_rpow_iff hR).mp hp
  have hdR : ((Module.finrank ℝ E - 1 : ℕ) : ℝ) = (Module.finrank ℝ E : ℝ) - 1 := by
    simp only [Nat.cast_sub hd, Nat.cast_one]
  rw [hdR] at hlt
  linarith

end

end Hironaka.ActualRadialIntegrabilityExponent
