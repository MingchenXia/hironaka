import Hironaka.Analytic.ActualRadialIntegrabilityExponent
import Hironaka.Analytic.PotentialTheory.MultiplierIdealsBasic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

set_option autoImplicit false

/-! # Actual unit multiplier integrability bounds logarithmic exponents -/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace Hironaka.ActualMultiplierLogarithmicExponent

noncomputable section

/-- Actual Haar translation transports the radial threshold to any center. -/
theorem exponent_lt_finrank_of_integrableOn_norm_sub_rpow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {a R : ℝ} {x : E} (hR : 0 < R)
    (hint : IntegrableOn (fun y : E => ‖y - x‖ ^ (-a)) (ball x R) μ) :
    a < (Module.finrank ℝ E : ℝ) := by
  have ht := ((measurePreserving_add_right μ x).integrableOn_comp_preimage
    (Homeomorph.addRight x).measurableEmbedding).mpr hint
  have hs : (fun y : E => y + x) ⁻¹' ball x R = ball 0 R := by
    ext y
    simp only [mem_preimage, mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero]
  rw [hs] at ht
  have hi : IntegrableOn (fun y : E => ‖y‖ ^ (-a)) (ball 0 R) μ := by
    simpa only [Function.comp_def, add_sub_cancel_right] using ht
  exact ActualRadialIntegrabilityExponent.exponent_lt_finrank_of_integrableOn_norm_rpow
    μ hR hi

/-- True unit multiplier integrability and a punctured logarithmic upper bound
force each exponent below the real-dimensional inverse-integrability threshold. -/
theorem logarithmic_exponent_lt_finrank_div_of_unit_multiplier
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {u : E → EReal} {x : E}
    {c γ C : ℝ}
    (hint : MultiplierIntegrableAt u c (fun _ => (1 : ℂ)) x μ)
    (hlog : ∀ᶠ y in 𝓝[≠] x,
      u y ≤ ((γ * Real.log ‖y - x‖ + C : ℝ) : EReal)) :
    γ < (Module.finrank ℝ E : ℝ) / c := by
  have hc : 0 < c := hint.1
  have hd : 0 < (Module.finrank ℝ E : ℝ) := Nat.cast_pos.mpr Module.finrank_pos
  by_cases hγ : γ ≤ 0
  · exact hγ.trans_lt (div_pos hd hc)
  have hγpos : 0 < γ := lt_of_not_ge hγ
  obtain ⟨U, hU, hxU, -, hL2⟩ := hint.2
  have hevent : ∀ᶠ y in 𝓝 x, y ∈ U ∧
      (y ≠ x → u y ≤ ((γ * Real.log ‖y - x‖ + C : ℝ) : EReal)) := by
    filter_upwards [hU.mem_nhds hxU, eventually_nhdsWithin_iff.mp hlog] with y hy hl
    exact ⟨hy, hl⟩
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp hevent
  have hBU : ball x R ⊆ U := fun _ hy => (hball hy).1
  have hpoint : ∀ y ∈ ball x R,
      ENNReal.ofReal (‖y - x‖ ^ (-(c * γ))) ≤
        ENNReal.ofReal (Real.exp (c * C)) * multiplierWeight c (u y) := by
    intro y hy
    by_cases hyx : y = x
    · subst y
      simp only [sub_self, norm_zero, Real.zero_rpow (ne_of_lt (neg_neg_of_pos
        (mul_pos hc hγpos))), ENNReal.ofReal_zero]
      exact bot_le
    have hnorm : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyx)
    have hid : ENNReal.ofReal (‖y - x‖ ^ (-(c * γ))) =
        ENNReal.ofReal (Real.exp (c * C)) *
          multiplierWeight c ((γ * Real.log ‖y - x‖ + C : ℝ) : EReal) := by
      rw [multiplierWeight_coe, ← ENNReal.ofReal_mul (Real.exp_nonneg _),
        ← Real.exp_add, Real.rpow_def_of_pos hnorm]
      congr 2
      ring
    rw [hid]
    gcongr
    exact multiplierWeight_antitone hc.le ((hball hy).2 hyx)
  have hfinite : (∫⁻ y in ball x R, ENNReal.ofReal (‖y - x‖ ^ (-(c * γ))) ∂μ) < ⊤ := by
    calc
      _ ≤ ∫⁻ y in ball x R, ENNReal.ofReal (Real.exp (c * C)) *
          multiplierWeight c (u y) ∂μ :=
        setLIntegral_mono_ae' measurableSet_ball (Eventually.of_forall hpoint)
      _ = ENNReal.ofReal (Real.exp (c * C)) *
          ∫⁻ y in ball x R, multiplierWeight c (u y) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by
        simpa only [multiplierDensity, norm_one, one_pow, ENNReal.ofReal_one, one_mul]
          using (hL2.mono hBU).2)
  have hmeas : Measurable (fun y : E => ‖y - x‖ ^ (-(c * γ))) := by fun_prop
  have hi : IntegrableOn (fun y : E => ‖y - x‖ ^ (-(c * γ))) (ball x R) μ :=
    ⟨hmeas.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y =>
        Real.rpow_nonneg (norm_nonneg _) _)).mpr hfinite⟩
  have hlt := exponent_lt_finrank_of_integrableOn_norm_sub_rpow μ hR hi
  exact (lt_div_iff₀ hc).mpr (by simpa only [mul_comm] using hlt)

end

end Hironaka.ActualMultiplierLogarithmicExponent
