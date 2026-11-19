import Hironaka.Analytic.SNCCoordinateMonomialMultiplier
import Hironaka.Analytic.ComplexMonomialMultiplierUnit
import Hironaka.Analytic.QuantitativeRegularizationChartBranch

set_option autoImplicit false

/-! # Actual continuous remainder and holomorphic unit transport in normal coordinates -/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace Hironaka.SNCCoordinateUnitCorrection

noncomputable section

private theorem multiplierIntegrableAt_add_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    {φ : E → EReal} {ρ : E → ℝ} {c : ℝ} {f : E → ℂ} {x : E}
    (hρ : ∀ᶠ y in 𝓝 x, ContinuousAt ρ y)
    (hf : MultiplierIntegrableAt φ c f x μ) :
    MultiplierIntegrableAt (fun y => φ y + (ρ y : EReal)) c f x μ := by
  obtain ⟨hc, U, hU, hxU, hfhol, hfint⟩ := hf
  have hbound : ∀ᶠ y in 𝓝 x, |ρ y| ≤ |ρ x| + 1 := by
    have hnorm : Tendsto (fun y => |ρ y|) (𝓝 x) (𝓝 |ρ x|) :=
      hρ.self_of_nhds.abs
    exact (hnorm.eventually_lt tendsto_const_nhds (by linarith)).mono fun _ hy => hy.le
  obtain ⟨V, hVsub, hV, hxV⟩ := _root_.mem_nhds_iff.mp (hρ.and hbound)
  let W := U ∩ V
  have hW : IsOpen W := hU.inter hV
  have hρW : ContinuousOn ρ W := fun y hy => (hVsub hy.2).1.continuousWithinAt
  have hfW := hfint.mono (inter_subset_left : W ⊆ U)
  have hdens (y : E) :
      multiplierDensity (fun z => φ z + (ρ z : EReal)) c f y =
        ENNReal.ofReal (Real.exp (-(c * ρ y))) * multiplierDensity φ c f y := by
    rw [multiplierDensity, QuantitativeRegularizationChartBranch.multiplierWeight_add_coe hc]
    simp only [multiplierDensity]
    ac_rfl
  refine ⟨hc, W, hW, ⟨hxU, hxV⟩, hfhol.mono inter_subset_left, ?_, ?_⟩
  · have hfactor : AEMeasurable (fun y => ENNReal.ofReal (Real.exp (-(c * ρ y))))
        (μ.restrict W) :=
      (ENNReal.continuous_ofReal.comp_continuousOn
        (((continuousOn_const.mul hρW).neg).rexp)).aemeasurable hW.measurableSet
    have hfun : multiplierDensity (fun y => φ y + (ρ y : EReal)) c f =
        fun y => ENNReal.ofReal (Real.exp (-(c * ρ y))) * multiplierDensity φ c f y :=
      funext hdens
    rw [hfun]
    exact hfactor.mul hfW.1
  · let K : ℝ≥0∞ := ENNReal.ofReal (Real.exp (c * (|ρ x| + 1)))
    calc
      (∫⁻ y in W, multiplierDensity (fun z => φ z + (ρ z : EReal)) c f y ∂μ) ≤
          ∫⁻ y in W, K * multiplierDensity φ c f y ∂μ := by
        refine setLIntegral_mono_ae' hW.measurableSet
          (Eventually.of_forall fun y hy => ?_)
        rw [hdens]
        apply mul_le_mul_left
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        have hρbound := (hVsub hy.2).2
        have hρlower := neg_le_abs (ρ y)
        nlinarith
      _ = K * ∫⁻ y in W, multiplierDensity φ c f y ∂μ := by
        rw [lintegral_const_mul' K _ (by simp [K])]
      _ < ⊤ := ENNReal.mul_lt_top (by simp [K]) hfW.2

/-- Actual continuous real remainders preserve the literal germ for arbitrary raw weights. -/
theorem multiplierIntegrableAt_add_continuous_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    {φ : E → EReal} {ρ : E → ℝ} {c : ℝ} {f : E → ℂ} {x : E}
    (hρ : ∀ᶠ y in 𝓝 x, ContinuousAt ρ y) :
    MultiplierIntegrableAt (fun y => φ y + (ρ y : EReal)) c f x μ ↔
      MultiplierIntegrableAt φ c f x μ := by
  constructor
  · intro hf
    have hneg : ∀ᶠ y in 𝓝 x, ContinuousAt (fun z => -ρ z) y :=
      hρ.mono fun _ hy => hy.neg
    have hback := multiplierIntegrableAt_add_continuous hneg hf
    apply hback.congr ?_ EventuallyEq.rfl
    exact Eventually.of_forall fun y => by
      dsimp only
      rw [add_assoc, ← EReal.coe_add]
      simp only [add_neg_cancel, EReal.coe_zero, add_zero]
  · intro hf
    exact multiplierIntegrableAt_add_continuous hρ hf

/-- The exact normal-coordinate thresholds with an actual holomorphic unit and real remainder. -/
theorem multiplierIntegrableAt_sum_log_unit_monomial_iff {n : ℕ}
    (a : Fin n → ℕ) (b : Fin n → ℝ) {c : ℝ} (hc : 0 < c)
    {g : (Fin n → ℂ) → ℂ} {ρ : (Fin n → ℂ) → ℝ}
    (hg : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), DifferentiableAt ℂ g z) (hg0 : g 0 ≠ 0)
    (hρ : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), ContinuousAt ρ z) :
    MultiplierIntegrableAt (fun z : Fin n → ℂ =>
      (∑ i, ((2 * b i : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal ‖z i‖)) + (ρ z : EReal))
      c (fun z => g z * ∏ i, z i ^ a i) 0 volume ↔
        ∀ i, c * b i < (a i : ℝ) + 1 := by
  exact (multiplierIntegrableAt_add_continuous_iff hρ).trans
    ((ComplexMonomialMultiplierUnit.multiplierIntegrableAt_mul_unit_iff hg hg0).trans
      (SNCCoordinateMonomialMultiplier.multiplierIntegrableAt_sum_log_monomial_iff a b hc))

end
end Hironaka.SNCCoordinateUnitCorrection
