import Hironaka.Analytic.MultiplierHaarLinearTransport
import Hironaka.Analytic.SNCCoordinateUnitCorrection

set_option autoImplicit false

/-! # The literal normal-coordinate criterion for the actual Euclidean model -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Hironaka.SNCEuclideanCoordinateMultiplier



noncomputable section

/-- Exact coordinate thresholds for the actual Euclidean model and preferred volume. -/
theorem multiplierIntegrableAt_sum_log_unit_monomial_iff {n : ℕ}
    (a : Fin n → ℕ) (b : Fin n → ℝ) {c : ℝ} (hc : 0 < c)
    {g : ComplexModel n → ℂ} {ρ : ComplexModel n → ℝ}
    (hg : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ g z) (hg0 : g 0 ≠ 0)
    (hρ : ∀ᶠ z in 𝓝 (0 : ComplexModel n), ContinuousAt ρ z) :
    MultiplierIntegrableAt (fun z : ComplexModel n =>
      (∑ i, ((2 * b i : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal ‖z i‖)) + (ρ z : EReal))
      c (fun z => g z * ∏ i, z i ^ a i) 0 volume ↔
        ∀ i, c * b i < (a i : ℝ) + 1 := by
  let L : ComplexModel n ≃L[ℂ] (Fin n → ℂ) :=
    PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)
  have hT : Tendsto L.symm (𝓝 (0 : Fin n → ℂ)) (𝓝 (0 : ComplexModel n)) := by
    simpa only [map_zero] using L.symm.continuousAt.tendsto (x := 0)
  have hg' : ∀ᶠ y in 𝓝 (0 : Fin n → ℂ), DifferentiableAt ℂ (g ∘ L.symm) y := by
    filter_upwards [hT.eventually hg] with y hy
    exact hy.comp y L.symm.differentiableAt
  have hρ' : ∀ᶠ y in 𝓝 (0 : Fin n → ℂ), ContinuousAt (ρ ∘ L.symm) y := by
    filter_upwards [hT.eventually hρ] with y hy
    exact hy.comp L.symm.continuousAt
  have hg0' : (g ∘ L.symm) 0 ≠ 0 := by
    simpa only [Function.comp_apply, map_zero] using hg0
  let φ : (Fin n → ℂ) → EReal := fun y =>
    (∑ i, ((2 * b i : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal ‖y i‖)) +
      ((ρ ∘ L.symm) y : EReal)
  let f : (Fin n → ℂ) → ℂ := fun y => (g ∘ L.symm) y * ∏ i, y i ^ a i
  have hcoords :=
    MultiplierHaarLinearTransport.multiplierIntegrableAt_continuousLinearEquiv_iff
      (volume : Measure (ComplexModel n)) (volume : Measure (Fin n → ℂ)) L
      (φ := φ) (f := f) (c := c) (x := 0)
  have hplain : MultiplierIntegrableAt φ c f 0 volume ↔
      ∀ i, c * b i < (a i : ℝ) + 1 :=
    SNCCoordinateUnitCorrection.multiplierIntegrableAt_sum_log_unit_monomial_iff
      a b hc hg' hg0' hρ'
  simpa only [φ, f, Function.comp_def, L.symm_apply_apply, map_zero,
    L, PiLp.coe_continuousLinearEquiv, PiLp.coe_symm_continuousLinearEquiv,
    WithLp.toLp_ofLp] using
    hcoords.trans hplain

end
end Hironaka.SNCEuclideanCoordinateMultiplier
