import Hironaka.Analytic.ComplexMonomialMultiplierThreshold
import Hironaka.Analytic.StrongOpennessSliceInduction

set_option autoImplicit false

/-! # Actual holomorphic unit transport of multiplier germs -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Hironaka.ComplexMonomialMultiplierUnit

noncomputable section

/-- An actual holomorphic unit preserves the literal multiplier germ for every raw weight. -/
theorem multiplierIntegrableAt_mul_unit_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    {φ : E → EReal} {c : ℝ} {f g : E → ℂ} {x : E}
    (hg : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ g y) (hg0 : g x ≠ 0) :
    MultiplierIntegrableAt φ c (fun y => g y * f y) x μ ↔
      MultiplierIntegrableAt φ c f x μ := by
  have hne : ∀ᶠ y in 𝓝 x, g y ≠ 0 :=
    hg.self_of_nhds.continuousAt.eventually_ne hg0
  have hinv : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ (fun z => (g z)⁻¹) y := by
    filter_upwards [hg, hne] with y hy hy0
    exact hy.inv hy0
  constructor
  · intro hint
    have hback := multiplierIntegrableAt_differentiable_mul hint hinv
    apply hback.congr EventuallyEq.rfl
    filter_upwards [hne] with y hy
    simp only [← mul_assoc, inv_mul_cancel₀ hy, one_mul]
  · intro hint
    exact multiplierIntegrableAt_differentiable_mul hint hg

/-- The same strict transverse threshold after an actual holomorphic unit factor. -/
theorem multiplierIntegrableAt_log_unit_monomial_iff
    (a : ℕ) (b : ℝ) {c : ℝ} (hc : 0 < c) {g : ℂ → ℂ}
    (hg : ∀ᶠ w in 𝓝 (0 : ℂ), DifferentiableAt ℂ g w) (hg0 : g 0 ≠ 0) :
    MultiplierIntegrableAt (fun w : ℂ => ((2 * b : ℝ) : EReal) *
      ENNReal.log (ENNReal.ofReal ‖w‖)) c (fun w => g w * w ^ a) 0 volume ↔
      c * b < (a : ℝ) + 1 := by
  exact (multiplierIntegrableAt_mul_unit_iff hg hg0).trans
    (ComplexMonomialMultiplierThreshold.multiplierIntegrableAt_log_monomial_iff a b hc)

end
end Hironaka.ComplexMonomialMultiplierUnit
