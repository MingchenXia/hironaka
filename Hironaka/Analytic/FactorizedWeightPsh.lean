import Hironaka.Analytic.FactorizedWeightForm
import Hironaka.Analytic.PotentialTheory.AnalyticSingularities

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# `c log U` is a `(-cΘ)`-PSH potential for a factorized weight

Let `U ≥ 0` be locally `|hₓ|² Uₓ'` with `hₓ` holomorphic and `Uₓ' > 0` smooth
(`FactorizedWeightForm.WeightFactorization`), and let `Θ` be the glued form `ddᶜ log Uₓ'`.
Then for `c > 0` the extended-real function `c log U` (value `-∞` on the zeros of `U`) is
theta-PSH for `-cΘ`: with the local potential `-c log Uₓ'`, the corrected germ is
`c log |hₓ|²`, which is PSH (`plurisubharmonicAt_scaled_generatorLog`).
-/

open Set Filter
open scoped Topology Manifold ContDiff ENNReal

namespace Hironaka.FactorizedWeightPsh

open FactorizedWeightForm

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The extended-real logarithm `log U`, equal to `-∞` where `U ≤ 0`. -/
def logWeight (U : M → ℝ) (y : M) : EReal := ENNReal.log (ENNReal.ofReal (U y))

theorem logWeight_of_pos {U : M → ℝ} {y : M} (hy : 0 < U y) :
    logWeight U y = (Real.log (U y) : EReal) := by
  simp [logWeight, ENNReal.log_ofReal_of_pos hy]

theorem logWeight_ne_bot_of_pos {U : M → ℝ} {y : M} (hy : 0 < U y) : logWeight U y ≠ ⊥ := by
  rw [logWeight_of_pos hy]; exact EReal.coe_ne_bot _

/-- `c (A + r) - c r = c A` in `EReal`, for `c > 0`, `A ≠ ⊤` and `r` real. -/
theorem ereal_mul_add_coe_sub {c : ℝ} (hc : 0 < c) {A : EReal} (hA : A ≠ ⊤) (r : ℝ) :
    (c : EReal) * (A + (r : EReal)) + ((-(c * r) : ℝ) : EReal) = (c : EReal) * A := by
  induction A using EReal.rec with
  | bot =>
    have : (c : EReal) * ⊥ = ⊥ := EReal.coe_mul_bot_of_pos hc
    simp [this]
  | top => exact absurd rfl hA
  | coe a =>
    rw [← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_mul]
    congr 1
    ring

variable {U : M → ℝ} (F : WeightFactorization n U)

/-- **`c log U` is `(-cΘ)`-PSH**, `Θ = F.closedForm`. -/
theorem thetaPlurisubharmonic_logWeight {c : ℝ} (hc : 0 < c) :
    ThetaPlurisubharmonic (-(c • F.closedForm)).val
      (fun y => (c : EReal) * logWeight U y) := by
  intro e z hz
  set x := e.val.symm z
  set W := e.val.target ∩ e.val.symm ⁻¹' F.domain x with hW_def
  have hW : IsOpen W := e.val.isOpen_inter_preimage_symm (F.isOpen_domain x)
  have hzW : z ∈ W := ⟨hz, F.mem_domain x⟩
  have hlog : ContDiffOn ℝ ∞ (fun w => Real.log (F.smoothPart x (e.val.symm w))) W :=
    (F.smooth x e).log fun w hw => (F.pos x _ hw.2).ne'
  refine ⟨W, fun w => -(c * Real.log (F.smoothPart x (e.val.symm w))), hzW,
    ⟨hW, inter_subset_left, (hlog.const_smul c).neg, fun w hw => ?_⟩, ?_⟩
  · change smoothDDC (fun w => -(c • Real.log (F.smoothPart x (e.val.symm w)))) w = _
    rw [smoothDDC_neg hW (hlog.const_smul c) hw, smoothDDC_smul hW hlog c hw,
      ClosedRealOneOneForm.coeff_neg, ClosedRealOneOneForm.coeff_smul,
      (F.closedForm_coeff_eventuallyEq x e hw.1 hw.2).self_of_nhds]
  · let f : Fin 1 → ComplexModel n → ℂ := fun _ w => F.gen x (e.val.symm w)
    intro w hw
    have hgen : HolomorphicGeneratorsAt f w :=
      ⟨W, hW, hw, fun _ w' hw' =>
        (differentiableAt_comp_chart_symm e hw'.1
          (F.gen_mdifferentiable x _ hw'.2)).differentiableWithinAt⟩
    refine (plurisubharmonicAt_scaled_generatorLog hgen hc).congr ?_
    filter_upwards [hW.mem_nhds hw] with w' hw'
    have hs := F.pos x _ hw'.2
    have hfac := F.factor x _ hw'.2
    change (c : EReal) * generatorLog f w' =
      (c : EReal) * logWeight U (e.val.symm w') +
        ((-(c * Real.log (F.smoothPart x (e.val.symm w'))) : ℝ) : EReal)
    have hsplit : logWeight U (e.val.symm w') =
        generatorLog f w' + (Real.log (F.smoothPart x (e.val.symm w')) : EReal) := by
      rw [logWeight, hfac, generatorLog_eq_log_sum, ENNReal.ofReal_mul (Complex.normSq_nonneg _),
        ENNReal.log_mul_add, ENNReal.log_ofReal_of_pos hs]
      simp [f, Complex.normSq_eq_norm_sq]
    rw [hsplit, ereal_mul_add_coe_sub hc (generatorLog_ne_top f w')]

end

end Hironaka.FactorizedWeightPsh
