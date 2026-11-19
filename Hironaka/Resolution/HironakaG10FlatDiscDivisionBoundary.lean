import Hironaka.Resolution.HironakaG10FlatDiscWeierstrassDivision

/-! # Weierstrass division with the contour on the boundary of the disc

Continuation of `HironakaG10FlatDiscWeierstrassDivision` for functions that are only
CONTINUOUS on the closed disc `D̄(0,ρ)` and holomorphic on the open disc (the fibres of an
element of `B(K' × D̄(0,ρ))`): the Cauchy division with the contour `|ζ| = ρ` still gives
`h = W q + ∑_{i<b} rᵢ wⁱ` on `D(0,ρ)` (`division_eq_of_continuousOn`), the quotient is
holomorphic on `D(0,ρ)` (`differentiableOn_divQuot_slice_of_continuousOn`, a Cauchy-type
integral of a continuous density), and if `W(z,·)` is monic of degree `b` with all roots in
`D(0,ρ)` every such division is this one (`eq_divQuot_remCoeff_of_continuousOn`).
This is the fibrewise division of elements of `B(K)` needed for privilege of polydiscs.
BP: hironaka-g10-flat-disc-division-boundary.tex. -/
set_option autoImplicit false
namespace Hironaka.HironakaG10FlatDiscDivisionBoundary
open Complex Metric Set Filter
open scoped Real Topology NNReal
open HironakaG10FlatDiscWeierstrassDivision
noncomputable section

variable {P : Type*} {b : ℕ} {A : ℕ → P → ℂ} {h : P × ℂ → ℂ} {ρ : ℝ}

/-- **Division with the contour on the boundary.** -/
theorem division_eq_of_continuousOn (hρ : 0 < ρ) (z : P)
    (hc : ContinuousOn (fun ζ => h (z, ζ)) (closedBall 0 ρ))
    (hd : DifferentiableOn ℂ (fun ζ => h (z, ζ)) (ball 0 ρ))
    (hW : ∀ ζ ∈ sphere (0 : ℂ) ρ, polyEval b A z ζ ≠ 0) {w : ℂ} (hw : w ∈ ball (0 : ℂ) ρ) :
    h (z, w) = polyEval b A z w * divQuot b A h ρ (z, w) + divRem b A h ρ (z, w) := by
  set f : ℂ → ℂ := fun ζ => h (z, ζ) with hf
  have hcauchy : (∮ ζ in C(0, ρ), f ζ / (ζ - w)) = 2 * π * I * f w :=
    circleIntegral_div_sub_of_differentiable_on_off_countable countable_empty hw hc
      fun ζ hζ => hd.differentiableAt (isOpen_ball.mem_nhds hζ.1)
  have hne : ∀ ζ ∈ sphere (0 : ℂ) ρ, ζ - w ≠ 0 := by
    intro ζ hζ h0
    rw [sub_eq_zero] at h0
    rw [h0, mem_sphere_zero_iff_norm] at hζ
    rw [mem_ball_zero_iff, hζ] at hw
    exact lt_irrefl _ hw
  have hfc : ContinuousOn f (sphere 0 ρ) := hc.mono sphere_subset_closedBall
  have hWc : ContinuousOn (polyEval b A z) (sphere 0 ρ) := (continuous_polyEval b A z).continuousOn
  have hpt : EqOn (fun ζ => f ζ / (ζ - w))
      (fun ζ => polyEval b A z w * (f ζ / (polyEval b A z ζ * (ζ - w))) +
        ∑ i ∈ Finset.range b, w ^ i * (f ζ * diffCoeff b A i z ζ / polyEval b A z ζ))
      (sphere 0 ρ) := by
    intro ζ hζ
    have hW0 := hW ζ hζ
    have hw0 := hne ζ hζ
    have hid := polyEval_sub_eq b A z ζ w
    simp only
    rw [show (∑ i ∈ Finset.range b, w ^ i * (f ζ * diffCoeff b A i z ζ / polyEval b A z ζ)) =
        f ζ / polyEval b A z ζ * ∑ i ∈ Finset.range b, diffCoeff b A i z ζ * w ^ i by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring]
    field_simp
    linear_combination (f ζ) * hid
  have hint₀ : CircleIntegrable
      (fun ζ => polyEval b A z w * (f ζ / (polyEval b A z ζ * (ζ - w)))) 0 ρ :=
    (continuousOn_const.mul (hfc.div (hWc.mul (continuousOn_id.sub continuousOn_const))
      fun ζ hζ => mul_ne_zero (hW ζ hζ) (hne ζ hζ))).circleIntegrable hρ.le
  have hcontᵢ : ∀ i ∈ Finset.range b, ContinuousOn
      (fun ζ => w ^ i * (f ζ * diffCoeff b A i z ζ / polyEval b A z ζ)) (sphere 0 ρ) :=
    fun i _ => continuousOn_const.mul ((hfc.mul (continuous_diffCoeff b A i z).continuousOn).div
      hWc fun ζ hζ => hW ζ hζ)
  have hintᵢ : ∀ i ∈ Finset.range b, CircleIntegrable
      (fun ζ => w ^ i * (f ζ * diffCoeff b A i z ζ / polyEval b A z ζ)) 0 ρ :=
    fun i hi => (hcontᵢ i hi).circleIntegrable hρ.le
  have hintS : CircleIntegrable (fun ζ => ∑ i ∈ Finset.range b,
      w ^ i * (f ζ * diffCoeff b A i z ζ / polyEval b A z ζ)) 0 ρ :=
    (continuousOn_finsetSum _ hcontᵢ).circleIntegrable hρ.le
  rw [circleIntegral.integral_congr hρ.le hpt, circleIntegral.integral_add hint₀ hintS,
    circleIntegral.integral_const_mul, circleIntegral.integral_fun_sum hintᵢ] at hcauchy
  simp only [circleIntegral.integral_const_mul] at hcauchy
  have h2pi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  have hfw : f w = (2 * π * I)⁻¹ * (2 * π * I * f w) := by field_simp
  rw [show h (z, w) = f w from rfl, hfw, ← hcauchy, divRem, divQuot, mul_add, Finset.mul_sum]
  simp only [remCoeff]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun i _ => by ring

/-- The quotient of a function merely continuous on the circle is holomorphic on the open disc
(Cauchy-type integral of a continuous density). -/
theorem differentiableOn_divQuot_slice_of_continuousOn (hρ : 0 < ρ) (z : P)
    (hc : ContinuousOn (fun ζ => h (z, ζ)) (sphere 0 ρ))
    (hW : ∀ ζ ∈ sphere (0 : ℂ) ρ, polyEval b A z ζ ≠ 0) :
    DifferentiableOn ℂ (fun w => divQuot b A h ρ (z, w)) (ball 0 ρ) := by
  set g : ℂ → ℂ := fun ζ => h (z, ζ) / polyEval b A z ζ with hg
  have hgi : CircleIntegrable g 0 ρ :=
    (hc.div (continuous_polyEval b A z).continuousOn hW).circleIntegrable hρ.le
  let R : ℝ≥0 := ⟨ρ, hρ.le⟩
  have hgi' : CircleIntegrable g 0 R := hgi
  have hser := hasFPowerSeriesOn_cauchy_integral hgi' (by exact_mod_cast hρ)
  have hd := hser.differentiableOn
  have heq : ∀ w, divQuot b A h ρ (z, w) =
      (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(0, (R : ℝ)), (ζ - w)⁻¹ • g ζ := by
    intro w
    rw [divQuot, smul_eq_mul]
    congr 1
    refine circleIntegral.integral_congr hρ.le fun ζ _ => ?_
    simp only [hg, smul_eq_mul]
    rw [div_mul_eq_div_div_swap, div_eq_inv_mul]
    simp only [div_eq_mul_inv]
    ring
  intro w hw
  have hwR : w ∈ Metric.eball (0 : ℂ) R := by
    rw [Metric.eball_coe]
    exact hw
  have := (hd w hwR).differentiableAt (Metric.isOpen_eball.mem_nhds hwR)
  refine (this.congr_of_eventuallyEq (Eventually.of_forall fun w' => heq w')).differentiableWithinAt

/-- **Uniqueness for boundary-continuous functions.** If `W(z,·)` is monic of degree `b` with
all its roots in `D(0,ρ)`, every division `h(z,·) = W q + ∑_{i<b} cᵢ wⁱ` on `D(0,ρ)` with `q`
continuous is the Cauchy division with the contour `|ζ| = ρ`. -/
theorem eq_divQuot_remCoeff_of_continuousOn (hρ : 0 < ρ) (z : P)
    (hc : ContinuousOn (fun ζ => h (z, ζ)) (closedBall 0 ρ))
    (hd : DifferentiableOn ℂ (fun ζ => h (z, ζ)) (ball 0 ρ)) (hmon : A b z = 1)
    (hroots : ∀ α, polyEval b A z α = 0 → α ∈ ball (0 : ℂ) ρ)
    (q : ℂ → ℂ) (hq : ContinuousOn q (ball 0 ρ)) (c : ℕ → ℂ)
    (hdiv : ∀ w ∈ ball (0 : ℂ) ρ, h (z, w) = polyEval b A z w * q w +
      ∑ i ∈ Finset.range b, c i * w ^ i) :
    (∀ i < b, c i = remCoeff b A h ρ i z) ∧ EqOn q (fun w => divQuot b A h ρ (z, w)) (ball 0 ρ) := by
  have hW : ∀ ζ ∈ sphere (0 : ℂ) ρ, polyEval b A z ζ ≠ 0 := by
    intro ζ hζ h0
    have := hroots ζ h0
    rw [mem_ball_zero_iff, mem_sphere_zero_iff_norm.mp hζ] at this
    exact lt_irrefl _ this
  have hq₀ : ContinuousOn (fun w => divQuot b A h ρ (z, w)) (ball 0 ρ) :=
    (differentiableOn_divQuot_slice_of_continuousOn hρ z (hc.mono sphere_subset_closedBall)
      hW).continuousOn
  have hroots' : ∀ α, (toPoly b A z).IsRoot α → α ∈ ball (0 : ℂ) ρ := by
    intro α hα
    apply hroots α
    rw [← eval_toPoly hmon]
    exact hα
  refine division_unique (toPoly b A z) (toPoly_monic b A z) (toPoly_natDegree b A z) hroots'
    q _ hq hq₀ c (fun i => remCoeff b A h ρ i z) fun w hw => ?_
  rw [eval_toPoly hmon, mul_comm (q w), mul_comm (divQuot b A h ρ (z, w)), ← hdiv w hw]
  exact division_eq_of_continuousOn hρ z hc hd hW hw

end
end Hironaka.HironakaG10FlatDiscDivisionBoundary
