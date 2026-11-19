import Hironaka.Analytic.PotentialTheory.LogLevi
import Hironaka.Analytic.LocalPotentialIndependence

set_option autoImplicit false

/-!
# The Levi form of `log ‖X + t Y‖²` and `ddᶜ` along a complex line

* `leviForm_log_normSq_line`: for `X, Y` in a complex inner product space with `X + tY ≠ 0`
  for all `t`, the Levi form of `t ↦ log ‖X + tY‖²` at `0` is
  `(‖X‖²‖Y‖² - |⟨X, Y⟩|²) / ‖X‖⁴`;
* `leviForm_log_normSq_line_pos`: it is positive when `Y` is not a multiple of `X`
  (strict Cauchy–Schwarz);
* `leviForm_eq_line`: the Levi form of a function `C²` at `x` in direction `v` only depends
  on its restriction to the complex line `t ↦ x + tv`;
* `quad_smoothDDC_eq_leviForm`: `ddᶜu(v, iv) = L_u(v) / π`.

This is the Fubini–Study positivity used for the Blanchard Kähler form on a blowup: along a
fibre of the exceptional divisor the local weight is `log ‖X + tY‖²` with `X, Y` independent.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace Hironaka.FubiniStudyLineLevi

section Line

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

local instance : InnerProductSpace ℝ H := InnerProductSpace.complexToReal

theorem normSq_line_ne_zero {X Y : H} (hind : ∀ r : ℂ, Y ≠ r • X) (hX : X ≠ 0) (t : ℂ) :
    ‖X + t • Y‖ ^ 2 ≠ 0 := by
  intro h
  have h0 : X + t • Y = 0 := by simpa using h
  by_cases ht : t = 0
  · subst ht; simp at h0; exact hX h0
  · apply hind (-t⁻¹)
    have : t • Y = -X := eq_neg_of_add_eq_zero_right h0
    rw [neg_smul, ← smul_neg, ← this, smul_smul, inv_mul_cancel₀ ht, one_smul]

/-- **The Levi form of `log ‖X + tY‖²`.** -/
theorem leviForm_log_normSq_line {X Y : H} (hind : ∀ r : ℂ, Y ≠ r • X) (hX : X ≠ 0) :
    leviForm (fun t : ℂ => Real.log (‖X + t • Y‖ ^ 2)) 0 1 =
      (‖X‖ ^ 2 * ‖Y‖ ^ 2 - ‖inner ℂ X Y‖ ^ 2) / (‖X‖ ^ 2) ^ 2 := by
  have hs : ContDiff ℝ 2 (fun t : ℂ => ‖X + t • Y‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp (contDiff_const.add
      ((ContinuousLinearMap.id ℂ ℂ).smulRight Y |>.restrictScalars ℝ).contDiff)
  have hz := normSq_line_ne_zero hind hX
  have hH : ∀ a b : ℂ, realHessian (fun t : ℂ => ‖X + t • Y‖ ^ 2) 0 a b =
      2 * inner ℝ (a • Y) (b • Y) := by
    intro a b
    have := realHessian_comp_affine (contDiff_norm_sq ℝ) (complexLineLinear Y) X 0 a b
    simp only [complexLineLinear_apply, zero_smul, add_zero] at this
    rw [this, realHessian_norm_sq]
  have hD : ∀ a : ℂ, fderiv ℝ (fun t : ℂ => ‖X + t • Y‖ ^ 2) 0 a = 2 * inner ℝ X (a • Y) := by
    intro a
    have hA : HasFDerivAt (fun t : ℂ => X + t • Y) (complexLineLinear Y) 0 :=
      (complexLineLinear Y).hasFDerivAt.const_add X
    have := ((hasStrictFDerivAt_norm_sq (X + (0 : ℂ) • Y)).hasFDerivAt.comp 0 hA).fderiv
    show fderiv ℝ ((fun x : H => ‖x‖ ^ 2) ∘ fun t : ℂ => X + t • Y) 0 a = _
    rw [this]
    simp [innerSL_apply_apply, two_smul]
    ring
  have hpair : (inner ℝ X Y) ^ 2 + (inner ℝ X (Complex.I • Y)) ^ 2 =
      ‖inner ℂ X Y‖ ^ 2 := by
    change (inner ℂ X Y).re ^ 2 + (inner ℂ X (Complex.I • Y)).re ^ 2 = _
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [inner_smul_right, Complex.I_mul_re, neg_sq]
    ring
  have hX2 : ‖X + (0 : ℂ) • Y‖ ^ 2 = ‖X‖ ^ 2 := by simp
  have hXp : 0 < ‖X‖ ^ 2 := by positivity
  simp only [leviForm, realHessian_log hs hz, hH, hD, hX2, one_smul,
    real_inner_self_eq_norm_sq, norm_smul, Complex.norm_I, one_mul, smul_eq_mul, mul_one]
  rw [← hpair]
  field_simp
  ring

theorem leviForm_log_normSq_line_pos {X Y : H} (hind : ∀ r : ℂ, Y ≠ r • X) (hX : X ≠ 0) :
    0 < leviForm (fun t : ℂ => Real.log (‖X + t • Y‖ ^ 2)) 0 1 := by
  rw [leviForm_log_normSq_line hind hX]
  have hY : Y ≠ 0 := fun h => hind 0 (by simp [h])
  have hlt : ‖inner ℂ X Y‖ < ‖X‖ * ‖Y‖ := by
    refine lt_of_le_of_ne (norm_inner_le_norm X Y) fun heq => ?_
    obtain ⟨r, -, hr⟩ := (norm_inner_eq_norm_iff (𝕜 := ℂ) hX hY).mp heq
    exact hind r hr
  have h2 : ‖inner ℂ X Y‖ ^ 2 < ‖X‖ ^ 2 * ‖Y‖ ^ 2 := by
    rw [← mul_pow]; exact pow_lt_pow_left₀ hlt (norm_nonneg _) two_ne_zero
  apply div_pos (by linarith)
  positivity

end Line

section Restriction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]

/-- The second derivative along a complex line only needs `C²` at the base point. -/
theorem realHessian_line {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (v : E) (a b : ℂ) :
    realHessian (fun t : ℂ => u (x + t • v)) 0 a b = realHessian u x (a • v) (b • v) := by
  set L := complexLineLinear (E := E) v
  have hA : ∀ t : ℂ, HasFDerivAt (fun t : ℂ => x + t • v) L t := fun t =>
    L.hasFDerivAt.const_add x
  have hx0 : x + (0 : ℂ) • v = x := by simp
  have hcont : ContinuousAt (fun t : ℂ => x + t • v) 0 := (hA 0).continuousAt
  have hdiff : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ u y :=
    (hu.eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp)
  have hdiff' : ∀ᶠ t in 𝓝 (0 : ℂ), DifferentiableAt ℝ u (x + t • v) := by
    rw [← hx0] at hdiff; exact hcont.eventually hdiff
  have h1 : fderiv ℝ (fun t : ℂ => u (x + t • v)) =ᶠ[𝓝 0]
      fun t => (fderiv ℝ u (x + t • v)).comp L := by
    filter_upwards [hdiff'] with t ht
    exact (ht.hasFDerivAt.comp t (hA t)).fderiv
  have hD2 : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hcomp : HasFDerivAt (fun t : ℂ => (fderiv ℝ u (x + t • v)).comp L)
      ((ContinuousLinearMap.compL ℝ ℂ E ℝ).flip L |>.comp ((fderiv ℝ (fderiv ℝ u) x).comp L)) 0 := by
    have h2 : HasFDerivAt (fun t : ℂ => fderiv ℝ u (x + t • v))
        ((fderiv ℝ (fderiv ℝ u) x).comp L) 0 := by
      have hD2' : HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) x) (x + (0 : ℂ) • v) := by
        rw [hx0]; exact hD2.hasFDerivAt
      exact hD2'.comp 0 (hA 0)
    exact ((ContinuousLinearMap.compL ℝ ℂ E ℝ).flip L).hasFDerivAt.comp 0 h2
  rw [realHessian_eq_fderiv, h1.fderiv_eq, hcomp.fderiv, realHessian_eq_fderiv]
  rfl

/-- **The Levi form only depends on the restriction to the complex line.** -/
theorem leviForm_eq_line {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (v : E) :
    leviForm u x v = leviForm (fun t : ℂ => u (x + t • v)) 0 1 := by
  simp only [leviForm, realHessian_line hu, one_smul, smul_eq_mul, mul_one]

end Restriction

/-- `ddᶜu(v, iv) = L_u(v) / π`. -/
theorem quad_smoothDDC_eq_leviForm {n : ℕ} {u : ComplexModel n → ℝ} {z : ComplexModel n}
    (hu : ContDiffAt ℝ 2 u z) (v : ComplexModel n) :
    smoothDDC u z ![v, Complex.I • v] = leviForm u z v / Real.pi := by
  rw [smoothDDC_apply_eq_realHessian hu]
  simp only [smul_smul, Complex.I_mul_I, neg_one_smul]
  rw [show -v = (-1 : ℝ) • v by simp, realHessian_smul_right]
  simp only [leviForm]
  field_simp
  ring

end Hironaka.FubiniStudyLineLevi
