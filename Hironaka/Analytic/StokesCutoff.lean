import Hironaka.Analytic.PotentialTheory.LeviForm
import Hironaka.Manifold.ComplexManifold
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false

/-!
# Smooth cutoffs with almost positive Levi form (TN.4 #4, Stokes against `[V]`)

Source: Demailly, *Complex Analytic and Differential Geometry*, III, Lemma 2.2 b
(`demailly-cadg:III.2.2`) in the analytic case: if `u ≤ 0` is quasi-plurisubharmonic with
`ddᶜu ≥ -C ω` and poles along an analytic set `A`, the functions `χ_m = θ(e^{u/m})` vanish near
`A`, tend to `1` off `A`, and `ddᶜχ_m ≥ -(C θ'(1)/m) ω`.  Blueprint `ana:stokes-cutoffs`
(the cutoffs of the one-sided probe, Remark `ana:stokes-one-sided-probe`).

This module is pointwise and local: the second-order chain rule for a scalar outer function,
its Levi-form version, the explicit convex glue `θ`, and the Levi bound of `θ(e^{u/m})` at a
point where `u` is `C²`.  The global function `u` with poles exactly on `V_sing` is
`ana:stokes-pole-potential`, the next module.

## Main results

* `realHessian_comp` — `D²(θ ∘ f)(a, b) = θ'(f) D²f(a, b) + θ''(f) Df(a) Df(b)`.
* `leviForm_comp`, `mul_leviForm_le_leviForm_comp` — `L(θ ∘ f) = θ'(f) L(f) + θ''(f) |∂f|²`,
  hence `≥ θ'(f) L(f)` when `θ''(f) ≥ 0`; `exp_mul_leviForm_le_leviForm_exp` —
  `L(e^{u/m}) ≥ e^{u/m} L(u)/m`.
* `glue` — `θ(t) = e² exp(-1/(t - 1/2))` for `t > 1/2`, `0` otherwise: smooth, `0` on
  `(-∞, 1/2]`, `θ(1) = 1`, `θ' ≥ 0`, `θ'' ≥ 0` on `(-∞, 1]` (`deriv_deriv_glue_nonneg`),
  `θ'(1) = 4`, `θ'(s) s ≤ 4` on `[0, 1]`.
* `glue_exp_eq_zero`, `glue_exp_le_one`, `tendsto_glue_exp` — `χ_m = 0` where
  `u ≤ -m log 2`, `0 ≤ χ_m ≤ 1`, `χ_m → 1` where `u` is finite.
* `neg_le_leviForm_glue_exp` — if `u ≤ 0` and `L(u)(v) ≥ -c` at `z`, then
  `L(θ(e^{u/m}))(v) ≥ -4c/m` there.
-/


open Set Filter Polynomial
open scoped Topology ContDiff

namespace Hironaka.StokesCutoff



noncomputable section

section ChainRule

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The second-order chain rule** for a scalar outer function, at a point:
`D²(θ ∘ f)(a, b) = θ'(f) D²f(a, b) + θ''(f) Df(a) Df(b)`. -/
theorem realHessian_comp {θ : ℝ → ℝ} {f : E → ℝ} {z : E} (hθ : ContDiffAt ℝ 2 θ (f z))
    (hf : ContDiffAt ℝ 2 f z) (a b : E) :
    realHessian (fun y => θ (f y)) z a b =
      deriv θ (f z) * realHessian f z a b +
        deriv (deriv θ) (f z) * (fderiv ℝ f z a * fderiv ℝ f z b) := by
  have hDf : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ f y :=
    (hf.eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp)
  have hDθ : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ θ (f y) :=
    hf.continuousAt.eventually ((hθ.eventually (by simp)).mono fun t ht =>
      ht.differentiableAt (by simp))
  have hDDf : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hdθ : DifferentiableAt ℝ (deriv θ) (f z) :=
    (hθ.derivWithin (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hev : fderiv ℝ (fun y => θ (f y)) =ᶠ[𝓝 z]
      fun y => deriv θ (f y) • fderiv ℝ f y := by
    filter_upwards [hDf, hDθ] with y hy hθy
    have := (hθy.hasDerivAt.comp_hasFDerivAt y hy.hasFDerivAt).fderiv
    simpa [Function.comp_def] using this
  have hc : HasFDerivAt (fun y => deriv θ (f y))
      (deriv (deriv θ) (f z) • fderiv ℝ f z) z :=
    hdθ.hasDerivAt.comp_hasFDerivAt z (hf.differentiableAt (by simp)).hasFDerivAt
  have hsm : HasFDerivAt (fun y => deriv θ (f y) • fderiv ℝ f y) _ z :=
    hc.smul hDDf.hasFDerivAt
  rw [realHessian_eq_fderiv, hev.fderiv_eq, hsm.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, realHessian_eq_fderiv]
  ring

end ChainRule

section Levi

variable {n : ℕ}

local notation "E" => ComplexModel n

/-- The Levi form of `θ ∘ f`: `L(θ ∘ f) = θ'(f) L(f) + θ''(f) |∂f|²`, with
`|∂f(v)|² = (Df(v)² + Df(iv)²)/4`. -/
theorem leviForm_comp {θ : ℝ → ℝ} {f : E → ℝ} {z : E} (hθ : ContDiffAt ℝ 2 θ (f z))
    (hf : ContDiffAt ℝ 2 f z) (v : E) :
    leviForm (fun y => θ (f y)) z v =
      deriv θ (f z) * leviForm f z v +
        deriv (deriv θ) (f z) *
          ((fderiv ℝ f z v ^ 2 + fderiv ℝ f z (Complex.I • v) ^ 2) / 4) := by
  simp only [leviForm, realHessian_comp hθ hf]
  ring

/-- For an outer function with `θ'' ≥ 0` at the point, `L(θ ∘ f) ≥ θ'(f) L(f)`. -/
theorem mul_leviForm_le_leviForm_comp {θ : ℝ → ℝ} {f : E → ℝ} {z : E}
    (hθ : ContDiffAt ℝ 2 θ (f z)) (hf : ContDiffAt ℝ 2 f z)
    (hθ2 : 0 ≤ deriv (deriv θ) (f z)) (v : E) :
    deriv θ (f z) * leviForm f z v ≤ leviForm (fun y => θ (f y)) z v := by
  rw [leviForm_comp hθ hf]
  have : 0 ≤ deriv (deriv θ) (f z) *
      ((fderiv ℝ f z v ^ 2 + fderiv ℝ f z (Complex.I • v) ^ 2) / 4) := by positivity
  linarith

/-- `L(e^{u/m}) ≥ e^{u/m} L(u)/m`. -/
theorem exp_mul_leviForm_le_leviForm_exp {u : E → ℝ} {z : E} (hu : ContDiffAt ℝ 2 u z)
    {m : ℝ} (v : E) :
    Real.exp (u z / m) * (leviForm u z v / m) ≤
      leviForm (fun y => Real.exp (u y / m)) z v := by
  have hf : ContDiffAt ℝ 2 (fun y => u y / m) z := hu.div_const m
  have h := mul_leviForm_le_leviForm_comp (θ := Real.exp) (f := fun y => u y / m)
    Real.contDiff_exp.contDiffAt hf (by simp [Real.exp_pos, le_of_lt]) v
  have hL : leviForm (fun y => u y / m) z v = leviForm u z v / m := by
    have : (fun y => u y / m) = m⁻¹ • u := by
      funext y; simp [div_eq_inv_mul]
    rw [this, leviForm_smul hu]
    ring
  simpa [Real.deriv_exp, hL] using h

end Levi

/-! ### The convex glue `θ` -/

/-- The convex glue: `θ(t) = e² exp(-1/(t - 1/2))` for `t > 1/2`, `0` otherwise. -/
def glue (t : ℝ) : ℝ := Real.exp 2 * expNegInvGlue (t - 1 / 2)

theorem contDiff_glue {k : ℕ∞} : ContDiff ℝ k glue :=
  contDiff_const.mul (expNegInvGlue.contDiff.comp (contDiff_id.sub contDiff_const))

theorem glue_eq_zero {t : ℝ} (ht : t ≤ 1 / 2) : glue t = 0 := by
  rw [glue, expNegInvGlue.zero_of_nonpos (by linarith : t - 1 / 2 ≤ 0), mul_zero]

theorem glue_nonneg (t : ℝ) : 0 ≤ glue t :=
  mul_nonneg (Real.exp_pos 2).le (expNegInvGlue.nonneg _)

theorem glue_one : glue 1 = 1 := by
  have h : expNegInvGlue (1 - 1 / 2) = Real.exp (-2) := by
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
    simp only [expNegInvGlue, show ¬ (1 / 2 : ℝ) ≤ 0 by norm_num, if_false]
    norm_num
  rw [glue, h, ← Real.exp_add]
  norm_num

/-- First derivative of `expNegInvGlue`: `x⁻² g(x)`. -/
theorem hasDerivAt_expNegInvGlue (x : ℝ) :
    HasDerivAt expNegInvGlue ((x⁻¹) ^ 2 * expNegInvGlue x) x := by
  have h := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : ℝ[X]) x
  simp only [eval_one, one_mul, derivative_one, sub_zero, mul_one, eval_pow, eval_X] at h
  exact h

theorem deriv_expNegInvGlue : deriv expNegInvGlue = fun x => (x⁻¹) ^ 2 * expNegInvGlue x :=
  funext fun x => (hasDerivAt_expNegInvGlue x).deriv

/-- Second derivative of `expNegInvGlue`: `(x⁻⁴ - 2 x⁻³) g(x)`. -/
theorem deriv_deriv_expNegInvGlue (x : ℝ) :
    deriv (deriv expNegInvGlue) x = ((x⁻¹) ^ 2 * ((x⁻¹) ^ 2 - 2 * x⁻¹)) * expNegInvGlue x := by
  rw [deriv_expNegInvGlue]
  have h := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul ((X : ℝ[X]) ^ 2) x
  simp only [eval_pow, eval_X, eval_mul, eval_sub, derivative_X_pow, eval_C] at h
  convert h.deriv using 1
  simp

theorem hasDerivAt_glue (t : ℝ) :
    HasDerivAt glue (Real.exp 2 * (((t - 1 / 2)⁻¹) ^ 2 * expNegInvGlue (t - 1 / 2))) t := by
  have h1 := (hasDerivAt_expNegInvGlue (t - 1 / 2)).comp t ((hasDerivAt_id t).sub_const (1 / 2))
  have h2 := h1.const_mul (Real.exp 2)
  rw [mul_one] at h2
  exact h2

theorem deriv_glue (t : ℝ) :
    deriv glue t = Real.exp 2 * (((t - 1 / 2)⁻¹) ^ 2 * expNegInvGlue (t - 1 / 2)) :=
  (hasDerivAt_glue t).deriv

theorem deriv_glue_nonneg (t : ℝ) : 0 ≤ deriv glue t := by
  rw [deriv_glue]
  have := expNegInvGlue.nonneg (t - 1 / 2)
  positivity

theorem deriv_deriv_glue (t : ℝ) :
    deriv (deriv glue) t = Real.exp 2 *
      ((((t - 1 / 2)⁻¹) ^ 2 * (((t - 1 / 2)⁻¹) ^ 2 - 2 * (t - 1 / 2)⁻¹)) *
        expNegInvGlue (t - 1 / 2)) := by
  have hd : deriv glue = fun s => Real.exp 2 * (deriv expNegInvGlue (s - 1 / 2)) := by
    funext s; rw [deriv_glue, deriv_expNegInvGlue]
  rw [hd]
  have hdd : HasDerivAt (deriv expNegInvGlue)
      (deriv (deriv expNegInvGlue) (t - 1 / 2)) (t - 1 / 2) := by
    refine (DifferentiableAt.hasDerivAt ?_)
    exact ((expNegInvGlue.contDiff (n := 2)).differentiable_deriv_two) _
  have h := ((hdd.comp t ((hasDerivAt_id t).sub_const (1 / 2))).const_mul (Real.exp 2))
  rw [show (fun s => Real.exp 2 * deriv expNegInvGlue (s - 1 / 2)) =
      fun s => Real.exp 2 * (deriv expNegInvGlue ∘ fun s => id s - 1 / 2) s from rfl,
    h.deriv, deriv_deriv_expNegInvGlue]
  simp

/-- `θ'' ≥ 0` on `(-∞, 1]`: the glue is convex there. -/
theorem deriv_deriv_glue_nonneg {t : ℝ} (ht : t ≤ 1) : 0 ≤ deriv (deriv glue) t := by
  rcases le_or_gt (t - 1 / 2) 0 with h | h
  · rw [deriv_deriv_glue, expNegInvGlue.zero_of_nonpos h]
    simp
  · rw [deriv_deriv_glue]
    have hs : (t - 1 / 2)⁻¹ ≥ 2 := by
      rw [ge_iff_le, le_inv_comm₀ (by norm_num) h]; linarith
    have h1 : 0 ≤ ((t - 1 / 2)⁻¹) ^ 2 - 2 * (t - 1 / 2)⁻¹ := by nlinarith
    have := expNegInvGlue.nonneg (t - 1 / 2)
    positivity

theorem deriv_glue_one : deriv glue 1 = 4 := by
  rw [deriv_glue]
  have h : expNegInvGlue (1 - 1 / 2) = Real.exp (-2) := by
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
    simp only [expNegInvGlue, show ¬ (1 / 2 : ℝ) ≤ 0 by norm_num, if_false]
    norm_num
  rw [h, show ((1 : ℝ) - 1 / 2)⁻¹ = 2 by norm_num]
  have : Real.exp 2 * Real.exp (-2) = 1 := by rw [← Real.exp_add]; norm_num
  nlinarith [this]

theorem monotoneOn_deriv_glue : MonotoneOn (deriv glue) (Iic 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Iic 1)
  · exact ((contDiff_glue (k := 2)).continuous_deriv (by norm_num)).continuousOn
  · exact ((contDiff_glue (k := 2)).differentiable_deriv_two).differentiableOn
  · intro t ht
    rw [interior_Iic] at ht
    exact deriv_deriv_glue_nonneg (le_of_lt ht)

/-- `0 ≤ θ'(s) s ≤ θ'(1) = 4` for `0 ≤ s ≤ 1`. -/
theorem deriv_glue_mul_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : deriv glue s * s ≤ 4 := by
  have h1 : deriv glue s ≤ deriv glue 1 :=
    monotoneOn_deriv_glue (mem_Iic.2 hs1) (mem_Iic.2 le_rfl) hs1
  have h0 := deriv_glue_nonneg s
  rw [deriv_glue_one] at h1
  nlinarith

theorem monotone_glue : Monotone glue :=
  monotone_of_deriv_nonneg (contDiff_glue (k := 1)).differentiable_one deriv_glue_nonneg

theorem glue_le_one {t : ℝ} (ht : t ≤ 1) : glue t ≤ 1 :=
  glue_one ▸ monotone_glue ht

/-! ### The cutoffs `θ(e^{u/m})` -/

/-- The cutoff vanishes where `u ≤ -m log 2`. -/
theorem glue_exp_eq_zero {t m : ℝ} (hm : 0 < m) (ht : t ≤ -(m * Real.log 2)) :
    glue (Real.exp (t / m)) = 0 := by
  apply glue_eq_zero
  have h1 : t / m ≤ -Real.log 2 := by
    rw [div_le_iff₀ hm]; linarith
  calc Real.exp (t / m) ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.2 h1
    _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num

theorem glue_exp_nonneg (t m : ℝ) : 0 ≤ glue (Real.exp (t / m)) := glue_nonneg _

theorem glue_exp_le_one {t m : ℝ} (hm : 0 < m) (ht : t ≤ 0) : glue (Real.exp (t / m)) ≤ 1 :=
  glue_le_one (Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg ht hm.le))

/-- At every point where `u` is finite the cutoffs tend to `1`. -/
theorem tendsto_glue_exp (t : ℝ) :
    Tendsto (fun m : ℕ => glue (Real.exp (t / m))) atTop (𝓝 1) := by
  have h1 : Tendsto (fun m : ℕ => t / (m : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun m : ℕ => Real.exp (t / m)) atTop (𝓝 1) := by
    have := (Real.continuous_exp.tendsto 0).comp h1
    rw [Real.exp_zero] at this
    exact this
  have := ((contDiff_glue (k := 0)).continuous.tendsto 1).comp h2
  rw [glue_one] at this
  exact this

section CutoffLevi

variable {n : ℕ}

local notation "E" => ComplexModel n

/-- **The Levi bound of the cutoffs** (`demailly-cadg:III.2.2`, analytic case): if `u ≤ 0` at
`z` and `L(u)(v) ≥ -c`, then `L(θ(e^{u/m}))(v) ≥ -4c/m`; `4 = θ'(1)`. -/
theorem neg_le_leviForm_glue_exp {u : E → ℝ} {z : E} (hu : ContDiffAt ℝ 2 u z)
    (hu0 : u z ≤ 0) {m : ℝ} (hm : 0 < m) {c : ℝ} (hc : 0 ≤ c) (v : E)
    (hL : -c ≤ leviForm u z v) :
    -(4 * c / m) ≤ leviForm (fun y => glue (Real.exp (u y / m))) z v := by
  have hg : ContDiffAt ℝ 2 (fun y => Real.exp (u y / m)) z :=
    Real.contDiff_exp.contDiffAt.comp z (hu.div_const m)
  set g0 := Real.exp (u z / m) with hg0
  have hg0pos : 0 < g0 := Real.exp_pos _
  have hg0le : g0 ≤ 1 := Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg hu0 hm.le)
  have h1 := mul_leviForm_le_leviForm_comp (θ := glue) (f := fun y => Real.exp (u y / m))
    (contDiff_glue (k := 2)).contDiffAt hg (deriv_deriv_glue_nonneg hg0le) v
  have h2 := exp_mul_leviForm_le_leviForm_exp (z := z) hu (m := m) v
  have hd0 := deriv_glue_nonneg g0
  have hd4 := deriv_glue_mul_le hg0pos.le hg0le
  have hLm : -(c / m) ≤ leviForm u z v / m := by
    rw [← neg_div]; exact div_le_div_of_nonneg_right hL hm.le
  -- θ'(g0) L(g) ≥ θ'(g0) g0 L(u)/m ≥ -θ'(g0) g0 c/m ≥ -4c/m
  have h3 : deriv glue g0 * (g0 * (leviForm u z v / m)) ≤
      deriv glue g0 * leviForm (fun y => Real.exp (u y / m)) z v :=
    mul_le_mul_of_nonneg_left h2 hd0
  have h4 : deriv glue g0 * g0 * (-(c / m)) ≤ deriv glue g0 * g0 * (leviForm u z v / m) :=
    mul_le_mul_of_nonneg_left hLm (mul_nonneg hd0 hg0pos.le)
  have h5 : -(4 * c / m) ≤ deriv glue g0 * g0 * (-(c / m)) := by
    have hcm : 0 ≤ c / m := div_nonneg hc hm.le
    have : deriv glue g0 * g0 * (c / m) ≤ 4 * (c / m) := mul_le_mul_of_nonneg_right hd4 hcm
    have e : 4 * c / m = 4 * (c / m) := by ring
    linarith
  have e2 : deriv glue g0 * (g0 * (leviForm u z v / m)) =
      deriv glue g0 * g0 * (leviForm u z v / m) := by ring
  linarith

end CutoffLevi

end

end Hironaka.StokesCutoff
