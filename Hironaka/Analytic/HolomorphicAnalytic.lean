/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Manifold.HolomorphicContDiff
import Mathlib.Analysis.Complex.TaylorSeries
set_option autoImplicit false

/-!
# Holomorphic functions of several complex variables are analytic

Let `E` be a finite-dimensional complex normed space and `F` a complex Banach space. A map
`f : E → F` that is complex differentiable on an open set `U` is analytic on `U`
(`analyticOnNhd_of_differentiableOn`). Mathlib has this only for `E = ℂ`.

The proof avoids several-variable Cauchy integrals. By
`Hironaka.contDiffOn_of_differentiableOn_complex`, `f` is `C^∞`, and the candidate power
series at `c` is `pₙ = (n!)⁻¹ • D^n f(c)`.

* `norm_iteratedFDeriv_le_of_forall_norm_le`: if `‖f‖ ≤ M` on `ball c R`, then
  `‖D^k f(w)‖ ≤ M / δ^k` on `ball c (R - k δ)`. Induction on `k`, using the one-variable Cauchy
  estimate for the Banach-valued map `D^k f` (`Hironaka.norm_fderiv_le_of_forall_norm_le`)
  and `‖D (D^k f)‖ = ‖D^{k+1} f‖`. With `δ = R / (n + 1)` this gives
  `‖D^n f(c)‖ ≤ M ((n+1)/R)^n`, and `(n+1)^n / n! ≤ e^{n+1}` bounds the radius below by `R/e`.
* `iteratedDeriv_comp_line`: along the complex line `t ↦ c + t • y`,
  `(d/dt)^n f(c + t y)|_{t=0} = D^n f(c)(y, …, y)`.
* `hasFPowerSeriesOnBall_of_differentiableOn`: the one-variable Taylor expansion of
  `t ↦ f (c + t • y)` (`Complex.hasSum_taylorSeries_on_ball`) evaluated at `t = 1` shows that
  the series sums to `f (c + y)` for `‖y‖ < R / e`.
-/

open Filter Metric Set
open scoped Topology ContDiff Nat

namespace Hironaka.HolomorphicAnalytic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Cauchy estimates for the iterated derivatives of a bounded holomorphic map: if `f` is
holomorphic and bounded by `M` on `ball c R`, then `‖D^k f(w)‖ ≤ M / δ ^ k` for
`w ∈ ball c (R - k δ)`. -/
theorem norm_iteratedFDeriv_le_of_forall_norm_le [FiniteDimensional ℂ E] [CompleteSpace F]
    {f : E → F} {c : E} {R M δ : ℝ} (hf : DifferentiableOn ℂ f (ball c R))
    (hM : ∀ w ∈ ball c R, ‖f w‖ ≤ M) (hδ : 0 < δ) (k : ℕ) :
    ∀ w ∈ ball c (R - k * δ), ‖iteratedFDeriv ℂ k f w‖ ≤ M / δ ^ k := by
  have hcd := Hironaka.contDiffOn_of_differentiableOn_complex hf isOpen_ball
  induction k with
  | zero =>
    intro w hw
    simpa using hM w (by simpa using hw)
  | succ k ih =>
    intro w hw
    rw [mem_ball] at hw
    push_cast at hw
    set R' := R - k * δ - dist w c with hR'
    have hsub : ball w R' ⊆ ball c (R - k * δ) := by
      intro z hz
      rw [mem_ball] at hz ⊢
      linarith [dist_triangle z w c]
    have hwR : ∀ z ∈ ball w R', z ∈ ball c R := by
      intro z hz
      have := hsub hz
      rw [mem_ball] at this ⊢
      nlinarith [hδ, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hdiff : DifferentiableOn ℂ (iteratedFDeriv ℂ k f) (ball w R') := by
      intro z hz
      refine DifferentiableAt.differentiableWithinAt ?_
      exact (hcd.contDiffAt (isOpen_ball.mem_nhds (hwR z hz))).differentiableAt_iteratedFDeriv
        (by exact_mod_cast WithTop.coe_lt_top _)
    have hbd := Hironaka.norm_fderiv_le_of_forall_norm_le hdiff (fun z hz => ih z (hsub hz))
      hδ (by rw [hR']; linarith)
    rw [norm_fderiv_iteratedFDeriv] at hbd
    calc ‖iteratedFDeriv ℂ (k + 1) f w‖ ≤ M / δ ^ k / δ := hbd
      _ = M / δ ^ (k + 1) := by rw [pow_succ, div_div]

/-- Along the complex line `t ↦ c + t • y`, the `n`-th derivative at `t = 0` is
`D^n f(c)(y, …, y)`. -/
theorem iteratedDeriv_comp_line {f : E → F} {s : Set E} (hs : IsOpen s)
    (hf : ContDiffOn ℂ ∞ f s) {c : E} (hc : c ∈ s) (y : E) (n : ℕ) :
    iteratedDeriv n (fun t : ℂ => f (c + t • y)) 0 = iteratedFDeriv ℂ n f c (fun _ => y) := by
  set g : E → F := fun z => f (c + z) with hg
  set s' : Set E := (fun z => c + z) ⁻¹' s with hs'
  have hs'o : IsOpen s' := hs.preimage (continuous_const.add continuous_id)
  have hgc : ContDiffOn ℂ ∞ g s' :=
    hf.comp (contDiff_const.add contDiff_id).contDiffOn (fun z hz => hz)
  set A : ℂ →L[ℂ] E := ContinuousLinearMap.toSpanSingleton ℂ y with hA
  have hcomp : (fun t : ℂ => f (c + t • y)) = g ∘ A := by
    funext t
    simp [hg, hA]
  have h0 : (0 : ℂ) ∈ A ⁻¹' s' := by simpa [hs', hA] using hc
  have hA0 : A 0 ∈ s' := h0
  have hopen : IsOpen (A ⁻¹' s') := hs'o.preimage A.continuous
  rw [iteratedDeriv_eq_iteratedFDeriv, hcomp,
    ← iteratedFDerivWithin_of_isOpen n hopen h0,
    A.iteratedFDerivWithin_comp_right hgc hs'o.uniqueDiffOn hopen.uniqueDiffOn hA0
      (by exact_mod_cast le_top),
    iteratedFDerivWithin_of_isOpen n hs'o hA0]
  simp [hg, hA, iteratedFDeriv_comp_add_left]

/-- Cauchy estimates for the Taylor coefficients: if `f` is holomorphic and bounded by `M` on
`ball c R`, then `‖(n!)⁻¹ • D^n f(c)‖ ≤ M e (e / R)^n`. -/
theorem norm_factorial_inv_smul_iteratedFDeriv_le [FiniteDimensional ℂ E] [CompleteSpace F]
    {f : E → F} {c : E} {R M : ℝ} (hR : 0 < R) (hf : DifferentiableOn ℂ f (ball c R))
    (hM : ∀ w ∈ ball c R, ‖f w‖ ≤ M) (n : ℕ) :
    ‖((n ! : ℂ)⁻¹ • iteratedFDeriv ℂ n f c)‖ ≤ M * Real.exp 1 * (Real.exp 1 / R) ^ n := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM c (mem_ball_self hR))
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  set δ : ℝ := R / (n + 1) with hδ
  have hδ0 : 0 < δ := div_pos hR hn1
  have hc : c ∈ ball c (R - n * δ) := by
    rw [mem_ball, dist_self, hδ]
    rw [show R - n * (R / (n + 1)) = R / (n + 1) by field_simp; ring]
    exact div_pos hR hn1
  have hbd := norm_iteratedFDeriv_le_of_forall_norm_le hf hM hδ0 n c hc
  have hfac : ((n : ℝ) + 1) ^ n / (n ! : ℝ) ≤ Real.exp 1 * Real.exp 1 ^ n := by
    have h := Real.pow_div_factorial_le_exp (x := (n : ℝ) + 1) hn1.le (n + 1)
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    calc ((n : ℝ) + 1) ^ n / (n ! : ℝ) = ((n : ℝ) + 1) ^ (n + 1) / ((n + 1)! : ℕ) := by
          rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]; push_cast
          field_simp
      _ ≤ Real.exp ((n : ℝ) + 1) := h
      _ = Real.exp (1 + n * 1) := by ring_nf
  rw [norm_smul, norm_inv, Complex.norm_natCast]
  have hfac0 : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  calc (n ! : ℝ)⁻¹ * ‖iteratedFDeriv ℂ n f c‖ ≤ (n ! : ℝ)⁻¹ * (M / δ ^ n) := by gcongr
    _ = M * (((n : ℝ) + 1) ^ n / (n ! : ℝ)) / R ^ n := by
          rw [hδ, div_pow]; field_simp
    _ ≤ M * (Real.exp 1 * Real.exp 1 ^ n) / R ^ n := by gcongr
    _ = M * Real.exp 1 * (Real.exp 1 / R) ^ n := by rw [div_pow]; ring

/-- A map holomorphic and bounded on `ball c R` in a finite-dimensional space has the power
series `(n!)⁻¹ • D^n f(c)` on the ball of radius `R / e`. -/
theorem hasFPowerSeriesOnBall_of_differentiableOn [FiniteDimensional ℂ E] [CompleteSpace F]
    {f : E → F} {c : E} {R M : ℝ} (hR : 0 < R) (hf : DifferentiableOn ℂ f (ball c R))
    (hM : ∀ w ∈ ball c R, ‖f w‖ ≤ M) :
    HasFPowerSeriesOnBall f (fun n => (n ! : ℂ)⁻¹ • iteratedFDeriv ℂ n f c) c
      (ENNReal.ofReal (R / Real.exp 1)) := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM c (mem_ball_self hR))
  have hcd := Hironaka.contDiffOn_of_differentiableOn_complex hf isOpen_ball
  refine ⟨?_, ENNReal.ofReal_pos.2 (div_pos hR he), ?_⟩
  · refine FormalMultilinearSeries.le_radius_of_bound _ (M * Real.exp 1) fun n => ?_
    have h := norm_factorial_inv_smul_iteratedFDeriv_le hR hf hM n
    rw [Real.coe_toNNReal _ (div_pos hR he).le]
    calc ‖((n ! : ℂ)⁻¹ • iteratedFDeriv ℂ n f c)‖ * (R / Real.exp 1) ^ n
        ≤ M * Real.exp 1 * (Real.exp 1 / R) ^ n * (R / Real.exp 1) ^ n := by gcongr
      _ = M * Real.exp 1 := by
          rw [mul_assoc, ← mul_pow, div_mul_div_comm, mul_comm (Real.exp 1) R,
            div_self (by positivity), one_pow, mul_one]
  · intro y hy
    have hyR : ‖y‖ < R := by
      rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm,
        ENNReal.ofReal_lt_ofReal_iff (div_pos hR he)] at hy
      have h1 : R / Real.exp 1 ≤ R := div_le_self hR.le (Real.one_le_exp zero_le_one)
      exact hy.trans_le h1
    set T : ℝ := 2 * R / (R + ‖y‖) with hT
    have hRy : 0 < R + ‖y‖ := by positivity
    have hT1 : 1 < T := by rw [hT, lt_div_iff₀ hRy]; linarith
    have hTy : T * ‖y‖ < R := by
      rw [hT, div_mul_eq_mul_div, div_lt_iff₀ hRy]; nlinarith [norm_nonneg y]
    have hg : DifferentiableOn ℂ (fun t : ℂ => f (c + t • y)) (ball 0 T) := by
      refine hf.comp (by fun_prop : Differentiable ℂ fun t : ℂ => c + t • y).differentiableOn
        fun t ht => ?_
      rw [mem_ball, dist_zero_right] at ht
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
      calc ‖t‖ * ‖y‖ ≤ T * ‖y‖ := by gcongr
        _ < R := hTy
    have h1 : (1 : ℂ) ∈ ball (0 : ℂ) T := by simpa using hT1
    have hs := Complex.hasSum_taylorSeries_on_ball hg h1
    simp only [sub_zero, one_pow, one_smul] at hs
    convert hs using 1
    · funext n
      rw [iteratedDeriv_comp_line isOpen_ball hcd (mem_ball_self hR)]
      simp

/-- A complex differentiable map on an open subset of a finite-dimensional complex normed
space, with values in a complex Banach space, is analytic at every point of the set. -/
theorem analyticAt_of_differentiableOn [FiniteDimensional ℂ E] [CompleteSpace F]
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {c : E}
    (hc : c ∈ U) : AnalyticAt ℂ f c := by
  have hcont : ContinuousAt (fun z => ‖f z‖) c :=
    continuous_norm.continuousAt.comp (hf.continuousOn.continuousAt (hU.mem_nhds hc))
  have hev : ∀ᶠ z in 𝓝 c, z ∈ U ∧ ‖f z‖ < ‖f c‖ + 1 :=
    (hU.eventually_mem hc).and (hcont.eventually (gt_mem_nhds (lt_add_one _)))
  obtain ⟨R, hR, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  exact (hasFPowerSeriesOnBall_of_differentiableOn hR
    (hf.mono fun z hz => (hball z hz).1) fun z hz => (hball z hz).2.le).analyticAt

/-- **Holomorphic functions of several complex variables are analytic.** A map from a
finite-dimensional complex normed space to a complex Banach space that is complex
differentiable on an open set is analytic on a neighbourhood of every point of that set. -/
theorem analyticOnNhd_of_differentiableOn
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) :
    AnalyticOnNhd ℂ f U :=
  fun _ hc => analyticAt_of_differentiableOn hU hf hc

end Hironaka.HolomorphicAnalytic
