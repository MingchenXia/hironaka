import Hironaka.Analytic.DivisorialSliceBound
import Hironaka.Analytic.RiemannExtension
import Hironaka.Analytic.HolomorphicAnalytic

set_option autoImplicit false

/-!
# Vanishing order along a coordinate hyperplane of a germ with a weighted `L²` bound

Blueprint `pc:divisorial-multiplier-order` (Copy-4 `lem:domination`, Step 1), in coordinates in which
the divisor is the hyperplane `E = {z_{m+1} = 0}` of `ℂ^{m+1}`; Lelong numbers are normalized by
`ν(log ‖z‖, 0) = 1`.

Let `u` satisfy the slice bound `u ≤ γ log |z_{m+1}| + C` near `p ∈ E` for every `γ < ν`
(`DivisorialSliceBound`), and let `G`, `J` be holomorphic near `p` with `J = z_{m+1}^k J'`, `J'` not
identically zero on `E` near `p`.  If `∫ |G J|² e^{-c u} < ∞` near `p`, then

  `G = z_{m+1}^a H` near `p`, with `H` holomorphic, for every integer `a ≥ 0` with `a + k < c ν / 2`.

In the application `G = g ∘ ρ` for a germ `g` of the multiplier ideal `𝓘(m v)` and `J` the Jacobian
determinant of `ρ`, so that `|G J|² e^{-c u}` is the pullback of `|g|² e^{-m v}` by the change of
variables formula; the conclusion is `ord_E (g ∘ ρ) ≥ (m/2) ν(ρ^* v, E) - A_E`, `A_E = 1 + k`.

* `neg_two_lt_of_lintegral_ne_top` — the exponent lemma: `∫ |z_{m+1}|^{2b} |f|² e^{-c u} < ∞` near a
  point `y ∈ E` with `f(y) ≠ 0` forces `2b - cγ > -2`, because `|z_{m+1}|^{-2}` is not integrable
  near `y` (`OTChen.lintegral_ball_div_normSq_last_eq_top`).
* `exists_eq_last_mul_of_eq_zero` — division by the coordinate: a holomorphic germ vanishing on `E`
  is `z_{m+1}` times a holomorphic germ (Riemann extension of `G / z_{m+1}`, bounded by the mean
  value inequality).
* `frequently_ne_zero_and_ne_zero` — two holomorphic germs, neither identically zero on `E` near
  `p`, are simultaneously nonzero at points of `E` arbitrarily close to `p` (identity theorem on the
  hyperplane).
* `exists_eq_last_pow_mul_of_lintegral_ne_top` — the conclusion above, by induction on `a`.

Sorry-free.
-/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal

namespace Hironaka.DivisorialMultiplierOrder

open DivisorialSliceBound

noncomputable section

variable {m : ℕ}

/-! ### The exponent lemma -/

/-- The real inequality behind the exponent lemma: for `0 < t ≤ 1` and `2b - cγ ≤ -2`,
`κ / t² ≤ t^{2b} · A · e^{-c(γ log t + C)}` whenever `κ ≤ A e^{-cC}`. -/
theorem div_sq_le_of_exponent_le {t A κ c γ C : ℝ} (b : ℕ) (ht : 0 < t) (ht1 : t ≤ 1)
    (hle : 2 * (b : ℝ) - c * γ ≤ -2) (hκ : κ ≤ A * Real.exp (-(c * C))) (hκ0 : 0 ≤ κ) :
    κ / t ^ 2 ≤ t ^ (2 * b) * A * Real.exp (-(c * (γ * Real.log t + C))) := by
  have hexp : Real.exp (-(c * (γ * Real.log t + C))) =
      t ^ (-(c * γ)) * Real.exp (-(c * C)) := by
    rw [Real.rpow_def_of_pos ht, ← Real.exp_add]
    congr 1
    ring
  have hpow : t ^ (2 * b) * t ^ (-(c * γ)) = t ^ (2 * (b : ℝ) - c * γ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ht]
    congr 1
    push_cast
    ring
  have hmono : t ^ (-2 : ℝ) ≤ t ^ (2 * (b : ℝ) - c * γ) :=
    Real.rpow_le_rpow_of_exponent_ge ht ht1 hle
  have hinv : κ / t ^ 2 = κ * t ^ (-2 : ℝ) := by
    rw [Real.rpow_neg ht.le, div_eq_mul_inv]
    norm_num
  have hApos : 0 ≤ A * Real.exp (-(c * C)) := hκ0.trans hκ
  calc κ / t ^ 2 = κ * t ^ (-2 : ℝ) := hinv
    _ ≤ (A * Real.exp (-(c * C))) * t ^ (2 * (b : ℝ) - c * γ) :=
        mul_le_mul hκ hmono (Real.rpow_nonneg ht.le _) hApos
    _ = t ^ (2 * b) * A * Real.exp (-(c * (γ * Real.log t + C))) := by
        rw [hexp, ← hpow]
        ring

/-- **The exponent lemma.**  Let `y` lie on the hyperplane `{z_{m+1} = 0}`, `U` a neighbourhood of
`y` on which `u ≤ γ log |z_{m+1}| + C` off the hyperplane, and `f` continuous at `y` with
`f(y) ≠ 0`.  If `∫_U |z_{m+1}|^{2b} |f|² e^{-c u} < ∞` (with `c > 0`), then `2b - cγ > -2`. -/
theorem neg_two_lt_of_lintegral_ne_top {y : ComplexModel (m + 1)} (hy : y (Fin.last m) = 0)
    {U : Set (ComplexModel (m + 1))} (hU : U ∈ 𝓝 y) {u : ComplexModel (m + 1) → EReal}
    {c γ C : ℝ} (hc : 0 < c)
    (hu : ∀ z ∈ U, z (Fin.last m) ≠ 0 →
      u z ≤ ((γ * Real.log ‖z (Fin.last m)‖ + C : ℝ) : EReal))
    {f : ComplexModel (m + 1) → ℂ} (hf : ContinuousAt f y) (hfy : f y ≠ 0) (b : ℕ)
    (hint : ∫⁻ z in U, multiplierDensity u c (fun z => z (Fin.last m) ^ b * f z) z ≠ ⊤) :
    -2 < 2 * (b : ℝ) - c * γ := by
  by_contra hle
  push Not at hle
  set a := ‖f y‖ ^ 2 with ha
  have hapos : 0 < a := by positivity
  have hcont : ContinuousAt (fun z => ‖f z‖ ^ 2) y := hf.norm.pow 2
  have hev : ∀ᶠ z in 𝓝 y, a / 2 < ‖f z‖ ^ 2 ∧ z ∈ U :=
    (hcont.eventually (lt_mem_nhds (by linarith))).and hU
  obtain ⟨r₀, hr₀, hball⟩ := Metric.mem_nhds_iff.mp hev
  set r := min r₀ 1 with hrdef
  have hr : 0 < r := lt_min hr₀ one_pos
  set κ := a / 2 * Real.exp (-(c * C)) with hκdef
  have hκ : 0 < κ := by positivity
  apply hint
  refine top_le_iff.mp ?_
  rw [← OTChen.lintegral_ball_div_normSq_last_eq_top hy hr hκ]
  calc ∫⁻ z in ball y r, ENNReal.ofReal (κ / ‖z (Fin.last m)‖ ^ 2)
      ≤ ∫⁻ z in ball y r,
          multiplierDensity u c (fun z => z (Fin.last m) ^ b * f z) z := by
        refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
        have hz₀ : z ∈ ball y r₀ := ball_subset_ball (min_le_left _ _) hz
        obtain ⟨hfz, hzU⟩ := hball hz₀
        by_cases h0 : z (Fin.last m) = 0
        · simp [h0]
        set t := ‖z (Fin.last m)‖ with ht
        have htpos : 0 < t := norm_pos_iff.mpr h0
        have ht1 : t ≤ 1 := by
          have h1 : t ≤ ‖z - y‖ := norm_last_le hy z
          have h2 : ‖z - y‖ < r := by rw [← dist_eq_norm]; exact mem_ball.mp hz
          linarith [min_le_right r₀ 1]
        have hw : multiplierWeight c (((γ * Real.log t + C : ℝ)) : EReal) ≤
            multiplierWeight c (u z) :=
          multiplierWeight_antitone hc.le (hu z hzU h0)
        rw [multiplierWeight_coe] at hw
        unfold multiplierDensity
        refine le_trans ?_ (mul_le_mul' le_rfl hw)
        rw [← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [norm_mul, norm_pow, mul_pow, ← pow_mul, ← ht, mul_comm b 2]
        refine div_sq_le_of_exponent_le b htpos ht1 hle ?_ hκ.le
        exact mul_le_mul_of_nonneg_right hfz.le (Real.exp_pos _).le
    _ ≤ ∫⁻ z in U, multiplierDensity u c (fun z => z (Fin.last m) ^ b * f z) z :=
        lintegral_mono_set fun z hz =>
          (hball (ball_subset_ball (min_le_left _ _) hz)).2

/-! ### Division by the coordinate -/

/-- A point of `ℂ^{m+1}` off the hyperplane, arbitrarily close to the origin. -/
theorem not_eventually_last_eq_zero : ¬ ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
    z (Fin.last m) = 0 := by
  intro h
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp h
  have hmem : EuclideanSpace.single (Fin.last m) ((δ / 2 : ℝ) : ℂ) ∈
      ball (0 : ComplexModel (m + 1)) δ := by
    rw [mem_ball_zero_iff, PiLp.norm_single]
    simp [abs_of_pos hδ]
    linarith
  have := hball _ hmem
  simp at this
  linarith

/-- **Division by the coordinate.**  A function holomorphic near a point `p` of the hyperplane
`{z_{m+1} = 0}` and vanishing on the hyperplane near `p` is `z_{m+1} H` near `p`, with `H`
holomorphic near `p`. -/
theorem exists_eq_last_mul_of_eq_zero {p : ComplexModel (m + 1)} (hp : p (Fin.last m) = 0)
    {G : ComplexModel (m + 1) → ℂ} (hG : ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ G z)
    (h0 : ∀ᶠ z in 𝓝 p, z (Fin.last m) = 0 → G z = 0) :
    ∃ H : ComplexModel (m + 1) → ℂ, (∀ᶠ z in 𝓝 p, DifferentiableAt ℂ H z) ∧
      G =ᶠ[𝓝 p] fun z => z (Fin.last m) * H z := by
  obtain ⟨R, hR, hRball⟩ := Metric.eventually_nhds_iff_ball.mp (hG.and h0)
  set r := R / 2 with hrdef
  have hr : 0 < r := by positivity
  have hrR : r < R := by linarith
  -- a bound on the derivative on `closedBall p r`
  have hdiffOn : DifferentiableOn ℂ G (ball p R) := fun z hz =>
    (hRball z hz).1.differentiableWithinAt
  have hcd : ContDiffOn ℂ 1 G (ball p R) :=
    (HolomorphicAnalytic.analyticOnNhd_of_differentiableOn isOpen_ball hdiffOn).contDiffOn
      isOpen_ball.uniqueDiffOn
  have hfd : ContinuousOn (fun z => ‖fderiv ℂ G z‖) (closedBall p r) :=
    ((hcd.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).mono
      (closedBall_subset_ball hrR)).norm
  obtain ⟨M, hM⟩ := (isCompact_closedBall p r).exists_bound_of_continuousOn hfd
  have hMb : ∀ z ∈ ball p r, ‖fderiv ℂ G z‖ ≤ M := fun z hz => by
    have := hM z (ball_subset_closedBall hz)
    rwa [Real.norm_eq_abs, abs_norm] at this
  -- the quotient `G(z + p) / z_{m+1}` on the punctured ball
  set h : ComplexModel (m + 1) → ℂ := fun z => z (Fin.last m) with hhdef
  have hhlin : h = ⇑(EuclideanSpace.proj (𝕜 := ℂ) (Fin.last m)) := by
    funext z; rfl
  set f : ComplexModel (m + 1) → ℂ := fun z => G (z + p) / z (Fin.last m) with hfdef
  have hmemR : ∀ z ∈ ball (0 : ComplexModel (m + 1)) r, z + p ∈ ball p R := fun z hz => by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_right]
    rw [mem_ball_zero_iff] at hz
    linarith
  have hmemr : ∀ z ∈ ball (0 : ComplexModel (m + 1)) r, z + p ∈ ball p r := fun z hz => by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_right]
    rwa [mem_ball_zero_iff] at hz
  have hhd : DifferentiableOn ℂ h (ball 0 r) := by
    rw [hhlin]; exact (ContinuousLinearMap.differentiable _).differentiableOn
  have hfd' : DifferentiableOn ℂ f (ball 0 r \ h ⁻¹' {0}) := by
    intro z hz
    have hz0 : z (Fin.last m) ≠ 0 := hz.2
    have hGd : DifferentiableAt ℂ (fun w => G (w + p)) z :=
      (hRball _ (hmemR z hz.1)).1.comp z (differentiableAt_id.add_const p)
    have hhz : DifferentiableAt ℂ h z := by
      rw [hhlin]; exact (ContinuousLinearMap.differentiable _) z
    have hq : DifferentiableAt ℂ (fun w => G (w + p) * (w (Fin.last m))⁻¹) z :=
      hGd.mul (hhz.fun_inv hz0)
    rw [hfdef]
    simp only [div_eq_mul_inv]
    exact hq.differentiableWithinAt
  have hbdd : ∃ C, ∀ z ∈ ball (0 : ComplexModel (m + 1)) r \ h ⁻¹' {0}, ‖f z‖ ≤ C := by
    refine ⟨M, fun z hz => ?_⟩
    have hz0 : z (Fin.last m) ≠ 0 := hz.2
    have hzb : z ∈ ball (0 : ComplexModel (m + 1)) r := hz.1
    set x := hyperplaneFoot z + p with hx
    have hxlast : x (Fin.last m) = 0 := by simp [hx, hp]
    have hfoot : ‖hyperplaneFoot z‖ ≤ ‖z‖ := by
      have := norm_hyperplaneFoot_sub_le (p := (0 : ComplexModel (m + 1))) (by simp) z
      simpa using this
    have hxb : x ∈ ball p r := by
      rw [mem_ball, dist_eq_norm, hx, add_sub_cancel_right]
      rw [mem_ball_zero_iff] at hzb
      linarith
    have hGx : G x = 0 := (hRball x (ball_subset_ball hrR.le hxb)).2 hxlast
    have hmv := (convex_ball p r).norm_image_sub_le_of_norm_fderiv_le
      (fun w hw => (hRball w (ball_subset_ball hrR.le hw)).1) hMb hxb (hmemr z hzb)
    rw [hGx, sub_zero, hx, add_sub_add_right_eq_sub, norm_sub_hyperplaneFoot] at hmv
    have hpos : 0 < ‖z (Fin.last m)‖ := norm_pos_iff.mpr hz0
    show ‖G (z + p) / z (Fin.last m)‖ ≤ M
    rw [norm_div, div_le_iff₀ hpos]
    exact hmv
  obtain ⟨ρ, hρ, F, hFd, hFeq⟩ := RiemannExtension.exists_extension_of_bounded hr hhd
    not_eventually_last_eq_zero hfd' hbdd
  refine ⟨fun z => F (z - p), ?_, ?_⟩
  · filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hρ : p ∈ ball p ρ)] with z hz
    have hz' : z - p ∈ ball (0 : ComplexModel (m + 1)) ρ := by
      rw [mem_ball_zero_iff, ← dist_eq_norm]; exact mem_ball.mp hz
    exact (hFd.differentiableAt (isOpen_ball.mem_nhds hz')).comp z
      (differentiableAt_id.sub_const p)
  · filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (lt_min hρ hr) : p ∈ ball p (min ρ r))]
      with z hz
    have hzρ : z - p ∈ ball (0 : ComplexModel (m + 1)) ρ := by
      rw [mem_ball_zero_iff, ← dist_eq_norm]
      exact (mem_ball.mp hz).trans_le (min_le_left _ _)
    have hzR : z ∈ ball p R :=
      ball_subset_ball ((min_le_right _ _).trans hrR.le) hz
    by_cases h0 : z (Fin.last m) = 0
    · simp only [h0, zero_mul]
      exact (hRball z hzR).2 h0
    · have hlast : (z - p) (Fin.last m) = z (Fin.last m) := by simp [hp]
      have hFz := hFeq (z - p) hzρ (by show (z - p) (Fin.last m) ≠ 0; rw [hlast]; exact h0)
      show G z = z (Fin.last m) * F (z - p)
      rw [hFz]
      show G z = z (Fin.last m) * (G (z - p + p) / (z - p) (Fin.last m))
      rw [sub_add_cancel, hlast]
      field_simp

/-! ### Simultaneous nonvanishing on the hyperplane -/

/-- On the hyperplane `{z_{m+1} = 0}` the norm is the norm of the first `m` coordinates. -/
theorem norm_eq_norm_initCoords {x : ComplexModel (m + 1)} (hx : x (Fin.last m) = 0) :
    ‖x‖ = ‖initCoords x‖ := by
  have h := OTChen.norm_sq_eq_initCoords x
  rw [hx, norm_zero] at h
  have h2 : ‖x‖ ^ 2 = ‖initCoords x‖ ^ 2 := by simpa using h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2


/-- **Two holomorphic germs, neither identically zero on the hyperplane near `p`, are
simultaneously nonzero at points of the hyperplane arbitrarily close to `p`.**  On the hyperplane
the second one is analytic; vanishing on the open set where the first one does not vanish, it
would vanish on a whole ball of the hyperplane by the identity theorem. -/
theorem frequently_ne_zero_and_ne_zero {p : ComplexModel (m + 1)} (hp : p (Fin.last m) = 0)
    {f g : ComplexModel (m + 1) → ℂ} (hf : ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ f z)
    (hg : ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ g z)
    (hf' : ∃ᶠ z in 𝓝 p, z (Fin.last m) = 0 ∧ f z ≠ 0)
    (hg' : ∃ᶠ z in 𝓝 p, z (Fin.last m) = 0 ∧ g z ≠ 0) :
    ∃ᶠ z in 𝓝 p, z (Fin.last m) = 0 ∧ f z ≠ 0 ∧ g z ≠ 0 := by
  rw [Filter.frequently_iff]
  intro U hU
  by_contra hcon
  push Not at hcon
  -- a ball on which everything holds
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp ((hf.and hg).and hU)
  -- a point of the hyperplane in the ball where `f ≠ 0`
  obtain ⟨z₁, hz₁b, hz₁last, hfz₁⟩ :=
    (Filter.frequently_iff.mp hf') (isOpen_ball.mem_nhds (mem_ball_self hε))
  -- near `z₁`, `f ≠ 0`
  have hfc : ContinuousAt f z₁ := ((hball hz₁b).1.1).continuousAt
  have hnear : ∀ᶠ z in 𝓝 z₁, f z ≠ 0 ∧ z ∈ ball p ε :=
    (hfc.eventually (isOpen_compl_singleton.mem_nhds hfz₁)).and
      (isOpen_ball.mem_nhds hz₁b)
  -- `g` vanishes on the hyperplane near `z₁`
  have hgz : ∀ᶠ z in 𝓝 z₁, z (Fin.last m) = 0 → g z = 0 := by
    filter_upwards [hnear] with z hz hzl
    by_contra hgz
    exact hgz (hcon z (hball hz.2).2 hzl hz.1)
  -- the restriction of `g` to a ball of the hyperplane
  set V : Set (ComplexModel m) := ball (initCoords p) ε with hV
  have hmaps : ∀ w ∈ V, sliceMap m 0 w ∈ ball p ε := fun w hw => by
    rw [mem_ball, dist_eq_norm, norm_eq_norm_initCoords (by simp [hp]), OTChen.initCoords_sub,
      initCoords_sliceMap, ← dist_eq_norm]
    exact hw
  have hinV : ∀ z ∈ ball p ε, z (Fin.last m) = 0 → initCoords z ∈ V := fun z hz hzl => by
    rw [hV, mem_ball, dist_eq_norm, ← OTChen.initCoords_sub,
      ← norm_eq_norm_initCoords (by simp [hzl, hp]), ← dist_eq_norm]
    exact hz
  have hsl : ∀ z : ComplexModel (m + 1), z (Fin.last m) = 0 → sliceMap m 0 (initCoords z) = z :=
    fun z hzl => by
      have := sliceMap_initCoords z
      rwa [hzl] at this
  set G' : ComplexModel m → ℂ := fun w => g (sliceMap m 0 w) with hG'
  have hG'd : DifferentiableOn ℂ G' V := fun w hw =>
    (((hball (hmaps w hw)).1.2).comp w ((differentiable_sliceMap 0) w)).differentiableWithinAt
  have hG'a : AnalyticOnNhd ℂ G' V :=
    HolomorphicAnalytic.analyticOnNhd_of_differentiableOn isOpen_ball hG'd
  have hw₁ : initCoords z₁ ∈ V := hinV z₁ hz₁b hz₁last
  have hG'ev : G' =ᶠ[𝓝 (initCoords z₁)] 0 := by
    have hcont : ContinuousAt (sliceMap m 0) (initCoords z₁) :=
      (continuous_sliceMap 0).continuousAt
    rw [← hsl z₁ hz₁last] at hgz
    filter_upwards [hcont.eventually hgz] with w hw
    exact hw (sliceMap_last 0 w)
  have hG'0 := hG'a.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball _ _).isPreconnected hw₁ hG'ev
  -- so `g` vanishes on the hyperplane near `p`, a contradiction
  apply (Filter.not_frequently.mpr ?_) hg'
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hε)] with z hz ⟨hzl, hgz⟩
  have := hG'0 (hinV z hz hzl)
  simp only [hG', Pi.zero_apply, hsl z hzl] at this
  exact hgz this

/-! ### The vanishing order -/

/-- **Vanishing order along the hyperplane of a germ with a weighted `L²` bound**
(`pc:divisorial-multiplier-order`, in coordinates).  Let `p` lie on `E = {z_{m+1} = 0}`, `c > 0`,
and suppose that for every `γ < ν` the slice bound `u ≤ γ log |z_{m+1}| + C` holds near `p` off `E`.
Let `G`, `J'` be holomorphic near `p`, `J = z_{m+1}^k J'` near `p` with `J'` not identically zero
on `E` near `p`, and `∫ |G J|² e^{-c u} < ∞` on a neighbourhood of `p`.  Then for every integer
`a ≥ 0` with `a + k < c ν / 2` (and for `a = 0`), `G = z_{m+1}^a H` near `p` with `H` holomorphic
near `p`. -/
theorem exists_eq_last_pow_mul_of_lintegral_ne_top {p : ComplexModel (m + 1)}
    (hp : p (Fin.last m) = 0) {u : ComplexModel (m + 1) → EReal} {c ν : ℝ} (hc : 0 < c)
    (hslice : ∀ γ < ν, ∃ U ∈ 𝓝 p, ∃ C : ℝ, ∀ z ∈ U, z (Fin.last m) ≠ 0 →
      u z ≤ ((γ * Real.log ‖z (Fin.last m)‖ + C : ℝ) : EReal))
    {G J J' : ComplexModel (m + 1) → ℂ} {k : ℕ}
    (hG : ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ G z)
    (hJ' : ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ J' z)
    (hJ : J =ᶠ[𝓝 p] fun z => z (Fin.last m) ^ k * J' z)
    (hJne : ∃ᶠ z in 𝓝 p, z (Fin.last m) = 0 ∧ J' z ≠ 0)
    (hint : ∃ U ∈ 𝓝 p, ∫⁻ z in U, multiplierDensity u c (fun z => G z * J z) z ≠ ⊤) :
    ∀ a : ℕ, (a = 0 ∨ (a : ℝ) + k < c * ν / 2) →
      ∃ H : ComplexModel (m + 1) → ℂ, (∀ᶠ z in 𝓝 p, DifferentiableAt ℂ H z) ∧
        G =ᶠ[𝓝 p] fun z => z (Fin.last m) ^ a * H z := by
  obtain ⟨U₀, hU₀, hint₀⟩ := hint
  intro a
  induction a with
  | zero =>
    intro _
    exact ⟨G, hG, Eventually.of_forall fun z => by simp⟩
  | succ a ih =>
    intro ha
    have ha' : ((a + 1 : ℕ) : ℝ) + k < c * ν / 2 := by
      rcases ha with h | h
      · exact absurd h (Nat.succ_ne_zero a)
      · exact h
    have ha'' : (a : ℝ) + k < c * ν / 2 := by push_cast at ha'; linarith
    obtain ⟨H, hHd, hGH⟩ := ih (Or.inr ha'')
    -- `H` vanishes on the hyperplane near `p`
    have hvan : ∀ᶠ z in 𝓝 p, z (Fin.last m) = 0 → H z = 0 := by
      by_contra hnv
      have hHne : ∃ᶠ z in 𝓝 p, z (Fin.last m) = 0 ∧ H z ≠ 0 := by
        rw [Filter.not_eventually] at hnv
        exact hnv.mono fun z hz => by push Not at hz; exact hz
      have hboth := frequently_ne_zero_and_ne_zero hp hHd hJ' hHne hJne
      -- the exponent `γ` with `2 (a + k) - c γ = -2`
      set γ : ℝ := (2 * ((a : ℝ) + k) + 2) / c with hγ
      have hγν : γ < ν := by
        rw [hγ, div_lt_iff₀ hc]
        push_cast at ha'
        linarith
      obtain ⟨U₁, hU₁, C, hC⟩ := hslice γ hγν
      -- a ball around `p` on which all the local data hold
      have hev : ∀ᶠ z in 𝓝 p, ((z ∈ U₀ ∧ z ∈ U₁) ∧
          (G z = z (Fin.last m) ^ a * H z ∧ J z = z (Fin.last m) ^ k * J' z)) ∧
          (DifferentiableAt ℂ H z ∧ DifferentiableAt ℂ J' z) :=
        (((show ∀ᶠ z in 𝓝 p, z ∈ U₀ from hU₀).and (show ∀ᶠ z in 𝓝 p, z ∈ U₁ from hU₁)).and
          (Filter.Eventually.and hGH hJ)).and (hHd.and hJ')
      obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hev
      obtain ⟨y, hyb, hylast, hHy, hJy⟩ :=
        (Filter.frequently_iff.mp hboth) (isOpen_ball.mem_nhds (mem_ball_self hε))
      have hUy : ball p ε ∈ 𝓝 y := isOpen_ball.mem_nhds hyb
      have hfc : ContinuousAt (fun z => H z * J' z) y :=
        ((hεsub hyb).2.1.continuousAt).mul ((hεsub hyb).2.2.continuousAt)
      have hlt := neg_two_lt_of_lintegral_ne_top (U := ball p ε) (u := u) (c := c) (γ := γ)
        (C := C) hylast hUy hc
        (fun z hz hz0 => hC z (hεsub hz).1.1.2 hz0) hfc (mul_ne_zero hHy hJy) (a + k) ?_
      · rw [hγ, mul_div_cancel₀ _ hc.ne'] at hlt
        push_cast at hlt
        linarith
      -- the integral over the ball is finite
      refine ne_top_of_le_ne_top hint₀ ?_
      calc ∫⁻ z in ball p ε,
            multiplierDensity u c (fun z => z (Fin.last m) ^ (a + k) * (H z * J' z)) z
          = ∫⁻ z in ball p ε, multiplierDensity u c (fun z => G z * J z) z := by
            refine setLIntegral_congr_fun measurableSet_ball fun z hz => ?_
            have h1 := (hεsub hz).1.2
            simp only [multiplierDensity]
            rw [h1.1, h1.2, pow_add]
            ring_nf
        _ ≤ ∫⁻ z in U₀, multiplierDensity u c (fun z => G z * J z) z :=
            lintegral_mono_set fun z hz => (hεsub hz).1.1.1
    obtain ⟨H', hH'd, hHH'⟩ := exists_eq_last_mul_of_eq_zero hp hHd hvan
    refine ⟨H', hH'd, ?_⟩
    filter_upwards [hGH, hHH'] with z h1 h2
    rw [h1, h2, pow_succ]
    ring

end

end Hironaka.DivisorialMultiplierOrder
