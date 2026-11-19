import Hironaka.Analytic.BochnerKodairaIdentity
import Hironaka.Analytic.HormanderWeightedL2

set_option autoImplicit false

/-!
# Hörmander's a priori estimate with three weights

For weights `w₃ = Φ + χ`, `w₂ = w₃ - ψ₀`, `w₁ = w₃ - 2ψ₀`, the formal adjoint of `∂̄` from
`L²(e^{-w₁})` to `L²_{(0,1)}(e^{-w₂})` is `T* α = -e^{-ψ₀} Σ_j δ^{w₂}_j α_j`.  If the Levi form of
`χ` dominates `(1 + 1/t) n ‖Dψ₀‖²`, then for every compactly supported smooth `(0,1)`-form `α`

  `∫ Levi_Φ(α) e^{-w₃} ≤ (1 + t) ∫ |T* α|² e^{-w₁} + ∫ Σ_{j,k} |∂̄_j α_k - ∂̄_k α_j|² e^{-w₃}`.

This is Hörmander, *An introduction to complex analysis in several variables*, (4.2.9) with the
cutoff weights of Lemma 4.1.3; the loss `1 + t` replaces Hörmander's limiting argument.
-/

open MeasureTheory Set Filter Complex
open scoped ComplexConjugate ContDiff Topology

namespace Hironaka.Hormander

noncomputable section

open CauchyGreen

variable {n : ℕ}

/-- The formal adjoint `T* α = -e^{-ψ₀} Σ_j δ^{w₂}_j α_j`. -/
def tstarForm (w₂ ψ₀ : ComplexModel n → ℝ) (α : Fin n → ComplexModel n → ℂ) (x : ComplexModel n) :
    ℂ :=
  -((Real.exp (-ψ₀ x) : ℝ) : ℂ) * ∑ j, deltaDir (coordVec j) w₂ (α j) x

/-- The coefficients `∂̄_j α_k - ∂̄_k α_j` of `∂̄ α`. -/
def dbarForm (α : Fin n → ComplexModel n → ℂ) (p : Fin n × Fin n) (x : ComplexModel n) : ℂ :=
  dbarDir (coordVec p.1) (α p.2) x - dbarDir (coordVec p.2) (α p.1) x

theorem norm_dDir_le {f : ComplexModel n → ℂ} {x v : ComplexModel n} (hv : ‖v‖ = 1) :
    ‖dDir v f x‖ ≤ ‖fderiv ℝ f x‖ := by
  have h1 : ‖fderiv ℝ f x v‖ ≤ ‖fderiv ℝ f x‖ := by
    simpa [hv] using (fderiv ℝ f x).le_opNorm v
  have h2 : ‖fderiv ℝ f x (I • v)‖ ≤ ‖fderiv ℝ f x‖ := by
    simpa [norm_smul, hv] using (fderiv ℝ f x).le_opNorm (I • v)
  unfold dDir
  rw [norm_div, RCLike.norm_ofNat]
  calc ‖fderiv ℝ f x v - I * fderiv ℝ f x (I • v)‖ / 2
      ≤ (‖fderiv ℝ f x v‖ + ‖I * fderiv ℝ f x (I • v)‖) / 2 := by
        gcongr; exact norm_sub_le _ _
    _ ≤ (‖fderiv ℝ f x‖ + ‖fderiv ℝ f x‖) / 2 := by
        gcongr; rw [norm_mul, norm_I, one_mul]; exact h2
    _ = ‖fderiv ℝ f x‖ := by ring

theorem norm_fderiv_ofReal_comp {φ : ComplexModel n → ℝ} {x : ComplexModel n}
    (hφ : DifferentiableAt ℝ φ x) :
    ‖fderiv ℝ (fun y ↦ (φ y : ℂ)) x‖ = ‖fderiv ℝ φ x‖ := by
  have h : fderiv ℝ (fun y ↦ (φ y : ℂ)) x = ofRealCLM.comp (fderiv ℝ φ x) :=
    ((ofRealCLM.hasFDerivAt).comp x hφ.hasFDerivAt).fderiv
  rw [h]
  exact LinearIsometry.norm_toContinuousLinearMap_comp (f := ofRealLI) (g := fderiv ℝ φ x)

theorem norm_coordVec (j : Fin n) : ‖(coordVec j : ComplexModel n)‖ = 1 := by
  simp [coordVec]

/-- `|Σ_j c_j α_j|² ≤ (Σ_j |c_j|²) (Σ_j |α_j|²)` in the form used below. -/
theorem norm_sum_mul_sq_le {c a : Fin n → ℂ} {M : ℝ} (hc : ∀ j, ‖c j‖ ≤ M) :
    ‖∑ j, c j * a j‖ ^ 2 ≤ n * M ^ 2 * ∑ j, ‖a j‖ ^ 2 := by
  calc ‖∑ j, c j * a j‖ ^ 2 ≤ (∑ j, ‖c j‖ * ‖a j‖) ^ 2 := by
        gcongr
        exact (norm_sum_le _ _).trans (by simp only [norm_mul, le_refl])
    _ ≤ (∑ j, ‖c j‖ ^ 2) * ∑ j, ‖a j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ (n * M ^ 2) * ∑ j, ‖a j‖ ^ 2 := by
        gcongr
        calc ∑ j, ‖c j‖ ^ 2 ≤ ∑ _j : Fin n, M ^ 2 :=
              Finset.sum_le_sum fun j _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hc j) 2
          _ = n * M ^ 2 := by simp

theorem sq_norm_sub_le_of_pos {a b : ℂ} {t : ℝ} (ht : 0 < t) :
    ‖a - b‖ ^ 2 ≤ (1 + t) * ‖a‖ ^ 2 + (1 + 1 / t) * ‖b‖ ^ 2 := by
  have h1 : ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le a b
  have h2 : 2 * ‖a‖ * ‖b‖ ≤ t * ‖a‖ ^ 2 + ‖b‖ ^ 2 / t := by
    have : 0 ≤ (t * ‖a‖ - ‖b‖) ^ 2 / t := div_nonneg (sq_nonneg _) ht.le
    have e : (t * ‖a‖ - ‖b‖) ^ 2 / t = t * ‖a‖ ^ 2 - 2 * ‖a‖ * ‖b‖ + ‖b‖ ^ 2 / t := by
      field_simp; ring
    linarith
  calc ‖a - b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := by gcongr
    _ = ‖a‖ ^ 2 + 2 * ‖a‖ * ‖b‖ + ‖b‖ ^ 2 := by ring
    _ ≤ (1 + t) * ‖a‖ ^ 2 + (1 + 1 / t) * ‖b‖ ^ 2 := by
      have : ‖b‖ ^ 2 / t = 1 / t * ‖b‖ ^ 2 := by ring
      nlinarith

theorem norm_sq_sum_smul_coordVec (ξ : Fin n → ℂ) :
    ‖∑ j, ξ j • (coordVec j : ComplexModel n)‖ ^ 2 = ∑ j, ‖ξ j‖ ^ 2 := by
  have h : ∑ j, ξ j • (coordVec j : ComplexModel n) = WithLp.toLp 2 ξ := by
    ext i
    simp [coordVec, Finset.sum_apply, Pi.single_apply]
  rw [h, EuclideanSpace.norm_sq_eq]

theorem eq_zero_of_notMem_tsupport' {f : ComplexModel n → ℂ} {x : ComplexModel n}
    (hx : x ∉ tsupport f) : f x = 0 :=
  image_eq_zero_of_notMem_tsupport hx

theorem fderiv_eq_zero_of_notMem_tsupport {f : ComplexModel n → ℂ} {x : ComplexModel n}
    (hx : x ∉ tsupport f) : fderiv ℝ f x = 0 := by
  have h := notMem_tsupport_iff_eventuallyEq.mp hx
  rw [h.fderiv_eq]
  simp

theorem dbarDir_eq_zero_of_notMem_tsupport {f : ComplexModel n → ℂ} {x v : ComplexModel n}
    (hx : x ∉ tsupport f) : dbarDir v f x = 0 := by
  simp [dbarDir, fderiv_eq_zero_of_notMem_tsupport hx]

theorem deltaDir_eq_zero_of_notMem_tsupport {f : ComplexModel n → ℂ} {w : ComplexModel n → ℝ}
    {x v : ComplexModel n} (hx : x ∉ tsupport f) : deltaDir v w f x = 0 := by
  simp [deltaDir, dDir, fderiv_eq_zero_of_notMem_tsupport hx, eq_zero_of_notMem_tsupport' hx]

theorem continuous_leviForm_comp {Φ : ComplexModel n → ℝ} (hΦ : ContDiff ℝ 2 Φ)
    {ξ : ComplexModel n → ComplexModel n} (hξ : Continuous ξ) :
    Continuous fun x ↦ leviForm Φ x (ξ x) := by
  have hD : Continuous (fderiv ℝ (fderiv ℝ Φ)) :=
    (hΦ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  have hH : ∀ v w : ComplexModel n → ComplexModel n, Continuous v → Continuous w →
      Continuous fun x ↦ realHessian Φ x (v x) (w x) := by
    intro v w hv hw
    simp only [realHessian_eq_fderiv]
    exact (hD.clm_apply hv).clm_apply hw
  unfold leviForm
  have hIξ : Continuous fun x ↦ Complex.I • ξ x := by fun_prop
  exact ((hH ξ ξ hξ hξ).add (hH _ _ hIξ hIξ)).div_const 4

theorem integrable_of_continuous_of_eq_zero_off {f : ComplexModel n → ℝ} {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hc : Continuous f) (h0 : ∀ x ∉ K, f x = 0) : Integrable f :=
  hc.integrable_of_hasCompactSupport (HasCompactSupport.intro hK h0)

theorem deltaDir_sub_weight {v : ComplexModel n} {W ψ : ComplexModel n → ℝ} {a : ComplexModel n → ℂ}
    {x : ComplexModel n} (hW : DifferentiableAt ℝ W x) (hψ : DifferentiableAt ℝ ψ x) :
    deltaDir v (fun y ↦ W y - ψ y) a x =
      deltaDir v W a x + dDir v (fun y ↦ (ψ y : ℂ)) x * a x := by
  have hc : (fun y ↦ ((W y - ψ y : ℝ) : ℂ)) = fun y ↦ (W y : ℂ) - (ψ y : ℂ) := by
    funext y; push_cast; ring
  unfold deltaDir
  rw [hc, dDir_sub (differentiableAt_ofReal_comp hW) (differentiableAt_ofReal_comp hψ)]
  ring

/-- **The a priori estimate** for globally `C²` weights. -/
theorem apriori_global {Φ χ ψ₀ : ComplexModel n → ℝ} (hΦ : ContDiff ℝ 2 Φ) (hχ : ContDiff ℝ 2 χ)
    (hψ : ContDiff ℝ 2 ψ₀) {t : ℝ} (ht : 0 < t) {α : Fin n → ComplexModel n → ℂ}
    (hα : ∀ j, ContDiff ℝ 2 (α j)) (hαc : ∀ j, HasCompactSupport (α j))
    (hLevi : ∀ x, (∃ j, x ∈ tsupport (α j)) → ∀ ξ,
      (1 + 1 / t) * n * ‖fderiv ℝ ψ₀ x‖ ^ 2 * ‖ξ‖ ^ 2 ≤ leviForm χ x ξ) :
    ∫ x, leviForm Φ x (∑ j, α j x • coordVec j) * Real.exp (-(Φ x + χ x)) ≤
      (1 + t) * (∫ x, ‖tstarForm (fun y ↦ Φ y + χ y - ψ₀ y) ψ₀ α x‖ ^ 2 *
          Real.exp (-(Φ x + χ x - 2 * ψ₀ x))) +
        ∫ x, (∑ p, ‖dbarForm α p x‖ ^ 2) * Real.exp (-(Φ x + χ x)) := by
  have hW : ContDiff ℝ 2 (fun y ↦ Φ y + χ y) := hΦ.add hχ
  have hW₂ : ContDiff ℝ 2 (fun y ↦ Φ y + χ y - ψ₀ y) := (hΦ.add hχ).sub hψ
  have hKc : IsCompact (⋃ j, tsupport (α j)) := isCompact_iUnion fun j ↦ hαc j
  have hout : ∀ x ∉ ⋃ j, tsupport (α j), ∀ j, x ∉ tsupport (α j) := fun x hx j h ↦
    hx (mem_iUnion.mpr ⟨j, h⟩)
  have bk := integral_bochnerKodaira_eq_zero (μ := volume)
    (fun j ↦ (coordVec j : ComplexModel n)) hW hα hαc
  have hα1 : ∀ j, ContDiff ℝ 1 (α j) := fun j ↦ (hα j).of_le (by norm_num)
  have hexp : Continuous fun x ↦ Real.exp (-(Φ x + χ x)) := by
    have := hΦ.continuous; have := hχ.continuous; fun_prop
  have hξc : Continuous fun x ↦ ∑ j, α j x • (coordVec j : ComplexModel n) := by
    have := fun j ↦ (hα j).continuous; fun_prop
  -- the three integrands on the right and the Levi integrand are integrable
  have iL : Integrable fun x ↦ leviForm Φ x (∑ j, α j x • coordVec j) *
      Real.exp (-(Φ x + χ x)) := by
    refine integrable_of_continuous_of_eq_zero_off hKc
      ((continuous_leviForm_comp hΦ hξc).mul hexp) fun x hx ↦ ?_
    simp [eq_zero_of_notMem_tsupport' (hout x hx _)]
  have iT : Integrable fun x ↦ ‖tstarForm (fun y ↦ Φ y + χ y - ψ₀ y) ψ₀ α x‖ ^ 2 *
      Real.exp (-(Φ x + χ x - 2 * ψ₀ x)) := by
    refine integrable_of_continuous_of_eq_zero_off hKc ?_ fun x hx ↦ ?_
    · have hd : ∀ j, Continuous (deltaDir (coordVec j) (fun y ↦ Φ y + χ y - ψ₀ y) (α j)) :=
        fun j ↦ continuous_deltaDir (hW₂.of_le (by norm_num)) (hα1 j)
      have := hΦ.continuous; have := hχ.continuous; have := hψ.continuous
      unfold tstarForm
      fun_prop
    · simp [tstarForm, deltaDir_eq_zero_of_notMem_tsupport (hout x hx _)]
  have iS : Integrable fun x ↦ (∑ p, ‖dbarForm α p x‖ ^ 2) * Real.exp (-(Φ x + χ x)) := by
    refine integrable_of_continuous_of_eq_zero_off hKc ?_ fun x hx ↦ ?_
    · have hd : ∀ j k, Continuous (dbarDir (coordVec j : ComplexModel n) (α k)) :=
        fun j k ↦ continuous_dbarDir (hα1 k)
      unfold dbarForm
      fun_prop
    · simp [dbarForm, dbarDir_eq_zero_of_notMem_tsupport (hout x hx _)]
  set G : ComplexModel n → ℝ := fun x ↦
    (‖∑ j, deltaDir (coordVec j) (fun y ↦ Φ y + χ y) (α j) x‖ ^ 2 +
            1 / 2 * ∑ j, ∑ k, ‖dbarDir (coordVec j) (α k) x - dbarDir (coordVec k) (α j) x‖ ^ 2 -
          (∑ j, ∑ k, ‖dbarDir (coordVec k) (α j) x‖ ^ 2 +
            (∑ j, ∑ k, dbarDir (coordVec k) (dDir (coordVec j) fun y ↦ ((Φ y + χ y : ℝ) : ℂ)) x *
              α j x * conj (α k x)).re)) * Real.exp (-(Φ x + χ x)) with hG
  have iG : Integrable G := by
    refine integrable_of_continuous_of_eq_zero_off hKc ?_ fun x hx ↦ ?_
    · have hd : ∀ j, Continuous (deltaDir (coordVec j) (fun y ↦ Φ y + χ y) (α j)) :=
        fun j ↦ continuous_deltaDir (hW.of_le (by norm_num)) (hα1 j)
      have hb : ∀ j k, Continuous (dbarDir (coordVec j : ComplexModel n) (α k)) :=
        fun j k ↦ continuous_dbarDir (hα1 k)
      have hL : ∀ j k, Continuous (dbarDir (coordVec k : ComplexModel n)
          (dDir (coordVec j) fun y ↦ ((Φ y + χ y : ℝ) : ℂ))) := fun j k ↦
        continuous_dbarDir (contDiff_dDir (k := 1) (contDiff_ofReal_comp hW))
      have ha : ∀ j, Continuous (α j) := fun j ↦ (hα j).continuous
      simp only [hG]
      fun_prop
    · simp [hG, eq_zero_of_notMem_tsupport' (hout x hx _),
        deltaDir_eq_zero_of_notMem_tsupport (hout x hx _),
        dbarDir_eq_zero_of_notMem_tsupport (hout x hx _)]
  have key : ∀ x, leviForm Φ x (∑ j, α j x • coordVec j) * Real.exp (-(Φ x + χ x)) ≤
      (1 + t) * (‖tstarForm (fun y ↦ Φ y + χ y - ψ₀ y) ψ₀ α x‖ ^ 2 *
          Real.exp (-(Φ x + χ x - 2 * ψ₀ x))) +
        (1 / 2) * ((∑ p, ‖dbarForm α p x‖ ^ 2) * Real.exp (-(Φ x + χ x))) - G x := by
    intro x
    set a : Fin n → ℂ := fun j ↦ α j x with ha
    set ξ : ComplexModel n := ∑ j, α j x • coordVec j with hξ
    set E3 := Real.exp (-(Φ x + χ x)) with hE3
    have hE3pos : 0 < E3 := Real.exp_pos _
    -- the curvature term
    have hRe : (∑ j, ∑ k, dbarDir (coordVec k) (dDir (coordVec j) fun y ↦ ((Φ y + χ y : ℝ) : ℂ)) x *
        α j x * conj (α k x)).re = leviForm Φ x ξ + leviForm χ x ξ := by
      have h := sum_dbarDir_dDir_mul_conj_eq_leviForm (fun j ↦ (coordVec j : ComplexModel n)) hW a x
      simp only [ha] at h
      rw [h, Complex.ofReal_re]
      exact leviForm_add (u := Φ) (v := χ) hΦ.contDiffAt hχ.contDiffAt ξ
    -- the twisted adjoint
    set c : Fin n → ℂ := fun j ↦ dDir (coordVec j) (fun y ↦ (ψ₀ y : ℂ)) x with hc
    have hδ : ∑ j, deltaDir (coordVec j) (fun y ↦ Φ y + χ y) (α j) x =
        ∑ j, deltaDir (coordVec j) (fun y ↦ Φ y + χ y - ψ₀ y) (α j) x - ∑ j, c j * a j := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [deltaDir_sub_weight (hW.differentiable (by norm_num) x)
        (hψ.differentiable (by norm_num) x)]
      ring
    have hcb : ∀ j, ‖c j‖ ≤ ‖fderiv ℝ ψ₀ x‖ := fun j ↦ by
      rw [← norm_fderiv_ofReal_comp (hψ.differentiable (by norm_num) x)]
      exact norm_dDir_le (norm_coordVec j)
    have hY : ‖∑ j, c j * a j‖ ^ 2 ≤ n * ‖fderiv ℝ ψ₀ x‖ ^ 2 * ‖ξ‖ ^ 2 := by
      rw [hξ, norm_sq_sum_smul_coordVec]
      exact norm_sum_mul_sq_le hcb
    have hsplit := sq_norm_sub_le_of_pos
      (a := ∑ j, deltaDir (coordVec j) (fun y ↦ Φ y + χ y - ψ₀ y) (α j) x)
      (b := ∑ j, c j * a j) ht
    rw [← hδ] at hsplit
    have hχξ : (1 + 1 / t) * n * ‖fderiv ℝ ψ₀ x‖ ^ 2 * ‖ξ‖ ^ 2 ≤ leviForm χ x ξ := by
      by_cases hx : ∃ j, x ∈ tsupport (α j)
      · exact hLevi x hx ξ
      · push Not at hx
        have h0 : ξ = 0 := by
          rw [hξ]
          exact Finset.sum_eq_zero fun j _ ↦ by rw [eq_zero_of_notMem_tsupport' (hx j), zero_smul]
        rw [h0]; simp
    -- the adjoint in the weight `e^{-w₁}`
    have hT : ‖tstarForm (fun y ↦ Φ y + χ y - ψ₀ y) ψ₀ α x‖ ^ 2 *
        Real.exp (-(Φ x + χ x - 2 * ψ₀ x)) =
        ‖∑ j, deltaDir (coordVec j) (fun y ↦ Φ y + χ y - ψ₀ y) (α j) x‖ ^ 2 * E3 := by
      rw [tstarForm, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), mul_pow, hE3]
      have : Real.exp (-ψ₀ x) ^ 2 * Real.exp (-(Φ x + χ x - 2 * ψ₀ x)) =
          Real.exp (-(Φ x + χ x)) := by
        rw [sq, ← Real.exp_add, ← Real.exp_add]; ring_nf
      linear_combination ‖∑ j, deltaDir (coordVec j) (fun y ↦ Φ y + χ y - ψ₀ y) (α j) x‖ ^ 2 * this
    -- the `∂̄` term
    have hS : ∑ p, ‖dbarForm α p x‖ ^ 2 =
        ∑ j, ∑ k, ‖dbarDir (coordVec j) (α k) x - dbarDir (coordVec k) (α j) x‖ ^ 2 := by
      rw [Fintype.sum_prod_type]; rfl
    have hA : 0 ≤ ∑ j, ∑ k, ‖dbarDir (coordVec k) (α j) x‖ ^ 2 :=
      Finset.sum_nonneg fun j _ ↦ Finset.sum_nonneg fun k _ ↦ sq_nonneg _
    rw [hT, hS]
    simp only [hG]
    rw [hRe]
    have hB := mul_le_mul_of_nonneg_right hY (by positivity : (0 : ℝ) ≤ 1 + 1 / t)
    nlinarith [mul_le_mul_of_nonneg_right hsplit hE3pos.le,
      mul_le_mul_of_nonneg_right hχξ hE3pos.le, mul_le_mul_of_nonneg_right hB hE3pos.le,
      mul_nonneg hA hE3pos.le]
  have hint : ∫ x, leviForm Φ x (∑ j, α j x • coordVec j) * Real.exp (-(Φ x + χ x)) ≤
      ∫ x, ((1 + t) * (‖tstarForm (fun y ↦ Φ y + χ y - ψ₀ y) ψ₀ α x‖ ^ 2 *
          Real.exp (-(Φ x + χ x - 2 * ψ₀ x))) +
        (1 / 2) * ((∑ p, ‖dbarForm α p x‖ ^ 2) * Real.exp (-(Φ x + χ x))) - G x) :=
    integral_mono iL (((iT.const_mul _).add (iS.const_mul _)).sub iG) key
  have i1 : Integrable fun x ↦ (1 + t) * (‖tstarForm (fun y ↦ Φ y + χ y - ψ₀ y) ψ₀ α x‖ ^ 2 *
      Real.exp (-(Φ x + χ x - 2 * ψ₀ x))) +
        (1 / 2) * ((∑ p, ‖dbarForm α p x‖ ^ 2) * Real.exp (-(Φ x + χ x))) :=
    (iT.const_mul _).add (iS.const_mul _)
  rw [integral_sub i1 iG, integral_add (iT.const_mul (1 + t)) (iS.const_mul (1 / 2)),
    integral_const_mul, integral_const_mul] at hint
  have hG0 : ∫ x, G x = 0 := bk
  have hS0 : 0 ≤ ∫ x, (∑ p, ‖dbarForm α p x‖ ^ 2) * Real.exp (-(Φ x + χ x)) :=
    integral_nonneg fun x ↦ mul_nonneg (Finset.sum_nonneg fun p _ ↦ sq_nonneg _)
      (Real.exp_pos _).le
  linarith

end

end Hironaka.Hormander
