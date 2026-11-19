import Hironaka.Analytic.WeightedWirtingerAdjoint

set_option autoImplicit false

/-!
# The Bochner--Kodaira--Morrey--Kohn identity for test `(0,1)`-forms

Let `φ` be a `C²` real weight on a finite-dimensional complex space `E` with an additive Haar
measure, `e : ι → E` a finite family of directions, and `α : ι → E → ℂ` compactly supported `C²`
coefficients.  With `δ_j = δ_{e_j}` the weighted `∂` and `∂̄_j = ∂̄_{e_j}`,

  `∫ |Σ_j δ_j α_j|² e^{-φ} + ½ ∫ Σ_{j,k} |∂̄_j α_k - ∂̄_k α_j|² e^{-φ}`
  `  = ∫ Σ_{j,k} |∂̄_k α_j|² e^{-φ} + ∫ Re Σ_{j,k} (∂̄_k ∂_j φ) α_j conj α_k e^{-φ}`.

For an orthonormal basis `e` the left side is `‖ϑ_φ α‖² + ‖∂̄ α‖²` and the last integrand is the
Levi form of `φ` evaluated at `Σ α_j e_j`.  This is the a priori identity behind Hörmander's `L²`
estimates (Hörmander, *An introduction to complex analysis in several variables*, §4.2).
-/

open MeasureTheory Set Filter Complex
open scoped Topology ContDiff ComplexConjugate

namespace Hironaka.CauchyGreen

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

omit [NormedSpace ℂ E] [FiniteDimensional ℂ E] in
theorem integrable_of_continuous_hasCompactSupport_mul {f g : E → ℂ} (hf : Continuous f)
    (hg : Continuous g) (hc : HasCompactSupport f) :
    Integrable (fun x ↦ f x * g x) μ :=
  (hf.mul hg).integrable_of_hasCompactSupport hc.mul_right

/-- The adjoint identity with the conjugate on the other factor. -/
theorem integral_conj_deltaDir_mul {v : E} {φ : E → ℝ} {a b : E → ℂ}
    (hφ : ContDiff ℝ 1 φ) (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b)
    (hab : HasCompactSupport a ∨ HasCompactSupport b) :
    ∫ x, conj (deltaDir v φ a x) * b x * cweight φ x ∂μ =
      - ∫ x, conj (a x) * dbarDir v b x * cweight φ x ∂μ := by
  have h := congrArg conj (integral_deltaDir_mul_conj (μ := μ) (v := v) hφ ha hb hab)
  rw [← integral_conj, map_neg, ← integral_conj] at h
  have hw : ∀ x, conj (cweight φ x) = cweight φ x := fun x ↦ by rw [cweight, Complex.conj_ofReal]
  simpa only [map_mul, conj_conj, hw] using h

omit [FiniteDimensional ℂ E] [MeasurableSpace E] [BorelSpace E] in
theorem continuous_deltaDir {v : E} {φ : E → ℝ} {a : E → ℂ}
    (hφ : ContDiff ℝ 1 φ) (ha : ContDiff ℝ 1 a) : Continuous (deltaDir v φ a) :=
  (contDiff_deltaDir (k := 0) (by simpa using hφ) (by simpa using ha)).continuous

omit [FiniteDimensional ℂ E] [MeasurableSpace E] [BorelSpace E] in
theorem continuous_dbarDir {v : E} {a : E → ℂ} (ha : ContDiff ℝ 1 a) :
    Continuous (dbarDir v a) :=
  (contDiff_dbarDir (k := 0) (by simpa using ha)).continuous

/-- **The pairwise Morrey--Kohn identity.** -/
theorem integral_deltaDir_mul_conj_deltaDir {u v : E} {φ : E → ℝ} {a b : E → ℂ}
    (hφ : ContDiff ℝ 2 φ) (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (hac : HasCompactSupport a) (hbc : HasCompactSupport b) :
    ∫ x, deltaDir u φ a x * conj (deltaDir v φ b x) * cweight φ x ∂μ =
      ∫ x, dbarDir v a x * conj (dbarDir u b x) * cweight φ x ∂μ +
        ∫ x, dbarDir v (dDir u (fun y ↦ (φ y : ℂ))) x * a x * conj (b x) * cweight φ x ∂μ := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have ha1 : ContDiff ℝ 1 a := ha.of_le (by norm_num)
  have hb1 : ContDiff ℝ 1 b := hb.of_le (by norm_num)
  have hA : ContDiff ℝ 1 (deltaDir u φ a) := contDiff_deltaDir (k := 1) hφ ha
  have hda : ContDiff ℝ 1 (dbarDir v a) := contDiff_dbarDir (k := 1) ha
  have hw : Continuous (cweight φ) := (contDiff_cweight hφ).continuous
  have hP : Continuous (dbarDir v (dDir u (fun y ↦ (φ y : ℂ)))) :=
    continuous_dbarDir (contDiff_dDir (k := 1) (contDiff_ofReal_comp hφ))
  -- step 1: move `δ_v` off `b`
  have s1 : ∫ x, deltaDir u φ a x * conj (deltaDir v φ b x) * cweight φ x ∂μ =
      - ∫ x, conj (b x) * dbarDir v (deltaDir u φ a) x * cweight φ x ∂μ := by
    rw [← integral_conj_deltaDir_mul hφ1 hb1 hA (Or.inl hbc)]
    congr 1; funext x; ring
  -- step 2: the commutator
  have s2 : (fun x ↦ conj (b x) * dbarDir v (deltaDir u φ a) x * cweight φ x) =
      fun x ↦ deltaDir u φ (dbarDir v a) x * conj (b x) * cweight φ x -
        dbarDir v (dDir u (fun y ↦ (φ y : ℂ))) x * a x * conj (b x) * cweight φ x := by
    funext x
    rw [dbarDir_deltaDir hφ ha]
    ring
  have hi1 : Integrable (fun x ↦ deltaDir u φ (dbarDir v a) x * conj (b x) * cweight φ x) μ := by
    have hc : HasCompactSupport (deltaDir u φ (dbarDir v a)) :=
      hasCompactSupport_deltaDir (hasCompactSupport_dbarDir hac)
    refine (integrable_of_continuous_hasCompactSupport_mul (μ := μ)
      (continuous_deltaDir hφ1 hda) ((continuous_conj.comp hb.continuous).mul hw) hc).congr
      (Eventually.of_forall fun x ↦ ?_)
    simp only [Pi.mul_apply, Function.comp_apply]; ring
  have hi2 : Integrable (fun x ↦ dbarDir v (dDir u (fun y ↦ (φ y : ℂ))) x * a x *
      conj (b x) * cweight φ x) μ := by
    have h := integrable_of_continuous_hasCompactSupport_mul (μ := μ) ha.continuous
      (hP.mul ((continuous_conj.comp hb.continuous).mul hw)) hac
    refine h.congr (Eventually.of_forall fun x ↦ ?_)
    simp only [Pi.mul_apply, Function.comp_apply]; ring
  -- step 3: move `δ_u` off `∂̄_v a`
  have s3 := integral_deltaDir_mul_conj (μ := μ) (v := u) hφ1 hda hb1 (Or.inr hbc)
  rw [s1, s2, integral_sub hi1 hi2, s3]
  ring

omit [FiniteDimensional ℂ E] [MeasurableSpace E] [BorelSpace E] in
/-- The pointwise algebra: `½ Σ_{j,k} |A_{jk} - A_{kj}|² = Σ_{j,k} |A_{kj}|² - Re Σ_{j,k} A_{kj} conj A_{jk}`. -/
theorem half_sum_normSq_sub_antisymm {ι : Type*} [Fintype ι] (A : ι → ι → ℂ) :
    (1 / 2 : ℝ) * ∑ j, ∑ k, ‖A j k - A k j‖ ^ 2 =
      ∑ j, ∑ k, ‖A k j‖ ^ 2 - (∑ j, ∑ k, A k j * conj (A j k)).re := by
  have h1 : ∀ z w : ℂ, ‖z - w‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 - 2 * (w * conj z).re := by
    intro z w
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_sub]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  simp_rw [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, Complex.re_sum]
  have hswap : ∑ j : ι, ∑ k : ι, ‖A j k‖ ^ 2 = ∑ j : ι, ∑ k : ι, ‖A k j‖ ^ 2 :=
    Finset.sum_comm
  rw [hswap]
  simp_rw [← Finset.mul_sum]
  ring

/-- **The Bochner--Kodaira--Morrey--Kohn identity** for compactly supported `C²` coefficients,
in the form `∫ G = 0`. -/
theorem integral_bochnerKodaira_eq_zero {ι : Type*} [Fintype ι] (e : ι → E) {φ : E → ℝ}
    {α : ι → E → ℂ} (hφ : ContDiff ℝ 2 φ) (hα : ∀ j, ContDiff ℝ 2 (α j))
    (hαc : ∀ j, HasCompactSupport (α j)) :
    ∫ x, ((‖∑ j, deltaDir (e j) φ (α j) x‖ ^ 2 +
        (1 / 2 : ℝ) * ∑ j, ∑ k, ‖dbarDir (e j) (α k) x - dbarDir (e k) (α j) x‖ ^ 2) -
      (∑ j, ∑ k, ‖dbarDir (e k) (α j) x‖ ^ 2 +
        (∑ j, ∑ k, dbarDir (e k) (dDir (e j) (fun y ↦ (φ y : ℂ))) x * α j x *
          conj (α k x)).re)) * Real.exp (-φ x) ∂μ = 0 := by
  set D : ι → E → ℂ := fun j ↦ deltaDir (e j) φ (α j) with hD
  set A : ι → ι → E → ℂ := fun j k ↦ dbarDir (e j) (α k) with hA
  set L : ι → ι → E → ℂ := fun j k ↦ dbarDir (e k) (dDir (e j) (fun y ↦ (φ y : ℂ))) with hL
  -- the complex integrand, summand by summand
  set F : ι → ι → E → ℂ := fun j k x ↦
    D j x * conj (D k x) * cweight φ x - A k j x * conj (A j k x) * cweight φ x -
      L j k x * α j x * conj (α k x) * cweight φ x with hF
  have hw : Continuous (cweight φ) := (contDiff_cweight hφ).continuous
  have hDc : ∀ j, Continuous (D j) := fun j ↦
    continuous_deltaDir (hφ.of_le (by norm_num)) ((hα j).of_le (by norm_num))
  have hAc : ∀ j k, Continuous (A j k) := fun j k ↦
    continuous_dbarDir ((hα k).of_le (by norm_num))
  have hLc : ∀ j k, Continuous (L j k) := fun j k ↦
    continuous_dbarDir (contDiff_dDir (k := 1) (contDiff_ofReal_comp hφ))
  have hDs : ∀ j, HasCompactSupport (D j) := fun j ↦ hasCompactSupport_deltaDir (hαc j)
  have hAs : ∀ j k, HasCompactSupport (A j k) := fun j k ↦ hasCompactSupport_dbarDir (hαc k)
  have hcj : ∀ k, Continuous fun x ↦ conj (α k x) := fun k ↦
    continuous_conj.comp (hα k).continuous
  have hFint : ∀ j k, Integrable (F j k) μ := by
    intro j k
    refine Integrable.sub (Integrable.sub ?_ ?_) ?_
    · refine (integrable_of_continuous_hasCompactSupport_mul (μ := μ) (hDc j)
        ((continuous_conj.comp (hDc k)).mul hw) (hDs j)).congr
        (Eventually.of_forall fun x ↦ ?_)
      simp only [Pi.mul_apply, Function.comp_apply]; ring
    · refine (integrable_of_continuous_hasCompactSupport_mul (μ := μ) (hAc k j)
        ((continuous_conj.comp (hAc j k)).mul hw) (hAs k j)).congr
        (Eventually.of_forall fun x ↦ ?_)
      simp only [Pi.mul_apply, Function.comp_apply]; ring
    · refine (integrable_of_continuous_hasCompactSupport_mul (μ := μ) (hα j).continuous
        ((hLc j k).mul ((hcj k).mul hw)) (hαc j)).congr
        (Eventually.of_forall fun x ↦ ?_)
      simp only [Pi.mul_apply]; ring
  have hF0 : ∀ j k, ∫ x, F j k x ∂μ = 0 := by
    intro j k
    have hpair := integral_deltaDir_mul_conj_deltaDir (μ := μ) (u := e j) (v := e k) hφ
      (hα j) (hα k) (hαc j) (hαc k)
    have i1 : Integrable (fun x ↦ D j x * conj (D k x) * cweight φ x) μ := by
      refine (integrable_of_continuous_hasCompactSupport_mul (μ := μ) (hDc j)
        ((continuous_conj.comp (hDc k)).mul hw) (hDs j)).congr
        (Eventually.of_forall fun x ↦ ?_)
      simp only [Pi.mul_apply, Function.comp_apply]; ring
    have i2 : Integrable (fun x ↦ A k j x * conj (A j k x) * cweight φ x) μ := by
      refine (integrable_of_continuous_hasCompactSupport_mul (μ := μ) (hAc k j)
        ((continuous_conj.comp (hAc j k)).mul hw) (hAs k j)).congr
        (Eventually.of_forall fun x ↦ ?_)
      simp only [Pi.mul_apply, Function.comp_apply]; ring
    have i3 : Integrable (fun x ↦ L j k x * α j x * conj (α k x) * cweight φ x) μ := by
      refine (integrable_of_continuous_hasCompactSupport_mul (μ := μ) (hα j).continuous
        ((hLc j k).mul ((hcj k).mul hw)) (hαc j)).congr
        (Eventually.of_forall fun x ↦ ?_)
      simp only [Pi.mul_apply]; ring
    calc ∫ x, F j k x ∂μ =
        ((∫ x, D j x * conj (D k x) * cweight φ x ∂μ) -
          ∫ x, A k j x * conj (A j k x) * cweight φ x ∂μ) -
          ∫ x, L j k x * α j x * conj (α k x) * cweight φ x ∂μ := by
          have i12 : Integrable (fun x ↦ D j x * conj (D k x) * cweight φ x -
              A k j x * conj (A j k x) * cweight φ x) μ := i1.sub i2
          rw [← integral_sub i1 i2, ← integral_sub i12 i3]
      _ = 0 := by
          simp only [hD, hA, hL]
          rw [hpair]
          ring
  have hsum : ∫ x, ∑ j, ∑ k, F j k x ∂μ = 0 := by
    rw [integral_finsetSum _ fun j _ ↦ integrable_finsetSum _ fun k _ ↦ hFint j k]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    rw [integral_finsetSum _ fun k _ ↦ hFint j k]
    exact Finset.sum_eq_zero fun k _ ↦ hF0 j k
  have hre : ∫ x, (∑ j, ∑ k, F j k x).re ∂μ = 0 := by
    have hint : Integrable (fun x ↦ ∑ j, ∑ k, F j k x) μ :=
      integrable_finsetSum _ fun j _ ↦ integrable_finsetSum _ fun k _ ↦ hFint j k
    have h := integral_re (𝕜 := ℂ) hint
    simp only [RCLike.re_to_complex] at h
    rw [h, hsum, Complex.zero_re]
  rw [← hre]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  have hcw : cweight φ x = ((Real.exp (-φ x) : ℝ) : ℂ) := rfl
  have hz : ∀ z : ℂ, ‖z‖ ^ 2 = (z * conj z).re := fun z ↦ by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hnorm : ‖∑ j, D j x‖ ^ 2 = (∑ j, ∑ k, D j x * conj (D k x)).re := by
    rw [hz, map_sum, Finset.sum_mul_sum]
  have halg := half_sum_normSq_sub_antisymm (fun j k ↦ A j k x)
  have hFx : ∑ j, ∑ k, F j k x = ((∑ j, ∑ k, D j x * conj (D k x)) -
      (∑ j, ∑ k, A k j x * conj (A j k x)) -
      ∑ j, ∑ k, L j k x * α j x * conj (α k x)) * cweight φ x := by
    simp only [hF, Finset.sum_sub_distrib]
    rw [sub_mul, sub_mul]
    simp only [Finset.sum_mul]
  beta_reduce
  rw [hFx, hcw, Complex.re_mul_ofReal, Complex.sub_re, Complex.sub_re, ← hnorm]
  rw [halg]
  ring

end

end Hironaka.CauchyGreen
