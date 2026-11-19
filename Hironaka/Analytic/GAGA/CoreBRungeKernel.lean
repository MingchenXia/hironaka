import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.PartitionOfUnity
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Polynomial approximation of the Cauchy kernel off a compact convex set

Infrastructure of lane SERRE-CORE2 (Serre's GAGA, towards source `lma:GAGA`), step M2.2 of the
plan in `blueprint/src/claude-serre-core.tex` (see `blueprint/src/claude-serre-core2.tex`).

Let `C ⊆ ℂ` be compact and convex.

* `exists_poly_approx_inv_sub`: for `ζ₀ ∉ C`, the function `w ↦ (w - ζ₀)⁻¹` is a uniform limit
  on `C` of polynomials. A real linear functional `Re(v ·)` separates `ζ₀` from `C`, so
  `ξ = v (w - ζ₀)` has `Re ξ ≥ d > 0` on `C`; for `R` large, `C` is mapped into a disc
  `|ξ - R| ≤ q R` with `q < 1`, and `1/ξ = R⁻¹ ∑_k ((R - ξ)/R)^k` converges uniformly there
  ("pushing the pole to infinity" in one step).
* `exists_kernel_approx`: for a compact `A` disjoint from `C`, the kernel `(w - ζ)⁻¹` is
  approximated uniformly on `A × C` by `∑_i χ_i(ζ) p_i(w)` with polynomials `p_i` and a
  continuous partition of unity `χ_i` on `A`.
-/

set_option autoImplicit false

open Set Filter Metric Complex
open scoped Topology

namespace Hironaka.Analytic.GAGA.Core.Runge

/-- **Pole pushing.** For `C ⊆ ℂ` compact convex and `ζ₀ ∉ C`, the function `(w - ζ₀)⁻¹` is
uniformly approximable on `C` by polynomials. -/
theorem exists_poly_approx_inv_sub {C : Set ℂ} (hC : IsCompact C) (hconv : Convex ℝ C)
    {ζ₀ : ℂ} (hζ₀ : ζ₀ ∉ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Polynomial ℂ, ∀ w ∈ C, ‖(w - ζ₀)⁻¹ - p.eval w‖ < ε := by
  obtain ⟨f, u, hfu, hfC⟩ := geometric_hahn_banach_point_closed hconv hC.isClosed hζ₀
  set v : ℂ := (f 1 : ℂ) - (f I : ℂ) * I with hv
  have hfv : ∀ x : ℂ, f x = (v * x).re := by
    intro x
    have hx : x = (x.re : ℝ) • (1 : ℂ) + (x.im : ℝ) • I := by
      apply Complex.ext <;> simp
    have h1 : f x = x.re * f 1 + x.im * f I := by
      conv_lhs => rw [hx]
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    rw [h1, hv]
    simp only [mul_re, sub_re, ofReal_re, mul_im, ofReal_im, I_re, I_im, sub_im]
    ring
  set d : ℝ := u - f ζ₀ with hd
  have hd0 : 0 < d := by linarith
  set ξ : ℂ → ℂ := fun w => v * (w - ζ₀) with hξ
  have hξre : ∀ w ∈ C, d < (ξ w).re := by
    intro w hw
    have h1 := hfC w hw
    rw [hfv w] at h1
    show u - f ζ₀ < (v * (w - ζ₀)).re
    rw [mul_sub, sub_re, hfv ζ₀]
    linarith
  obtain ⟨B₀, hB₀⟩ := hC.exists_bound_of_continuousOn
    ((continuous_const.mul (continuous_id.sub continuous_const)).continuousOn (f := ξ))
  set B : ℝ := |B₀| with hB
  have hBξ : ∀ w ∈ C, ‖ξ w‖ ≤ B := fun w hw => (hB₀ w hw).trans (le_abs_self _)
  set R : ℝ := B ^ 2 / d + 1 with hR
  have hR0 : 0 < R := by positivity
  set s : ℝ := (R ^ 2 - 2 * R * d + B ^ 2) / R ^ 2 with hs
  have hs1 : s < 1 := by
    rw [hs, div_lt_one (by positivity)]
    have : B ^ 2 < 2 * R * d := by
      have : 2 * R * d = 2 * B ^ 2 + 2 * d := by
        rw [hR]; field_simp
      rw [this]
      nlinarith [sq_nonneg B]
    linarith
  set q : ℝ := Real.sqrt s with hq
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq1 : q < 1 := by
    rw [hq, Real.sqrt_lt' one_pos]
    simpa using hs1
  set y : ℂ → ℂ := fun w => ((R : ℂ) - ξ w) / R with hy
  have hyq : ∀ w ∈ C, ‖y w‖ ≤ q := by
    intro w hw
    have hsq : ‖(R : ℂ) - ξ w‖ ^ 2 ≤ R ^ 2 - 2 * R * d + B ^ 2 := by
      have h1 : ‖(R : ℂ) - ξ w‖ ^ 2 = R ^ 2 - 2 * R * (ξ w).re + ‖ξ w‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
        simp only [sub_re, ofReal_re, sub_im, ofReal_im]
        ring
      rw [h1]
      have h2 := hξre w hw
      have h3 : ‖ξ w‖ ^ 2 ≤ B ^ 2 := by
        have := hBξ w hw
        exact pow_le_pow_left₀ (norm_nonneg _) this 2
      nlinarith
    have hy2 : ‖y w‖ ^ 2 ≤ s := by
      rw [hy, norm_div, Complex.norm_real, Real.norm_of_nonneg hR0.le, div_pow, hs]
      exact div_le_div_of_nonneg_right hsq (by positivity)
    rw [hq, ← Real.sqrt_sq (norm_nonneg (y w))]
    exact Real.sqrt_le_sqrt hy2
  -- the error of the truncated geometric series
  have hξne : ∀ w ∈ C, ξ w ≠ 0 := fun w hw h => by
    have := hξre w hw
    rw [h, zero_re] at this
    linarith
  have herr : ∀ N : ℕ, ∀ w ∈ C,
      (w - ζ₀)⁻¹ - v * ((1 / R : ℂ) * ∑ k ∈ Finset.range N, y w ^ k) = v * (y w ^ N * (ξ w)⁻¹) := by
    intro N w hw
    have hξw := hξne w hw
    have hv0 : v ≠ 0 := fun h => hξw (by simp [hξ, h])
    have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR0.ne'
    have hgeom := geom_sum_mul_neg (y w) N
    have h1y : 1 - y w = ξ w / R := by
      simp only [hy]
      field_simp
      ring
    rw [h1y] at hgeom
    have hw0 : w - ζ₀ ≠ 0 := fun h => hξw (by simp [hξ, h])
    have hinv : (w - ζ₀)⁻¹ = v * (ξ w)⁻¹ := by
      simp only [hξ, mul_inv]
      field_simp
    rw [hinv]
    have : (1 / R : ℂ) * ∑ k ∈ Finset.range N, y w ^ k = (1 - y w ^ N) * (ξ w)⁻¹ := by
      rw [← hgeom]
      field_simp
    rw [this]
    ring
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ‖v‖ * q ^ N / d < ε := by
    have ht : Tendsto (fun N : ℕ => ‖v‖ * q ^ N / d) atTop (𝓝 (‖v‖ * 0 / d)) :=
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul ‖v‖).div_const d
    rw [mul_zero, zero_div] at ht
    exact (ht.eventually (gt_mem_nhds hε)).exists
  refine ⟨Polynomial.C (v / R) * ∑ k ∈ Finset.range N,
    (Polynomial.C (((R : ℂ) + v * ζ₀) / R) - Polynomial.C (v / R) * Polynomial.X) ^ k,
    fun w hw => ?_⟩
  have heval : (Polynomial.C (v / R) * ∑ k ∈ Finset.range N,
      (Polynomial.C (((R : ℂ) + v * ζ₀) / R) - Polynomial.C (v / R) * Polynomial.X) ^ k).eval w =
      v * ((1 / R : ℂ) * ∑ k ∈ Finset.range N, y w ^ k) := by
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_finsetSum, Finset.mul_sum,
      Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_X, hy, hξ]
    ring_nf
  rw [heval, herr N w hw, norm_mul, norm_mul, norm_pow, norm_inv]
  have hξd : d ≤ ‖ξ w‖ := (hξre w hw).le.trans (Complex.re_le_norm _)
  calc ‖v‖ * (‖y w‖ ^ N * ‖ξ w‖⁻¹) ≤ ‖v‖ * (q ^ N * d⁻¹) := by
        gcongr
        exact hyq w hw
    _ = ‖v‖ * q ^ N / d := by ring
    _ < ε := hN

/-- **Uniform approximation of the Cauchy kernel.** Let `C ⊆ ℂ` be compact convex and `A ⊆ ℂ`
compact, disjoint from `C`. Then `(w - ζ)⁻¹` is approximated within `ε` on `A × C` by
`∑_i χ_i(ζ) p_i(w)`, with finitely many polynomials `p_i` and continuous `χ_i : ℂ → [0, 1]`. -/
theorem exists_kernel_approx {C A : Set ℂ} (hC : IsCompact C) (hconv : Convex ℝ C)
    (hA : IsCompact A) (hAC : Disjoint A C) {ε : ℝ} (hε : 0 < ε) :
    ∃ (ι : Type) (_ : Fintype ι) (χ : ι → ℂ → ℝ) (p : ι → Polynomial ℂ),
      (∀ i, Continuous (χ i)) ∧ (∀ i ζ, 0 ≤ χ i ζ ∧ χ i ζ ≤ 1) ∧
      ∀ ζ ∈ A, ∀ w ∈ C, ‖(w - ζ)⁻¹ - ∑ i, (χ i ζ : ℂ) * (p i).eval w‖ ≤ ε := by
  classical
  rcases C.eq_empty_or_nonempty with hCe | hCne
  · refine ⟨Empty, inferInstance, fun _ _ => 0, fun _ => 0, fun _ => continuous_const,
      fun i => i.elim, fun ζ _ w hw => ?_⟩
    rw [hCe] at hw
    exact absurd hw (notMem_empty w)
  -- local approximations
  have hloc : ∀ ζ₀ ∈ A, ∃ r > 0, ∃ p : Polynomial ℂ,
      ∀ ζ ∈ ball ζ₀ r, ∀ w ∈ C, ‖(w - ζ)⁻¹ - p.eval w‖ < ε := by
    intro ζ₀ hζ₀
    have hζC : ζ₀ ∉ C := fun h => hAC.ne_of_mem hζ₀ h rfl
    have hd₀ : 0 < infDist ζ₀ C := (hC.isClosed.notMem_iff_infDist_pos hCne).1 hζC
    set d₀ := infDist ζ₀ C
    obtain ⟨p, hp⟩ := exists_poly_approx_inv_sub hC hconv hζC (half_pos hε)
    refine ⟨min (d₀ / 2) (ε * d₀ ^ 2 / 4), by positivity, p, fun ζ hζ w hw => ?_⟩
    have hζ' : ‖ζ - ζ₀‖ < min (d₀ / 2) (ε * d₀ ^ 2 / 4) := by
      rw [← dist_eq_norm]; exact hζ
    have h1 : d₀ ≤ ‖w - ζ₀‖ := by
      rw [← dist_eq_norm, dist_comm]
      exact infDist_le_dist_of_mem hw
    have h2 : d₀ / 2 ≤ ‖w - ζ‖ := by
      have : ‖w - ζ₀‖ ≤ ‖w - ζ‖ + ‖ζ - ζ₀‖ := by
        calc ‖w - ζ₀‖ = ‖(w - ζ) + (ζ - ζ₀)‖ := by ring_nf
          _ ≤ ‖w - ζ‖ + ‖ζ - ζ₀‖ := norm_add_le _ _
      have := min_le_left (d₀ / 2) (ε * d₀ ^ 2 / 4)
      linarith
    have hne1 : w - ζ₀ ≠ 0 := fun h => by
      rw [h, norm_zero] at h1; linarith
    have hne2 : w - ζ ≠ 0 := fun h => by
      rw [h, norm_zero] at h2; linarith
    have hdiff : ‖(w - ζ)⁻¹ - (w - ζ₀)⁻¹‖ ≤ ε / 2 := by
      have heq : (w - ζ)⁻¹ - (w - ζ₀)⁻¹ = (ζ - ζ₀) / ((w - ζ) * (w - ζ₀)) := by
        field_simp
        ring
      rw [heq, norm_div, norm_mul]
      rw [div_le_iff₀ (by positivity)]
      have h3 : ‖ζ - ζ₀‖ ≤ ε * d₀ ^ 2 / 4 := hζ'.le.trans (min_le_right _ _)
      calc ‖ζ - ζ₀‖ ≤ ε * d₀ ^ 2 / 4 := h3
        _ = ε / 2 * (d₀ / 2 * d₀) := by ring
        _ ≤ ε / 2 * (‖w - ζ‖ * ‖w - ζ₀‖) := by gcongr
    calc ‖(w - ζ)⁻¹ - p.eval w‖ ≤ ‖(w - ζ)⁻¹ - (w - ζ₀)⁻¹‖ + ‖(w - ζ₀)⁻¹ - p.eval w‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt hdiff (hp w hw)
      _ = ε := add_halves ε
  choose! r hr p hp using hloc
  -- a finite subcover and a subordinate partition of unity
  obtain ⟨t, hcov⟩ := hA.elim_nhds_subcover' (fun ζ₀ _ => ball ζ₀ (r ζ₀))
    (fun ζ₀ hζ₀ => ball_mem_nhds ζ₀ (hr ζ₀ hζ₀))
  obtain ⟨f, hf⟩ := PartitionOfUnity.exists_isSubordinate hA.isClosed
    (fun i : t => ball ((i : A) : ℂ) (r (i : A))) (fun _ => isOpen_ball) (by
      intro ζ hζ
      obtain ⟨x, hx, hxζ⟩ := mem_iUnion₂.1 (hcov hζ)
      exact mem_iUnion.2 ⟨⟨x, hx⟩, hxζ⟩)
  refine ⟨t, inferInstance, fun i => f i, fun i => p (i : A), fun i => (f i).continuous,
    fun i ζ => ⟨f.nonneg i ζ, f.le_one i ζ⟩, fun ζ hζ w hw => ?_⟩
  have hsum : ∑ i, f i ζ = 1 := by
    rw [← finsum_eq_sum_of_fintype]
    exact f.sum_eq_one hζ
  have heq : (w - ζ)⁻¹ - ∑ i, ((f i ζ : ℝ) : ℂ) * (p i).eval w =
      ∑ i, ((f i ζ : ℝ) : ℂ) * ((w - ζ)⁻¹ - (p i).eval w) := by
    have : ∑ i, ((f i ζ : ℝ) : ℂ) = 1 := by exact_mod_cast hsum
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, this, one_mul]
  rw [heq]
  calc ‖∑ i, ((f i ζ : ℝ) : ℂ) * ((w - ζ)⁻¹ - (p i).eval w)‖
      ≤ ∑ i, ‖((f i ζ : ℝ) : ℂ) * ((w - ζ)⁻¹ - (p i).eval w)‖ := norm_sum_le _ _
    _ ≤ ∑ i, f i ζ * ε := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (f.nonneg i ζ)]
        by_cases h0 : f i ζ = 0
        · rw [h0]; simp
        · refine mul_le_mul_of_nonneg_left (hp (i : A) (i : A).2 ζ ?_ w hw).le (f.nonneg i ζ)
          exact hf i (subset_tsupport _ h0)
    _ = ε := by rw [← Finset.sum_mul, hsum, one_mul]

end Hironaka.Analytic.GAGA.Core.Runge
