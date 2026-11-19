import Hironaka.Analytic.FubiniStudyLineLevi
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

/-!
# Positivity of the Blanchard weight along the fibres of a monomial chart

On the `j`-th monomial chart of the blowup of `ℂⁿ` along `ℂᵏ × 0`, write
`ŵ(w)ₗ = wₗ` for `l ≠ j` and `ŵ(w)ⱼ = 1` (`hatCoord`).  The local weight of the Blanchard
form is
`Ũ(w) = ∑_b c_b(w) ∑_i |∑_l B_{b i l}(w) ŵ(w)ₗ|²`
(`blowupWeight`), where `c_b ≥ 0` are partition functions and `B_b` express the normal
coordinates of the `b`-th flattening in terms of those of the flattening of the chart.

`quad_smoothDDC_log_blowupWeight_pos`: if `c` and `B` are constant along the complex line
`w₀ + t v` (a fibre direction: `vⱼ = 0` and `vₗ = 0` for `l < k`), some block `a₀` has
`c_{a₀}(w₀) > 0` and `B_{a₀} = id` on the normal coordinates, and `v ≠ 0`, then
`ddᶜ log Ũ (v, iv) > 0` at `w₀`.  Along the line, `Ũ = ‖X + tY‖²` with `X, Y` independent
(the `(a₀, j)` entry of `X` is nonzero, that of `Y` vanishes), so this is
`FubiniStudyLineLevi.leviForm_log_normSq_line_pos`.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace Hironaka.BlowupWeightLevi

open FubiniStudyLineLevi

variable {n m : ℕ}

/-- The affine coordinates `ŵ` of the `j`-th monomial chart: `wₗ` for `l ≠ j`, and `1` at `j`. -/
def hatCoord (j : Fin n) (w : ComplexModel n) (l : Fin n) : ℂ := if l = j then 1 else w l

/-- The local Blanchard weight. -/
def blowupWeight (j : Fin n) (c : Fin m → ComplexModel n → ℝ)
    (B : Fin m → Fin n → Fin n → ComplexModel n → ℂ) (w : ComplexModel n) : ℝ :=
  ∑ b, c b w * ∑ i, Complex.normSq (∑ l, B b i l w * hatCoord j w l)

theorem hatCoord_line {j : Fin n} (w v : ComplexModel n) (hv : v j = 0) (t : ℂ) (l : Fin n) :
    hatCoord j (w + t • v) l = hatCoord j w l + t * v l := by
  by_cases hl : l = j
  · subst hl; simp [hatCoord, hv]
  · simp [hatCoord, hl]

/-- **Positivity of `ddᶜ log Ũ` in fibre directions.** -/
theorem quad_smoothDDC_log_blowupWeight_pos {k : ℕ} {j : Fin n} (hj : k ≤ j.1)
    {c : Fin m → ComplexModel n → ℝ} {B : Fin m → Fin n → Fin n → ComplexModel n → ℂ}
    {w₀ v : ComplexModel n}
    (hC2 : ContDiffAt ℝ 2 (fun w => Real.log (blowupWeight j c B w)) w₀)
    (hc_line : ∀ b (t : ℂ), c b (w₀ + t • v) = c b w₀)
    (hB_line : ∀ b i l (t : ℂ), B b i l (w₀ + t • v) = B b i l w₀)
    (hc_nonneg : ∀ b, 0 ≤ c b w₀) (a₀ : Fin m) (hca : 0 < c a₀ w₀)
    (hB : ∀ i l, B a₀ i l w₀ = if k ≤ l.1 ∧ i = l then 1 else 0)
    (hvj : v j = 0) (hvk : ∀ l : Fin n, l.1 < k → v l = 0) (hv : v ≠ 0) :
    0 < smoothDDC (fun w => Real.log (blowupWeight j c B w)) w₀ ![v, Complex.I • v] := by
  classical
  rw [quad_smoothDDC_eq_leviForm hC2, leviForm_eq_line hC2]
  apply div_pos _ Real.pi_pos
  set X : EuclideanSpace ℂ (Fin m × Fin n) := WithLp.toLp 2 fun s =>
    (Real.sqrt (c s.1 w₀) : ℂ) * ∑ l, B s.1 s.2 l w₀ * hatCoord j w₀ l with hX
  set Y : EuclideanSpace ℂ (Fin m × Fin n) := WithLp.toLp 2 fun s =>
    (Real.sqrt (c s.1 w₀) : ℂ) * ∑ l, B s.1 s.2 l w₀ * v l with hY
  have hline : (fun t : ℂ => Real.log (blowupWeight j c B (w₀ + t • v))) =
      fun t : ℂ => Real.log (‖X + t • Y‖ ^ 2) := by
    funext t
    congr 1
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, blowupWeight]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hc_line, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hX, hY, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hB_line, hatCoord_line w₀ v hvj]
    rw [← Complex.normSq_eq_norm_sq, mul_left_comm t, ← mul_add, map_mul, Complex.normSq_ofReal,
      Real.mul_self_sqrt (hc_nonneg b)]
    congr 2
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [hline]
  have hca' : (Real.sqrt (c a₀ w₀) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hca).ne'
  have hXj : X (a₀, j) ≠ 0 := by
    simp only [hX]
    refine mul_ne_zero hca' ?_
    rw [Finset.sum_eq_single j]
    · simp [hB, hj, hatCoord]
    · intro l _ hl; simp [hB, Ne.symm hl]
    · simp
  have hYj : Y (a₀, j) = 0 := by
    simp only [hY]
    rw [Finset.sum_eq_single j]
    · simp [hvj]
    · intro l _ hl; simp [hB, Ne.symm hl]
    · simp
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h; push Not at h; exact hv (by ext i; simp [h i])
  have hik : k ≤ i.1 := by
    by_contra h; exact hi (hvk i (by omega))
  have hYi : Y (a₀, i) ≠ 0 := by
    simp only [hY]
    refine mul_ne_zero hca' ?_
    rw [Finset.sum_eq_single i]
    · simp [hB, hik, hi]
    · intro l _ hl; simp [hB, Ne.symm hl]
    · simp
  refine leviForm_log_normSq_line_pos (fun r hr => ?_) (fun h0 => hXj (by rw [h0]; rfl))
  have h1 : Y (a₀, j) = r * X (a₀, j) := by rw [hr]; rfl
  rw [hYj] at h1
  have hr0 : r = 0 := by
    rcases mul_eq_zero.mp h1.symm with h | h
    · exact h
    · exact absurd h hXj
  apply hYi
  rw [hr, hr0, zero_smul]
  rfl

end Hironaka.BlowupWeightLevi
