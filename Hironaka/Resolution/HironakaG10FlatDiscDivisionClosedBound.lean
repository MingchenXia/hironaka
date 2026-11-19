import Hironaka.Resolution.HironakaG10FlatDiscWeierstrassDivision
import Mathlib.Analysis.Complex.AbsMax

/-! # Weierstrass division bounds on the CLOSED disc, in terms of the circle only

Continuation of `HironakaG10FlatDiscWeierstrassDivision`. If the contour radius is
`ρ₁ > ρ` and `W(z,·)` does not vanish on `ρ ≤ |ζ| ≤ ρ₁`, the Cauchy quotient is holomorphic on
`D(0,ρ₁) ⊇ D̄(0,ρ)` and, by the maximum modulus principle, it is bounded on the CLOSED disc
`D̄(0,ρ)` by its values on the circle `|ζ| = ρ`, where `q = (h - r)/W`
(`norm_divQuot_le_of_mem_closedBall`). If moreover `W(z,·)` is monic of degree `b` with all
its roots in `D(0,ρ)`, the remainder does not depend on the contour radius
(`remCoeff_eq_of_roots`), and the quotient on `D̄(0,ρ)` is bounded in terms of the sup of `h`
on the circle `|ζ| = ρ` ALONE (`norm_divQuot_closedBall_le`): this is the estimate that makes
division by a Weierstrass polynomial a bounded operator for the sup norm of the closed polydisc
`K' × D̄(0,ρ)` (privilege, Douady 1966 §7; Frisch 1968 Lemme 3/4).
BP: hironaka-g10-flat-disc-division-closed-bound.tex. -/
set_option autoImplicit false
namespace Hironaka.HironakaG10FlatDiscDivisionClosedBound
open Complex Metric Set Filter
open scoped Real Topology
open HironakaG10FlatDiscWeierstrassDivision
noncomputable section

variable {P : Type*} {b : ℕ} {A : ℕ → P → ℂ} {h : P × ℂ → ℂ}

/-- On a circle inside the contour, the quotient is `(h - r)/W`. -/
theorem divQuot_eq_of_lt {ρ₁ R : ℝ} (hρ₁ : 0 < ρ₁) (hρ₁R : ρ₁ < R) (z : P)
    (hh : DifferentiableOn ℂ (fun ζ => h (z, ζ)) (ball 0 R))
    (hW : ∀ ζ ∈ sphere (0 : ℂ) ρ₁, polyEval b A z ζ ≠ 0) {w : ℂ} (hw : w ∈ ball (0 : ℂ) ρ₁)
    (hWw : polyEval b A z w ≠ 0) :
    divQuot b A h ρ₁ (z, w) = (h (z, w) - divRem b A h ρ₁ (z, w)) / polyEval b A z w := by
  rw [division_eq hρ₁ hρ₁R z hh hW hw]
  field_simp
  ring

/-- **Maximum-modulus bound on the closed disc.** With contour `ρ₁ ∈ (ρ, R)` and
`|h| ≤ M`, `|W| ≥ m > 0` on the circle `|ζ| = ρ`, the quotient satisfies
`|q(z,w)| ≤ (M + ∑_{i<b} |rᵢ(z)| ρⁱ)/m` for ALL `|w| ≤ ρ`. -/
theorem norm_divQuot_le_of_mem_closedBall {ρ ρ₁ R : ℝ} (hρ : 0 < ρ) (hρρ₁ : ρ < ρ₁)
    (hρ₁R : ρ₁ < R) (z : P) (hh : DifferentiableOn ℂ (fun ζ => h (z, ζ)) (ball 0 R))
    (hW₁ : ∀ ζ ∈ sphere (0 : ℂ) ρ₁, polyEval b A z ζ ≠ 0) {M m : ℝ} (hm : 0 < m)
    (hM : ∀ ζ ∈ sphere (0 : ℂ) ρ, ‖h (z, ζ)‖ ≤ M)
    (hmW : ∀ ζ ∈ sphere (0 : ℂ) ρ, m ≤ ‖polyEval b A z ζ‖) {w : ℂ} (hw : w ∈ closedBall (0 : ℂ) ρ) :
    ‖divQuot b A h ρ₁ (z, w)‖ ≤
      (M + ∑ i ∈ Finset.range b, ‖remCoeff b A h ρ₁ i z‖ * ρ ^ i) / m := by
  have hρ₁ : 0 < ρ₁ := hρ.trans hρρ₁
  have hq : DifferentiableOn ℂ (fun w => divQuot b A h ρ₁ (z, w)) (ball 0 ρ₁) :=
    differentiableOn_divQuot_slice hρ₁ hρ₁R z hh hW₁
  have hcl : DiffContOnCl ℂ (fun w => divQuot b A h ρ₁ (z, w)) (ball 0 ρ) :=
    (hq.mono (closure_ball (0 : ℂ) hρ.ne' ▸ closedBall_subset_ball hρρ₁)).diffContOnCl
  refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hcl (fun ζ hζ => ?_)
    (by rwa [closure_ball (0 : ℂ) hρ.ne'])
  rw [frontier_ball (0 : ℂ) hρ.ne'] at hζ
  have hζn : ‖ζ‖ = ρ := mem_sphere_zero_iff_norm.mp hζ
  have hWζ : m ≤ ‖polyEval b A z ζ‖ := hmW ζ hζ
  have hW0 : polyEval b A z ζ ≠ 0 := norm_pos_iff.mp (hm.trans_le hWζ)
  have hζb : ζ ∈ ball (0 : ℂ) ρ₁ := by rw [mem_ball_zero_iff, hζn]; exact hρρ₁
  rw [divQuot_eq_of_lt hρ₁ hρ₁R z hh hW₁ hζb hW0, norm_div]
  have hrem : ‖divRem b A h ρ₁ (z, ζ)‖ ≤ ∑ i ∈ Finset.range b, ‖remCoeff b A h ρ₁ i z‖ * ρ ^ i := by
    unfold divRem
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul, norm_pow, hζn]
  have hnum : ‖h (z, ζ) - divRem b A h ρ₁ (z, ζ)‖ ≤
      M + ∑ i ∈ Finset.range b, ‖remCoeff b A h ρ₁ i z‖ * ρ ^ i :=
    (norm_sub_le _ _).trans (add_le_add (hM ζ hζ) hrem)
  have hnum0 : 0 ≤ M + ∑ i ∈ Finset.range b, ‖remCoeff b A h ρ₁ i z‖ * ρ ^ i :=
    (norm_nonneg _).trans hnum
  calc ‖h (z, ζ) - divRem b A h ρ₁ (z, ζ)‖ / ‖polyEval b A z ζ‖
      ≤ (M + ∑ i ∈ Finset.range b, ‖remCoeff b A h ρ₁ i z‖ * ρ ^ i) / ‖polyEval b A z ζ‖ := by
        gcongr
    _ ≤ (M + ∑ i ∈ Finset.range b, ‖remCoeff b A h ρ₁ i z‖ * ρ ^ i) / m := by
        gcongr

/-- **The remainder does not depend on the contour.** If `W(z,·)` is monic of degree `b` with
all its roots in `D(0,ρ)`, the Cauchy remainders and quotients for the contours `ρ` and
`ρ₁ ∈ (ρ, R)` agree. -/
theorem remCoeff_eq_of_roots [NormedAddCommGroup P] [NormedSpace ℂ P] {ρ ρ₁ R : ℝ} (hρ : 0 < ρ)
    (hρρ₁ : ρ < ρ₁) (hρ₁R : ρ₁ < R) (z : P)
    (hh : DifferentiableOn ℂ (fun ζ => h (z, ζ)) (ball 0 R)) (hmon : A b z = 1)
    (hroots : ∀ α, polyEval b A z α = 0 → α ∈ ball (0 : ℂ) ρ) :
    (∀ i < b, remCoeff b A h ρ₁ i z = remCoeff b A h ρ i z) ∧
      EqOn (fun w => divQuot b A h ρ₁ (z, w)) (fun w => divQuot b A h ρ (z, w)) (ball 0 ρ) := by
  have hρ₁ : 0 < ρ₁ := hρ.trans hρρ₁
  have hW₁ : ∀ ζ ∈ sphere (0 : ℂ) ρ₁, polyEval b A z ζ ≠ 0 := by
    intro ζ hζ h0
    have := hroots ζ h0
    rw [mem_ball_zero_iff, mem_sphere_zero_iff_norm.mp hζ] at this
    exact lt_irrefl _ (this.trans hρρ₁)
  have hq₁ : ContinuousOn (fun w => divQuot b A h ρ₁ (z, w)) (ball 0 ρ) :=
    ((differentiableOn_divQuot_slice hρ₁ hρ₁R z hh hW₁).mono
      (ball_subset_ball hρρ₁.le)).continuousOn
  have hdiv : ∀ w ∈ ball (0 : ℂ) ρ, h (z, w) = polyEval b A z w * divQuot b A h ρ₁ (z, w) +
      ∑ i ∈ Finset.range b, remCoeff b A h ρ₁ i z * w ^ i := fun w hw =>
    division_eq hρ₁ hρ₁R z hh hW₁ (ball_subset_ball hρρ₁.le hw)
  exact eq_divQuot_remCoeff hρ (hρρ₁.trans hρ₁R) z hh hmon hroots _ hq₁ _ hdiv

/-- **Division bound on the closed disc in terms of the circle `|ζ| = ρ` alone.** If `W(z,·)`
is monic of degree `b` with all its roots in `D(0,ρ)`, `|h| ≤ M`, `|W| ≥ m > 0` and
`|cᵢ| ≤ Bᵢ` on `|ζ| = ρ`, then for every contour `ρ₁ ∈ (ρ, R)` and every `|w| ≤ ρ`,
`|q(z,w)| ≤ (M + ∑_{i<b} ρ (M Bᵢ / m) ρⁱ)/m`, and `|rᵢ(z)| ≤ ρ M Bᵢ / m`. -/
theorem norm_divQuot_closedBall_le [NormedAddCommGroup P] [NormedSpace ℂ P] {ρ ρ₁ R : ℝ}
    (hρ : 0 < ρ) (hρρ₁ : ρ < ρ₁) (hρ₁R : ρ₁ < R) (z : P)
    (hh : DifferentiableOn ℂ (fun ζ => h (z, ζ)) (ball 0 R)) (hmon : A b z = 1)
    (hroots : ∀ α, polyEval b A z α = 0 → α ∈ ball (0 : ℂ) ρ)
    {M m : ℝ} (B : ℕ → ℝ) (hm : 0 < m) (hM : ∀ ζ ∈ sphere (0 : ℂ) ρ, ‖h (z, ζ)‖ ≤ M)
    (hmW : ∀ ζ ∈ sphere (0 : ℂ) ρ, m ≤ ‖polyEval b A z ζ‖)
    (hB : ∀ i, ∀ ζ ∈ sphere (0 : ℂ) ρ, ‖diffCoeff b A i z ζ‖ ≤ B i) :
    (∀ i < b, ‖remCoeff b A h ρ₁ i z‖ ≤ ρ * (M * B i / m)) ∧
      ∀ w ∈ closedBall (0 : ℂ) ρ, ‖divQuot b A h ρ₁ (z, w)‖ ≤
        (M + ∑ i ∈ Finset.range b, ρ * (M * B i / m) * ρ ^ i) / m := by
  have hW₁ : ∀ ζ ∈ sphere (0 : ℂ) ρ₁, polyEval b A z ζ ≠ 0 := by
    intro ζ hζ h0
    have := hroots ζ h0
    rw [mem_ball_zero_iff, mem_sphere_zero_iff_norm.mp hζ] at this
    exact lt_irrefl _ (this.trans hρρ₁)
  obtain ⟨hrem, -⟩ := remCoeff_eq_of_roots hρ hρρ₁ hρ₁R z hh hmon hroots
  have hr : ∀ i < b, ‖remCoeff b A h ρ₁ i z‖ ≤ ρ * (M * B i / m) := fun i hi => by
    rw [hrem i hi]
    exact norm_remCoeff_le hρ i z hm hM (hB i) hmW
  refine ⟨hr, fun w hw => ?_⟩
  refine (norm_divQuot_le_of_mem_closedBall hρ hρρ₁ hρ₁R z hh hW₁ hm hM hmW hw).trans ?_
  gcongr with i hi
  exact hr i (Finset.mem_range.mp hi)

end
end Hironaka.HironakaG10FlatDiscDivisionClosedBound
