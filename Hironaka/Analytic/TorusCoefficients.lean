import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.DSlope

set_option autoImplicit false

/-!
# Taylor coefficients on a torus

For a point `p` of `ℂ^{m+1}` (as `EuclideanSpace ℂ (Fin (m + 1))`), a radius `s` and a
multi-index `α ∈ ℤ^{m+1}`, `torusCoeff p s α q` is the Fourier coefficient

  `∫_{[0,2π]^m} ∫_0^{2π} q (p + s e^{iθ}) e^{-i⟨α, θ⟩} dθ_last dθ'`

of `q` on the torus `|z_i - p_i| = s`.  The integral is iterated, with the last angle
innermost.  For `q` holomorphic near the closed polydisc these are, by Cauchy's formula,
`(2π)^{m+1} s^{|α|}` times the Taylor coefficients of `q` at `p` (and `0` if some
`α_i < 0`).  That identification is not needed here.  This module proves the
facts the strong-openness argument uses:

* `torusCoeff_add`, `torusCoeff_const_mul`, `torusCoeff_sub`: linearity on functions that are
  continuous along the torus;
* `torusCoeff_mul_last`: multiplication by `z_last - p_last` shifts the last index by one
  and multiplies by `s`.  This is a pointwise identity of integrands;
* `torusCoeff_eq_zero_of_last_neg`: a function holomorphic in the last variable on a
  neighbourhood of the closed disc has vanishing coefficients whenever `α_last < 0`
  (Cauchy's theorem in one variable, inside the iterated integral);
* `norm_torusCoeff_le`: `‖torusCoeff p s α q‖ ≤ (2π)^{m+1} sup_torus ‖q‖`.
-/

open Set Filter MeasureTheory Complex
open scoped Real Topology

namespace Hironaka

noncomputable section

variable {m : ℕ}

/-- The point of the torus of centre `p` and radius `s` with angles `θ`. -/
def torusPoint (p : EuclideanSpace ℂ (Fin (m + 1))) (s : ℝ) (θ : Fin (m + 1) → ℝ) :
    EuclideanSpace ℂ (Fin (m + 1)) :=
  p + WithLp.toLp 2 (fun i => (s : ℂ) * exp (θ i * I))

/-- The complex line through the torus point with first angles `θ'`, in the last
coordinate: `ζ ↦ p + (s e^{iθ'}, ζ)`. -/
def torusLastLine (p : EuclideanSpace ℂ (Fin (m + 1))) (s : ℝ) (θ' : Fin m → ℝ) (ζ : ℂ) :
    EuclideanSpace ℂ (Fin (m + 1)) :=
  p + WithLp.toLp 2 (Fin.snoc (α := fun _ => ℂ) (fun i => (s : ℂ) * exp (θ' i * I)) ζ)

theorem torusPoint_snoc (p : EuclideanSpace ℂ (Fin (m + 1))) (s : ℝ) (θ' : Fin m → ℝ)
    (θ : ℝ) : torusPoint p s (Fin.snoc (α := fun _ => ℝ) θ' θ) =
      torusLastLine p s θ' ((s : ℂ) * exp (θ * I)) := by
  unfold torusPoint torusLastLine
  congr 2
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem continuous_torusPoint (p : EuclideanSpace ℂ (Fin (m + 1))) (s : ℝ) :
    Continuous (torusPoint p s) := by
  unfold torusPoint
  refine continuous_const.add ?_
  refine (PiLp.continuous_toLp 2 _).comp ?_
  fun_prop

theorem differentiable_torusLastLine (p : EuclideanSpace ℂ (Fin (m + 1))) (s : ℝ)
    (θ' : Fin m → ℝ) : Differentiable ℂ (torusLastLine p s θ') := by
  have : torusLastLine p s θ' = fun ζ => torusLastLine p s θ' 0 +
      ζ • EuclideanSpace.single (Fin.last m) (1 : ℂ) := by
    funext ζ
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;>
      simp [torusLastLine, Fin.castSucc_ne_last]
  rw [this]
  fun_prop

/-- The last coordinate of a torus point. -/
theorem torusPoint_last (p : EuclideanSpace ℂ (Fin (m + 1))) (s : ℝ) (θ : Fin (m + 1) → ℝ) :
    torusPoint p s θ (Fin.last m) - p (Fin.last m) = (s : ℂ) * exp (θ (Fin.last m) * I) := by
  simp [torusPoint]

theorem norm_torusPoint_sub (p : EuclideanSpace ℂ (Fin (m + 1))) {s : ℝ} (hs : 0 ≤ s)
    (θ : Fin (m + 1) → ℝ) (i : Fin (m + 1)) : ‖torusPoint p s θ i - p i‖ = s := by
  simp [torusPoint, norm_exp_ofReal_mul_I, abs_of_nonneg hs]

/-! ### Iterated integrals over the angle box -/

/-- The iterated integral over `[0, 2π]^{m+1}`, the last angle innermost. -/
def angleIntegral (G : (Fin (m + 1) → ℝ) → ℂ) : ℂ :=
  ∫ θ' in Icc (0 : Fin m → ℝ) (fun _ => 2 * π),
    ∫ θ in (0 : ℝ)..2 * π, G (Fin.snoc (α := fun _ => ℝ) θ' θ)

theorem continuous_angleIntegral_inner {G : (Fin (m + 1) → ℝ) → ℂ} (hG : Continuous G) :
    Continuous fun θ' : Fin m → ℝ =>
      ∫ θ in (0 : ℝ)..2 * π, G (Fin.snoc (α := fun _ => ℝ) θ' θ) := by
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun θ' θ => G (Fin.snoc (α := fun _ => ℝ) θ' θ)) ?_ _ _
  exact hG.comp (by fun_prop)

theorem angleIntegral_add {G H : (Fin (m + 1) → ℝ) → ℂ} (hG : Continuous G)
    (hH : Continuous H) :
    angleIntegral (fun θ => G θ + H θ) = angleIntegral G + angleIntegral H := by
  unfold angleIntegral
  rw [← integral_add ((continuous_angleIntegral_inner hG).integrableOn_Icc)
    ((continuous_angleIntegral_inner hH).integrableOn_Icc)]
  refine setIntegral_congr_fun measurableSet_Icc fun θ' _ => ?_
  exact intervalIntegral.integral_add
    ((hG.comp (by fun_prop)).intervalIntegrable _ _)
    ((hH.comp (by fun_prop)).intervalIntegrable _ _)

theorem angleIntegral_const_mul (a : ℂ) (G : (Fin (m + 1) → ℝ) → ℂ) :
    angleIntegral (fun θ => a * G θ) = a * angleIntegral G := by
  unfold angleIntegral
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Icc fun θ' _ => ?_
  exact intervalIntegral.integral_const_mul a _

theorem angleIntegral_congr {G H : (Fin (m + 1) → ℝ) → ℂ} (h : ∀ θ, G θ = H θ) :
    angleIntegral G = angleIntegral H := by
  simp only [angleIntegral, h]

theorem norm_angleIntegral_le {G : (Fin (m + 1) → ℝ) → ℂ} {C : ℝ} (hC : ∀ θ, ‖G θ‖ ≤ C) :
    ‖angleIntegral G‖ ≤ (2 * π) ^ (m + 1) * C := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  unfold angleIntegral
  have hvol : volume.real (Icc (0 : Fin m → ℝ) fun _ => 2 * π) = (2 * π) ^ m := by
    rw [measureReal_def, show (0 : Fin m → ℝ) = fun _ => 0 from rfl, Real.volume_Icc_pi_toReal fun _ => Real.two_pi_pos.le]
    simp
  calc ‖∫ θ' in Icc (0 : Fin m → ℝ) (fun _ => 2 * π),
          ∫ θ in (0 : ℝ)..2 * π, G (Fin.snoc (α := fun _ => ℝ) θ' θ)‖
      ≤ (C * |2 * π - 0|) * volume.real (Icc (0 : Fin m → ℝ) fun _ => 2 * π) :=
        norm_setIntegral_le_of_norm_le_const measure_Icc_lt_top fun θ' _ =>
          intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ => hC _
    _ = (2 * π) ^ (m + 1) * C := by
        rw [hvol, sub_zero, abs_of_pos Real.two_pi_pos, pow_succ]
        ring

/-! ### The coefficients -/

/-- The phase `e^{-i⟨α, θ⟩}`. -/
def anglePhase (α : Fin (m + 1) → ℤ) (θ : Fin (m + 1) → ℝ) : ℂ :=
  exp (-(∑ i, (α i : ℂ) * (θ i : ℂ)) * I)

theorem continuous_anglePhase (α : Fin (m + 1) → ℤ) : Continuous (anglePhase α) := by
  unfold anglePhase
  fun_prop

theorem norm_anglePhase (α : Fin (m + 1) → ℤ) (θ : Fin (m + 1) → ℝ) :
    ‖anglePhase α θ‖ = 1 := by
  unfold anglePhase
  have : -(∑ i, (α i : ℂ) * (θ i : ℂ)) = ((-(∑ i, (α i : ℝ) * θ i) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [this, norm_exp_ofReal_mul_I]

/-- The torus coefficient of index `α ∈ ℤ^{m+1}`. -/
def torusCoeff (p : EuclideanSpace ℂ (Fin (m + 1))) (s : ℝ) (α : Fin (m + 1) → ℤ)
    (q : EuclideanSpace ℂ (Fin (m + 1)) → ℂ) : ℂ :=
  angleIntegral fun θ => q (torusPoint p s θ) * anglePhase α θ

variable {p : EuclideanSpace ℂ (Fin (m + 1))} {s : ℝ}

/-- `q` is continuous along the torus. -/
def ContinuousOnTorus (p : EuclideanSpace ℂ (Fin (m + 1))) (s : ℝ)
    (q : EuclideanSpace ℂ (Fin (m + 1)) → ℂ) : Prop :=
  Continuous fun θ => q (torusPoint p s θ)

theorem torusCoeff_add {q₁ q₂ : EuclideanSpace ℂ (Fin (m + 1)) → ℂ}
    (h₁ : ContinuousOnTorus p s q₁) (h₂ : ContinuousOnTorus p s q₂) (α : Fin (m + 1) → ℤ) :
    torusCoeff p s α (q₁ + q₂) = torusCoeff p s α q₁ + torusCoeff p s α q₂ := by
  unfold torusCoeff
  rw [← angleIntegral_add (G := fun θ => q₁ (torusPoint p s θ) * anglePhase α θ)
    (H := fun θ => q₂ (torusPoint p s θ) * anglePhase α θ)
    (h₁.mul (continuous_anglePhase α)) (h₂.mul (continuous_anglePhase α))]
  exact angleIntegral_congr fun θ => by simp [add_mul]

theorem torusCoeff_const_mul (a : ℂ) (q : EuclideanSpace ℂ (Fin (m + 1)) → ℂ)
    (α : Fin (m + 1) → ℤ) :
    torusCoeff p s α (fun z => a * q z) = a * torusCoeff p s α q := by
  unfold torusCoeff
  rw [← angleIntegral_const_mul]
  exact angleIntegral_congr fun θ => by ring

theorem torusCoeff_sub {q₁ q₂ : EuclideanSpace ℂ (Fin (m + 1)) → ℂ}
    (h₁ : ContinuousOnTorus p s q₁) (h₂ : ContinuousOnTorus p s q₂) (α : Fin (m + 1) → ℤ) :
    torusCoeff p s α (q₁ - q₂) = torusCoeff p s α q₁ - torusCoeff p s α q₂ := by
  have h₂' : ContinuousOnTorus p s (fun z => (-1 : ℂ) * q₂ z) := continuous_const.mul h₂
  have := torusCoeff_add h₁ h₂' α
  rw [torusCoeff_const_mul] at this
  have e : q₁ - q₂ = q₁ + fun z => (-1 : ℂ) * q₂ z := by
    funext z; simp [sub_eq_add_neg]
  rw [e, this]
  ring

theorem torusCoeff_congr {q₁ q₂ : EuclideanSpace ℂ (Fin (m + 1)) → ℂ}
    (h : ∀ θ, q₁ (torusPoint p s θ) = q₂ (torusPoint p s θ)) (α : Fin (m + 1) → ℤ) :
    torusCoeff p s α q₁ = torusCoeff p s α q₂ := by
  unfold torusCoeff
  exact angleIntegral_congr fun θ => by rw [h]

/-- Multiplication by `z_last - p_last` shifts the last index down by one, times `s`. -/
theorem torusCoeff_mul_last (q : EuclideanSpace ℂ (Fin (m + 1)) → ℂ) (α : Fin (m + 1) → ℤ) :
    torusCoeff p s α (fun z => (z (Fin.last m) - p (Fin.last m)) * q z) =
      (s : ℂ) * torusCoeff p s (α - Pi.single (Fin.last m) 1) q := by
  unfold torusCoeff
  rw [← angleIntegral_const_mul]
  refine angleIntegral_congr fun θ => ?_
  beta_reduce
  rw [torusPoint_last]
  unfold anglePhase
  have hsum : (∑ i, ((((α - Pi.single (Fin.last m) (1 : ℤ) : Fin (m + 1) → ℤ)) i : ℤ) : ℂ) * (θ i : ℂ)) =
      (∑ i, (α i : ℂ) * (θ i : ℂ)) - (θ (Fin.last m) : ℂ) := by
    simp only [Pi.sub_apply, Int.cast_sub, sub_mul, Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_eq_single (Fin.last m)]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  rw [hsum]
  have : exp (-(∑ i, (α i : ℂ) * (θ i : ℂ) - (θ (Fin.last m) : ℂ)) * I) =
      exp ((θ (Fin.last m) : ℂ) * I) * exp (-(∑ i, (α i : ℂ) * (θ i : ℂ)) * I) := by
    rw [← exp_add]; congr 1; ring
  rw [this]
  ring

/-- **Cauchy's theorem in the last variable.**  If `q` is holomorphic in the last variable
on a disc of radius `s' > s` along every line of the torus, its coefficients with
negative last index vanish. -/
theorem torusCoeff_eq_zero_of_last_neg {q : EuclideanSpace ℂ (Fin (m + 1)) → ℂ} {s' : ℝ}
    (hs : 0 < s) (hss' : s < s')
    (hq : ∀ θ' : Fin m → ℝ, DifferentiableOn ℂ (fun ζ => q (torusLastLine p s θ' ζ))
      (Metric.ball 0 s'))
    {α : Fin (m + 1) → ℤ} (hα : α (Fin.last m) < 0) : torusCoeff p s α q = 0 := by
  unfold torusCoeff angleIntegral
  refine (setIntegral_congr_fun measurableSet_Icc fun θ' _ => ?_).trans (integral_zero _ _)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, α (Fin.last m) = -((k : ℤ) + 1) :=
    ⟨(-α (Fin.last m) - 1).toNat, by omega⟩
  set h : ℂ → ℂ := fun ζ => q (torusLastLine p s θ' ζ) with hh
  set c : ℂ := exp (-(∑ i : Fin m, (α i.castSucc : ℂ) * (θ' i : ℂ)) * I) with hc
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hint : ∀ θ : ℝ, q (torusPoint p s (Fin.snoc (α := fun _ => ℝ) θ' θ)) *
      anglePhase α (Fin.snoc (α := fun _ => ℝ) θ' θ) =
      (c / (I * (s : ℂ) ^ (k + 1))) *
        (deriv (circleMap 0 s) θ • (h (circleMap 0 s θ) * circleMap 0 s θ ^ k)) := by
    intro θ
    rw [torusPoint_snoc]
    have hsum : (∑ i, ((α i : ℤ) : ℂ) * ((Fin.snoc (α := fun _ => ℝ) θ' θ i : ℝ) : ℂ)) =
        (∑ i : Fin m, (α i.castSucc : ℂ) * (θ' i : ℂ)) - ((k : ℂ) + 1) * θ := by
      rw [Fin.sum_univ_castSucc]
      simp [hk]
      ring
    have hexp : anglePhase α (Fin.snoc (α := fun _ => ℝ) θ' θ) =
        c * (exp (θ * I) * exp (θ * I) ^ k) := by
      rw [anglePhase, hsum, hc, ← exp_nat_mul, ← exp_add, ← exp_add]
      congr 1
      ring
    rw [hexp, deriv_circleMap]
    simp only [circleMap, zero_add, smul_eq_mul, hh]
    field_simp
    ring
  simp_rw [hint]
  rw [intervalIntegral.integral_const_mul]
  have hci : (∮ ζ in C(0, s), h ζ * ζ ^ k) =
      ∫ θ in (0 : ℝ)..2 * π, deriv (circleMap 0 s) θ • (h (circleMap 0 s θ) *
        circleMap 0 s θ ^ k) := rfl
  rw [← hci]
  have hdiff : DifferentiableOn ℂ (fun ζ => h ζ * ζ ^ k) (Metric.ball 0 s') :=
    (hq θ').mul (differentiableOn_id.pow k)
  have hsub : Metric.closedBall (0 : ℂ) s ⊆ Metric.ball 0 s' :=
    Metric.closedBall_subset_ball hss'
  rw [circleIntegral_eq_zero_of_differentiable_on_off_countable hs.le countable_empty
    (hdiff.continuousOn.mono hsub)
    (fun z hz => hdiff.differentiableAt (Metric.isOpen_ball.mem_nhds
      (Metric.ball_subset_ball hss'.le hz.1))), mul_zero]

/-- The coefficients are bounded by `(2π)^{m+1}` times a bound along the torus. -/
theorem norm_torusCoeff_le {q : EuclideanSpace ℂ (Fin (m + 1)) → ℂ} {C : ℝ}
    (hC : ∀ θ, ‖q (torusPoint p s θ)‖ ≤ C) (α : Fin (m + 1) → ℤ) :
    ‖torusCoeff p s α q‖ ≤ (2 * π) ^ (m + 1) * C := by
  unfold torusCoeff
  refine norm_angleIntegral_le fun θ => ?_
  rw [norm_mul, norm_anglePhase, mul_one]
  exact hC θ

end

end Hironaka
