import Hironaka.Analytic.DemaillyAnalyticType

set_option autoImplicit false

/-!
# Exact holomorphic frame changes for finite Bergman generators

This is the algebraic step behind overlap log-sum descent.  If two local
potentials satisfy `Re g = σ - ρ` and `c > 0`, then the nonvanishing frame
`h = exp (g / (2c))` changes a generator family `f` into `h f`.  The
normalization is exact:

`c log Σ |h fⱼ|² - σ = c log Σ |fⱼ|² - ρ`.

All factors are retained explicitly.  In particular, the proof treats the
common-zero case of a generator family, so no illegal subtraction at a pole is
used.  This is a local algebra/analysis lemma; obtaining the additive
transition `g` and a cocycle-compatible finite family remains separate.
-/

open scoped BigOperators

namespace Hironaka.BergmanGeneratorFrameChange

noncomputable section

/-- A finite generator norm scales by the squared norm of a scalar frame. -/
theorem generatorNormSq_mul_scalar
    {X : Type*} {p : ℕ} (a : ℂ) (f : Fin p → X → ℂ) (y : X) :
    generatorNormSq (fun j z => a * f j z) y =
      Complex.normSq a * generatorNormSq f y := by
  simp only [generatorNormSq, norm_mul, mul_pow]
  rw [← Finset.mul_sum, Complex.normSq_eq_norm_sq]

/-- Generator logarithms respect multiplication by a nonzero scalar frame.
The added term is finite, while a common generator zero remains `⊥` on both
sides. -/
theorem generatorLog_mul_scalar
    {X : Type*} {p : ℕ} (a : ℂ) (ha : a ≠ 0)
    (f : Fin p → X → ℂ) (y : X) :
    generatorLog (fun j z => a * f j z) y =
      generatorLog f y + (Real.log (Complex.normSq a) : EReal) := by
  have hApos : 0 < Complex.normSq a := Complex.normSq_pos.mpr ha
  have hnorm := generatorNormSq_mul_scalar a f y
  by_cases hF : generatorNormSq f y = 0
  · have hvec : generatorVector f y = 0 := by
      apply norm_eq_zero.mp
      apply sq_eq_zero_iff.mp
      rw [generatorVector_norm_sq]
      exact hF
    have hfzero : ∀ j, f j y = 0 :=
      (generatorVector_eq_zero_iff f y).mp hvec
    have hscaledzero : ∀ j, a * f j y = 0 := by
      intro j
      rw [hfzero j, mul_zero]
    have hfbot : generatorLog f y = ⊥ :=
      (generatorLog_eq_bot_iff f y).mpr hfzero
    have hsbot : generatorLog (fun j z => a * f j z) y = ⊥ :=
      (generatorLog_eq_bot_iff (fun j z => a * f j z) y).mpr hscaledzero
    rw [hsbot, hfbot]
    simp
  · have hFpos : 0 < generatorNormSq f y :=
      lt_of_le_of_ne (generatorNormSq_nonneg f y) (Ne.symm hF)
    have hf : ∃ j, f j y ≠ 0 := by
      by_contra hnone
      simp only [not_exists, not_not] at hnone
      apply hF
      simp [generatorNormSq, hnone]
    have hs : ∃ j, a * f j y ≠ 0 := by
      obtain ⟨j, hj⟩ := hf
      exact ⟨j, mul_ne_zero ha hj⟩
    rw [generatorLog_of_nonzero hs, hnorm, generatorLog_of_nonzero hf,
      Real.log_mul hApos.ne' hFpos.ne', EReal.coe_add]
    ac_rfl

/-- Pointwise equality of finite generator values gives equality of their
logarithmic norms at that point. -/
theorem generatorLog_congr_at
    {X : Type*} {p : ℕ} {f q : Fin p → X → ℂ} {y : X}
    (h : ∀ j, f j y = q j y) : generatorLog f y = generatorLog q y := by
  rw [generatorLog_eq_log_sum, generatorLog_eq_log_sum]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  rw [h j]

/-- The multiplicative frame associated to an additive holomorphic transition.
Writing the reciprocal factor as a real scalar inside `ℂ` makes its precise
normalization visible. -/
def holomorphicFrame {X : Type*} (c : ℝ) (g : X → ℂ) : X → ℂ :=
  fun y => Complex.exp (((((2 * c)⁻¹ : ℝ) : ℂ) * g y))

/-- Exponentials never vanish, so the frame can be used in the scalar
generator-log identity. -/
theorem holomorphicFrame_ne_zero
    {X : Type*} (c : ℝ) (g : X → ℂ) (y : X) : holomorphicFrame c g y ≠ 0 :=
  Complex.exp_ne_zero _

/-- The squared norm of `exp (g / (2c))` has exactly the logarithm required
to absorb the difference of two local potentials. -/
theorem log_normSq_holomorphicFrame
    {X : Type*} (c : ℝ) (hc : 0 < c) (g : X → ℂ) (y : X) :
    Real.log (Complex.normSq (holomorphicFrame c g y)) = (g y).re / c := by
  unfold holomorphicFrame
  rw [Complex.normSq_eq_norm_sq, Complex.norm_exp, pow_two,
    ← Real.exp_add, Real.log_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  field_simp [hc.ne']
  ring

/-- **Exact frame-change identity.**  Given the real-part transition formula
`Re g = σ - ρ`, multiplying every generator by
`exp (g / (2c))` changes the local smooth remainder from `ρ` to `σ` with no
bounded-error replacement and no maximum operation. -/
theorem exact_frameChange_generatorLog
    {X : Type*} {p : ℕ} (c : ℝ) (hc : 0 < c) (g : X → ℂ)
    (ρ σ : X → ℝ) (f : Fin p → X → ℂ) (y : X)
    (hre : (g y).re = σ y - ρ y) :
    (c : EReal) * generatorLog (fun j z => holomorphicFrame c g z * f j z) y -
        (σ y : EReal) =
      (c : EReal) * generatorLog f y - (ρ y : EReal) := by
  have hframe : holomorphicFrame c g y ≠ 0 := holomorphicFrame_ne_zero c g y
  have hcongr : generatorLog (fun j z => holomorphicFrame c g z * f j z) y =
      generatorLog (fun j z => holomorphicFrame c g y * f j z) y :=
    generatorLog_congr_at fun j => rfl
  have hscalar := generatorLog_mul_scalar (holomorphicFrame c g y) hframe f y
  have hlog := log_normSq_holomorphicFrame c hc g y
  have hreal : c * Real.log (Complex.normSq (holomorphicFrame c g y)) =
      σ y - ρ y := by
    rw [hlog, hre]
    field_simp [hc.ne']
  have hscale : (c : EReal) *
      (Real.log (Complex.normSq (holomorphicFrame c g y)) : EReal) =
        ((σ y - ρ y : ℝ) : EReal) := by
    rw [← EReal.coe_mul]
    exact congrArg (fun r : ℝ => (r : EReal)) hreal
  have hcEreal_nonneg : 0 ≤ (c : EReal) := EReal.coe_nonneg.mpr hc.le
  have hcEreal_ne_top : (c : EReal) ≠ ⊤ := EReal.coe_ne_top c
  rw [hcongr, hscalar,
    EReal.left_distrib_of_nonneg_of_ne_top hcEreal_nonneg hcEreal_ne_top]
  calc
    ((c : EReal) * generatorLog f y +
        (c : EReal) *
          (Real.log (Complex.normSq (holomorphicFrame c g y)) : EReal)) -
        (σ y : EReal) =
      ((c : EReal) * generatorLog f y + ((σ y - ρ y : ℝ) : EReal)) -
        (σ y : EReal) := by rw [hscale]
    _ = (c : EReal) * generatorLog f y - (ρ y : EReal) := by
      have hfinite : ((σ y - ρ y : ℝ) : EReal) + -(σ y : EReal) =
          -(ρ y : EReal) := by
        rw [← EReal.coe_neg, ← EReal.coe_add]
        congr 1
        ring
      calc
        ((c : EReal) * generatorLog f y + ((σ y - ρ y : ℝ) : EReal)) -
            (σ y : EReal) =
          (c : EReal) * generatorLog f y +
            (((σ y - ρ y : ℝ) : EReal) + -(σ y : EReal)) := by
              rw [sub_eq_add_neg, add_assoc]
        _ = (c : EReal) * generatorLog f y + -(ρ y : EReal) := by rw [hfinite]
        _ = (c : EReal) * generatorLog f y - (ρ y : EReal) :=
          (sub_eq_add_neg _ _).symm

end

end Hironaka.BergmanGeneratorFrameChange
