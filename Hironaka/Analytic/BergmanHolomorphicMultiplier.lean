import Hironaka.Analytic.BergmanSupWeight

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Multiplication by `e^a` is an isometry of weighted Bergman spaces

Source: Copy-4, `lem:regularization`, Step 2, the sentence

> Multiplication by `e^{m a_j/2}` is an isometry from `H_{j,m}` onto the Hilbert space of
> holomorphic functions on `B_j` which are square integrable against `e^{-mΨ} dV_Z`

(`transcendental-nakamaye-copy4-20260911`).

This is the transformation rule that lets Copy-4 compare the two overlapping balls against a
*common* weight `Ψ` and then translate the comparison back to the own weights of the two balls:
with `h_j - H_{jl} = Re a_j` for a holomorphic `a_j`,

  `φ_{j,m} = Ψ_{j,m} + H_{jl}`,   `φ_{l,m} = Ψ_{l,m} + H_{jl}`,

so `H_{jl}` cancels in the difference and the common-weight comparison of
`Hironaka.QuantitativeRegularizationBergmanOverlap` becomes Copy-4's `eq:reg-overlap`.

The Lean form is an exact identity of Bergman sup-weights: for holomorphic `a` on `D`,

  `bergmanSup D (e^{-2 Re a} · w) y = e^{2 Re a y} · bergmanSup D w y`,

proved by the explicit bijection `f ↦ e^a f` of the two weighted unit balls, whose inverse is
`f ↦ e^{-a} f`.  Nothing here is asymptotic and nothing is lost: the two sides are equal.

The holomorphic `a` itself, for a prescribed pluriharmonic real part on a ball, is
`Hironaka.PrescribedBallPotentials.exists_holomorphic_re_eq_ball`.
-/

open Set MeasureTheory
open scoped ENNReal

namespace Hironaka.BergmanHolomorphicMultiplier

noncomputable section

open BergmanSupWeight

variable {d : ℕ} [MeasurableSpace (ComplexModel d)] [BorelSpace (ComplexModel d)]

/-- `‖e^a c‖² = e^{2 Re a} ‖c‖²`. -/
theorem normSq_exp_mul (a c : ℂ) :
    ‖Complex.exp a * c‖ ^ 2 = Real.exp (2 * a.re) * ‖c‖ ^ 2 := by
  rw [norm_mul, mul_pow, Complex.norm_exp, two_mul, Real.exp_add, sq]

/-- The pointwise form of the isometry: the integrand is unchanged. -/
theorem integrand_exp_mul {a : ComplexModel d → ℂ} {f : ComplexModel d → ℂ}
    (w : ComplexModel d → ℝ≥0∞) (z : ComplexModel d) :
    ENNReal.ofReal (‖Complex.exp (a z) * f z‖ ^ 2) *
        (ENNReal.ofReal (Real.exp (-(2 * (a z).re))) * w z) =
      ENNReal.ofReal (‖f z‖ ^ 2) * w z := by
  rw [normSq_exp_mul, ENNReal.ofReal_mul (Real.exp_pos _).le]
  rw [show ENNReal.ofReal (Real.exp (2 * (a z).re)) *
      ENNReal.ofReal (‖f z‖ ^ 2) *
      (ENNReal.ofReal (Real.exp (-(2 * (a z).re))) * w z) =
    (ENNReal.ofReal (Real.exp (2 * (a z).re)) *
      ENNReal.ofReal (Real.exp (-(2 * (a z).re)))) *
      (ENNReal.ofReal (‖f z‖ ^ 2) * w z) by ring]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_neg_cancel,
    Real.exp_zero, ENNReal.ofReal_one, one_mul]

/-- Multiplication by `e^a` maps the `w`-unit ball into the `e^{-2 Re a} w`-unit ball. -/
theorem exp_mul_mem_bergmanBall {D : Set (ComplexModel d)} {a : ComplexModel d → ℂ}
    (ha : DifferentiableOn ℂ a D) {w : ComplexModel d → ℝ≥0∞}
    {f : ComplexModel d → ℂ} (hf : f ∈ bergmanBall D w) :
    (fun z => Complex.exp (a z) * f z) ∈
      bergmanBall D (fun z => ENNReal.ofReal (Real.exp (-(2 * (a z).re))) * w z) := by
  refine ⟨(ha.cexp).mul hf.1, ?_⟩
  calc ∫⁻ z in D, ENNReal.ofReal (‖Complex.exp (a z) * f z‖ ^ 2) *
        (ENNReal.ofReal (Real.exp (-(2 * (a z).re))) * w z)
      = ∫⁻ z in D, ENNReal.ofReal (‖f z‖ ^ 2) * w z :=
        lintegral_congr fun z => integrand_exp_mul w z
    _ ≤ 1 := hf.2

/-- **The holomorphic multiplier isometry, at the level of Bergman sup-weights**
(Copy-4, `lem:regularization`, Step 2). -/
theorem bergmanSup_exp_weight {D : Set (ComplexModel d)} {a : ComplexModel d → ℂ}
    (ha : DifferentiableOn ℂ a D) (w : ComplexModel d → ℝ≥0∞) (y : ComplexModel d) :
    bergmanSup D (fun z => ENNReal.ofReal (Real.exp (-(2 * (a z).re))) * w z) y =
      ENNReal.ofReal (Real.exp (2 * (a y).re)) * bergmanSup D w y := by
  set w' : ComplexModel d → ℝ≥0∞ :=
    fun z => ENNReal.ofReal (Real.exp (-(2 * (a z).re))) * w z with hw'
  refine le_antisymm (bergmanSup_le fun g hg => ?_) ?_
  · -- divide by `e^a`
    have hinv : (fun z => Complex.exp (-a z) * g z) ∈ bergmanBall D w := by
      refine ⟨((ha.neg).cexp).mul hg.1, ?_⟩
      have hpt : ∀ z, ENNReal.ofReal (‖Complex.exp (-a z) * g z‖ ^ 2) * w z =
          ENNReal.ofReal (‖g z‖ ^ 2) * w' z := by
        intro z
        -- rewrite `g` as `e^{a} · (e^{-a} g)` and apply the pointwise identity
        have hgz : g z = Complex.exp (a z) * (Complex.exp (-a z) * g z) := by
          rw [show Complex.exp (a z) * (Complex.exp (-a z) * g z) =
            (Complex.exp (a z) * Complex.exp (-a z)) * g z by ring,
            ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
        rw [hw']
        conv_rhs => rw [hgz]
        rw [integrand_exp_mul (a := a) (f := fun z => Complex.exp (-a z) * g z) w z]
      calc ∫⁻ z in D, ENNReal.ofReal (‖Complex.exp (-a z) * g z‖ ^ 2) * w z
          = ∫⁻ z in D, ENNReal.ofReal (‖g z‖ ^ 2) * w' z := lintegral_congr hpt
        _ ≤ 1 := hg.2
    have hval : ENNReal.ofReal (‖g y‖ ^ 2) =
        ENNReal.ofReal (Real.exp (2 * (a y).re)) *
          ENNReal.ofReal (‖Complex.exp (-a y) * g y‖ ^ 2) := by
      rw [normSq_exp_mul, Complex.neg_re, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← mul_assoc, ← Real.exp_add]
      norm_num
    rw [hval]
    exact _root_.mul_le_mul_right (le_bergmanSup hinv y) _
  · -- multiply by `e^a`
    rw [bergmanSup, ENNReal.mul_iSup]
    refine iSup_le fun f => ?_
    rw [ENNReal.mul_iSup]
    refine iSup_le fun hf => ?_
    have hmem := exp_mul_mem_bergmanBall ha hf
    have hval : ENNReal.ofReal (Real.exp (2 * (a y).re)) * ENNReal.ofReal (‖f y‖ ^ 2) =
        ENNReal.ofReal (‖Complex.exp (a y) * f y‖ ^ 2) := by
      rw [normSq_exp_mul, ENNReal.ofReal_mul (Real.exp_pos _).le]
    rw [hval]
    exact le_bergmanSup hmem y

end

end Hironaka.BergmanHolomorphicMultiplier
