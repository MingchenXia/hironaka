import Hironaka.Analytic.DemaillyApproximation

set_option autoImplicit false

/-!
# Uniform local Demailly--Bergman data

`DemaillyApproximation.exists_weightedL2_generators` deliberately retains only
the point-extension consequence of the uniform Bergman estimate.  This module
keeps the stronger witness itself: one finite family lies in a weighted
Bergman unit ball and dominates every member of that ball on a smaller domain.
The retained fields are local coordinate data; they assert neither coherence
nor global gluing.
-/

open Set MeasureTheory Metric Filter
open scoped ENNReal

namespace Hironaka.DemaillyApproximation



noncomputable section

variable {n : ℕ}

/-- The local finite Bergman output with the Baire-category uniform domination
witness preserved. -/
structure UniformWeightedL2Generators
    (W : Set (ComplexModel n)) (P : ComplexModel n → EReal)
    (z : ComplexModel n) (m : ℕ) where
  radius : ℝ
  radius_pos : 0 < radius
  /-- The weighted Bergman unit ball is defined using the concentric ball of
  radius `2 * radius`; keeping this containment makes every local multiplier
  ideal witness available on that same integration domain. -/
  double_radius_subset : ball z (2 * radius) ⊆ W
  domain : Set (ComplexModel n)
  domain_open : IsOpen domain
  center_mem_domain : z ∈ domain
  domain_subset : domain ⊆ W
  N : ℕ
  generator : Fin N → ComplexModel n → ℂ
  C : ℝ≥0∞
  C_ne_top : C ≠ ⊤
  generator_analytic : ∀ l, AnalyticOnNhd ℂ (generator l) domain
  generator_weighted : by
    letI : MeasurableSpace (ComplexModel n) := borel _
    letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
    exact ∀ l, WeightedL2On P m (generator l) domain volume
  pointwise_domination : ∀ y ∈ domain,
    EReal.exp ((m : EReal) * P y) ≤ C * ∑ l, ENNReal.ofReal (‖generator l y‖ ^ 2)
  uniform_radius : ℝ
  uniform_radius_pos : 0 < uniform_radius
  generator_unitBall : by
    letI : MeasurableSpace (ComplexModel n) := borel _
    letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
    exact ∀ l, generator l ∈ BergmanGenerators.bergmanUnitBall z radius
      (fun x => multiplierWeight (m : ℝ) (P x))
  domain_subset_uniformBall : domain ⊆ ball z uniform_radius
  uniform_constant : ℝ
  uniform_domination : by
    letI : MeasurableSpace (ComplexModel n) := borel _
    letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
    exact ∀ f ∈ BergmanGenerators.bergmanUnitBall z radius
      (fun x => multiplierWeight (m : ℝ) (P x)), ∀ y ∈ domain,
        ‖f y‖ ^ 2 ≤ uniform_constant * ∑ l, ‖generator l y‖ ^ 2

/-- The Demailly construction can retain the universal weighted-unit-ball
estimate that it obtains from `BergmanGenerators.exists_uniform_generators`.
The ordinary finite weighted `L²` and pointwise exponential estimates are kept
at the same time. -/
theorem exists_uniform_weightedL2_generators :
    by
      letI : MeasurableSpace (ComplexModel n) := borel _
      letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
      exact ∀ (W : Set (ComplexModel n)) (P : ComplexModel n → EReal), IsOpen W →
        PlurisubharmonicOn P W → ∀ z ∈ W, ∀ m : ℕ, 0 < m →
          Nonempty (UniformWeightedL2Generators W P z m) := by
  let _ : MeasurableSpace (ComplexModel n) := borel _
  have _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
  intro W P hW hP z hz m hm
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hW z hz
  set R : ℝ := ε / 4 with hRdef
  have hR : 0 < R := by positivity
  have hBW : closedBall z (2 * R) ⊆ W :=
    (closedBall_subset_ball (by rw [hRdef]; linarith)).trans hεW
  have hbW : ball z (2 * R) ⊆ W := ball_subset_closedBall.trans hBW
  obtain ⟨A, -, hA⟩ := hP.exists_nonnegative_compact_upper_bound
    (isCompact_closedBall z (2 * R)) hBW
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set w : ComplexModel n → ℝ≥0∞ := fun x => multiplierWeight (m : ℝ) (P x) with hwdef
  have hw : AEMeasurable w (volume.restrict (ball z (2 * R))) :=
    aemeasurable_multiplierWeight_restrict isOpen_ball (hP.upperSemicontinuousOn.mono hbW)
      hm0.ne'
  have hlow : ∀ y ∈ ball z (2 * R),
      ENNReal.ofReal (Real.exp (-((m : ℝ) * A))) ≤ w y := by
    intro y hy
    rw [← multiplierWeight_coe]
    exact multiplierWeight_antitone hm0.le (hA y (ball_subset_closedBall hy))
  obtain ⟨N, g, r, K, hr, hgX, hdom⟩ :=
    BergmanGenerators.exists_uniform_generators hR hw (Real.exp_pos _) hlow
  obtain ⟨C, hC, hOT⟩ := OhsawaTakegoshiPoint.exists_extension_from_point n
    (‖z‖ + 2 * R + 1) (by positivity)
  set K' : ℝ := max K 0 with hK'
  set O : Set (ComplexModel n) := ball z (min r R) with hOdef
  have hOB : O ⊆ ball z (2 * R) := ball_subset_ball (by
    have := min_le_right r R
    linarith)
  refine ⟨{
    radius := R
    radius_pos := hR
    double_radius_subset := hbW
    domain := O
    domain_open := isOpen_ball
    center_mem_domain := mem_ball_self (lt_min hr hR)
    domain_subset := hOB.trans hbW
    N := N
    generator := g
    C := ENNReal.ofReal (C * K')
    C_ne_top := ENNReal.ofReal_ne_top
    generator_analytic := fun l =>
      (HolomorphicAnalytic.analyticOnNhd_of_differentiableOn isOpen_ball (hgX l).1).mono hOB
    generator_weighted := fun l => ⟨?_, ?_⟩
    pointwise_domination := fun y hy => ?_
    uniform_radius := r
    uniform_radius_pos := hr
    generator_unitBall := hgX
    domain_subset_uniformBall := fun y hy =>
      ball_subset_ball (min_le_left r R) hy
    uniform_constant := K
    uniform_domination := fun f hf y hy =>
      hdom f hf y (ball_subset_ball (min_le_left r R) hy)
  }⟩
  · exact ((ENNReal.continuous_ofReal.comp_continuousOn
      (((hgX l).1.mono hOB).continuousOn.norm.pow 2)).aemeasurable
        isOpen_ball.measurableSet).mul (hw.mono_measure (Measure.restrict_mono hOB le_rfl))
  · exact (lintegral_mono_set hOB).trans_lt ((hgX l).2.trans_lt ENNReal.one_lt_top)
  have hyB : y ∈ ball z (2 * R) := hOB hy
  have hyr : y ∈ ball z r := ball_subset_ball (min_le_left r R) hy
  have hsum0 : 0 ≤ ∑ l, ‖g l y‖ ^ 2 := Finset.sum_nonneg fun l _ => sq_nonneg _
  have hcast : ((m : ℝ) : EReal) = (m : EReal) := by simp
  induction hPy : P y using EReal.rec with
  | bot =>
    rw [EReal.mul_bot_of_pos (by exact_mod_cast hm), EReal.exp_bot]
    exact bot_le
  | top =>
    exact absurd hPy ((hP y (hbW hyB)).ne_top)
  | coe a =>
    have hΩ : ∀ x ∈ ball z (2 * R), ‖x‖ < ‖z‖ + 2 * R + 1 := fun x hx => by
      have := norm_le_norm_add_norm_sub' x z
      rw [mem_ball, dist_eq_norm] at hx
      linarith
    obtain ⟨F, hF, hFy, hFint⟩ := hOT (ball z (2 * R)) isOpen_ball
      (convex_ball z (2 * R)) hΩ P (hP.mono hbW) (m : ℝ) hm0 y hyB
    rw [hPy, multiplierWeight_coe] at hFint
    set s : ℝ := C * Real.exp (-((m : ℝ) * a)) with hs
    have hspos : 0 < s := by positivity
    set f : ComplexModel n → ℂ := fun x => ((Real.sqrt s)⁻¹ : ℂ) * F x with hf
    have hfX : f ∈ BergmanGenerators.bergmanUnitBall z R w := by
      refine ⟨hF.const_mul _, ?_⟩
      have hpt : ∀ x, ENNReal.ofReal (‖f x‖ ^ 2) * w x =
          ENNReal.ofReal s⁻¹ * multiplierDensity P (m : ℝ) F x := by
        intro x
        simp only [hf, multiplierDensity, hwdef]
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), norm_mul, mul_pow,
          norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), inv_pow,
          Real.sq_sqrt hspos.le]
      simp_rw [hpt]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      calc ENNReal.ofReal s⁻¹ * ∫⁻ x in ball z (2 * R), multiplierDensity P (m : ℝ) F x
          ≤ ENNReal.ofReal s⁻¹ * (ENNReal.ofReal C *
              ENNReal.ofReal (Real.exp (-((m : ℝ) * a)))) := by gcongr
        _ = 1 := by
          rw [← ENNReal.ofReal_mul hC.le, ← hs, ← ENNReal.ofReal_mul (by positivity),
            inv_mul_cancel₀ hspos.ne', ENNReal.ofReal_one]
    have hfy : ‖f y‖ ^ 2 = s⁻¹ := by
      simp only [hf, hFy, mul_one, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt hspos.le]
    have hmain : s⁻¹ ≤ K' * ∑ l, ‖g l y‖ ^ 2 := by
      rw [← hfy]
      exact (hdom f hfX y hyr).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hsum0)
    have hreal : Real.exp ((m : ℝ) * a) ≤ C * K' * ∑ l, ‖g l y‖ ^ 2 := by
      have h1 : 1 ≤ s * (K' * ∑ l, ‖g l y‖ ^ 2) := by
        rw [inv_le_iff_one_le_mul₀ hspos] at hmain
        linarith
      have h2 : Real.exp ((m : ℝ) * a) * Real.exp (-((m : ℝ) * a)) = 1 := by
        rw [← Real.exp_add]
        simp
      rw [hs] at h1
      nlinarith [Real.exp_pos ((m : ℝ) * a)]
    rw [← hcast, ← EReal.coe_mul, EReal.exp_coe,
      ← ENNReal.ofReal_sum_of_nonneg (fun l _ => sq_nonneg _), ← ENNReal.ofReal_mul
      (mul_nonneg hC.le (le_max_right _ _))]
    exact ENNReal.ofReal_le_ofReal hreal

end

end Hironaka.DemaillyApproximation
