import Hironaka.Analytic.PotentialTheory.MultiplierIdealsBasic
import Hironaka.Analytic.PotentialTheory.Plurisubharmonic
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.PotentialTheory.LocalPshDiscControl
import Hironaka.Analytic.BergmanGenerators
import Hironaka.Analytic.HolomorphicAnalytic
import Hironaka.Analytic.OhsawaTakegoshiPoint

set_option autoImplicit false

/-!
# Demailly's Bergman-kernel approximation with finitely many generators

Let `P` be plurisubharmonic near `z ∈ ℂⁿ` and `m ≥ 1`.  Near `z`, `e^{mP}` is dominated by
finitely many holomorphic functions that are `L²` for the weight `e^{-mP}` (Demailly,
*Analytic methods in algebraic geometry*, Theorem 13.2; Xia, Hironaka, Theorem 1.6.2,
`xia-sgpt:page-0049`).

On a ball `B` around `z`, let `X` be the unit ball of the Bergman space of holomorphic
functions with `∫_B |f|² e^{-mP} ≤ 1`.  Finitely many `g_l ∈ X` dominate every `f ∈ X`
near `z` with one constant (`BergmanGenerators.exists_uniform_generators`: Noetherian germ
ring, Montel, Baire).  The Ohsawa–Takegoshi extension from a point
(`OhsawaTakegoshiPoint.exists_extension_from_point`) gives, for each `y` with
`P(y) > -∞`, some `F ∈ X` scaled with `|F(y)|² ≥ e^{mP(y)} / C`.  Holomorphic functions of
several variables are analytic (`HolomorphicAnalytic.analyticOnNhd_of_differentiableOn`).
Weights follow the source convention `e^{-mP}` of `MultiplierIntegrableAt`.
-/

open Set MeasureTheory Metric Filter
open scoped ENNReal

namespace Hironaka.DemaillyApproximation



variable {n : ℕ}

/-- A weight `e^{-cP}` with `P` upper semicontinuous on an open set is a.e.-measurable
there. -/
theorem aemeasurable_multiplierWeight_restrict [MeasurableSpace (ComplexModel n)]
    [BorelSpace (ComplexModel n)] {P : ComplexModel n → EReal} {U : Set (ComplexModel n)}
    (hU : IsOpen U) (hP : UpperSemicontinuousOn P U) {c : ℝ} (hc : c ≠ 0) :
    AEMeasurable (fun x => multiplierWeight c (P x)) (volume.restrict U) := by
  classical
  have hφmeas : AEMeasurable P (volume.restrict U) := by
    let v : ComplexModel n → EReal := fun y => if y ∈ U then P y else ⊤
    have hv : UpperSemicontinuous v := by
      intro y a hya
      by_cases hy : y ∈ U
      · have hua : P y < a := by simpa [v, hy] using hya
        have hlocal := hP y hy a hua
        rw [hU.nhdsWithin_eq hy] at hlocal
        filter_upwards [hlocal, hU.mem_nhds hy] with z hz hzU
        simpa [v, hzU] using hz
      · simp [v, hy] at hya
    apply hv.measurable.aemeasurable.congr
    filter_upwards [ae_restrict_mem hU.measurableSet] with y hy
    simp [v, hy]
  have hcmul : AEMeasurable (fun y => (c : EReal) * P y) (volume.restrict U) :=
    (Hironaka.continuous_eReal_const_mul hc).measurable.comp_aemeasurable' hφmeas
  have hneg : AEMeasurable (fun y => -((c : EReal) * P y)) (volume.restrict U) :=
    continuous_neg.measurable.comp_aemeasurable' hcmul
  simpa only [multiplierWeight] using EReal.measurable_exp.comp_aemeasurable' hneg

/-- **Demailly approximation, finite form.** Near every point, `e^{mP}` is dominated by
finitely many holomorphic functions that are `L²` for the weight `e^{-mP}`. -/
theorem exists_weightedL2_generators :
    by
      letI : MeasurableSpace (ComplexModel n) := borel _
      letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
      exact ∀ (W : Set (ComplexModel n)) (P : ComplexModel n → EReal), IsOpen W →
        PlurisubharmonicOn P W → ∀ z ∈ W, ∀ m : ℕ, 0 < m →
          ∃ O : Set (ComplexModel n), IsOpen O ∧ z ∈ O ∧ O ⊆ W ∧
            ∃ (N : ℕ) (g : Fin N → ComplexModel n → ℂ) (C : ℝ≥0∞), C ≠ ⊤ ∧
              (∀ l, AnalyticOnNhd ℂ (g l) O) ∧
              (∀ l, WeightedL2On P m (g l) O volume) ∧
              ∀ y ∈ O, EReal.exp ((m : EReal) * P y) ≤
                C * ∑ l, ENNReal.ofReal (‖g l y‖ ^ 2) := by
  let _ : MeasurableSpace (ComplexModel n) := borel _
  have _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
  intro W P hW hP z hz m hm
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hW z hz
  set R : ℝ := ε / 4 with hRdef
  have hR : 0 < R := by positivity
  have hBW : closedBall z (2 * R) ⊆ W :=
    (closedBall_subset_ball (by rw [hRdef]; linarith)).trans hεW
  have hbW : ball z (2 * R) ⊆ W := ball_subset_closedBall.trans hBW
  obtain ⟨A, -, hA⟩ := hP.exists_nonnegative_compact_upper_bound (isCompact_closedBall z (2 * R))
    hBW
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set w : ComplexModel n → ℝ≥0∞ := fun x => multiplierWeight (m : ℝ) (P x) with hwdef
  have hw : AEMeasurable w (volume.restrict (ball z (2 * R))) :=
    aemeasurable_multiplierWeight_restrict isOpen_ball (hP.upperSemicontinuousOn.mono hbW)
      hm0.ne'
  have hlow : ∀ y ∈ ball z (2 * R), ENNReal.ofReal (Real.exp (-((m : ℝ) * A))) ≤ w y := by
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
    have := min_le_right r R; linarith)
  refine ⟨O, isOpen_ball, mem_ball_self (lt_min hr hR), hOB.trans hbW, N, g,
    ENNReal.ofReal (C * K'), ENNReal.ofReal_ne_top, fun l =>
      (HolomorphicAnalytic.analyticOnNhd_of_differentiableOn isOpen_ball (hgX l).1).mono hOB,
    fun l => ⟨?_, ?_⟩, fun y hy => ?_⟩
  · exact ((ENNReal.continuous_ofReal.comp_continuousOn
      (((hgX l).1.mono hOB).continuousOn.norm.pow 2)).aemeasurable
        isOpen_ball.measurableSet).mul (hw.mono_measure (Measure.restrict_mono hOB le_rfl))
  · exact (lintegral_mono_set hOB).trans_lt ((hgX l).2.trans_lt ENNReal.one_lt_top)
  -- the domination at `y`
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
    obtain ⟨F, hF, hFy, hFint⟩ := hOT (ball z (2 * R)) isOpen_ball (convex_ball z (2 * R)) hΩ P
      (hP.mono hbW) (m : ℝ) hm0 y hyB
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
        rw [← Real.exp_add]; simp
      rw [hs] at h1
      nlinarith [Real.exp_pos ((m : ℝ) * a)]
    rw [← hcast, ← EReal.coe_mul, EReal.exp_coe,
      ← ENNReal.ofReal_sum_of_nonneg (fun l _ => sq_nonneg _), ← ENNReal.ofReal_mul
      (mul_nonneg hC.le (le_max_right _ _))]
    exact ENNReal.ofReal_le_ofReal hreal

end Hironaka.DemaillyApproximation
