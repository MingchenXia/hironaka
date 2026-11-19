import Hironaka.Analytic.ComplexMonomialProductIntegral
import Mathlib.Analysis.Calculus.FDeriv.Pi

set_option autoImplicit false

/-! # Actual normal-coordinate logarithmic multiplier germs -/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace Hironaka.SNCCoordinateMonomialMultiplier

noncomputable section

private theorem density_eq_prod_of_coordinates_ne_zero {n : ℕ}
    (a : Fin n → ℕ) (b : Fin n → ℝ) (c : ℝ) (z : Fin n → ℂ)
    (hz : ∀ i, z i ≠ 0) :
    multiplierDensity (fun w : Fin n → ℂ => ∑ i, ((2 * b i : ℝ) : EReal) *
      ENNReal.log (ENNReal.ofReal ‖w i‖)) c (fun w => ∏ i, w i ^ a i) z =
      ∏ i, multiplierDensity (fun w : ℂ => ((2 * b i : ℝ) : EReal) *
        ENNReal.log (ENNReal.ofReal ‖w‖)) c (fun w => w ^ a i) (z i) := by
  classical
  have hlog (i : Fin n) : ENNReal.log (ENNReal.ofReal ‖z i‖) =
      ((Real.log ‖z i‖ : ℝ) : EReal) :=
    ENNReal.log_ofReal_of_pos (norm_pos_iff.mpr (hz i))
  have hP : (∑ i, ((2 * b i : ℝ) : EReal) *
      ENNReal.log (ENNReal.ofReal ‖z i‖)) =
      ((∑ i, 2 * b i * Real.log ‖z i‖ : ℝ) : EReal) := by
    simp_rw [hlog, ← EReal.coe_mul]
    exact (map_sum (⟨⟨fun r : ℝ => (r : EReal), EReal.coe_zero⟩,
      EReal.coe_add⟩ : ℝ →+ EReal) _ _).symm
  have hexp : Real.exp (-(c * ∑ i, 2 * b i * Real.log ‖z i‖)) =
      ∏ i, Real.exp (-(c * (2 * b i * Real.log ‖z i‖))) := by
    rw [← Real.exp_sum]
    congr 1
    simp only [Finset.mul_sum, Finset.sum_neg_distrib]
  rw [multiplierDensity, hP, multiplierWeight_coe, Complex.norm_prod,
    ← Finset.prod_pow, hexp]
  simp_rw [multiplierDensity, hlog, ← EReal.coe_mul, multiplierWeight_coe]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => sq_nonneg ‖z i ^ a i‖),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le),
    Finset.prod_mul_distrib]

/-- The literal total logarithmic density has the exact coordinate thresholds. -/
theorem weightedL2On_sum_log_monomial_iff {n : ℕ}
    (a : Fin n → ℕ) (b : Fin n → ℝ) (c : ℝ) (R : Fin n → ℝ)
    (hR : ∀ i, 0 < R i) :
    WeightedL2On (fun z : Fin n → ℂ => ∑ i, ((2 * b i : ℝ) : EReal) *
      ENNReal.log (ENNReal.ofReal ‖z i‖)) c (fun z => ∏ i, z i ^ a i)
      (Set.univ.pi fun i => ball 0 (R i)) volume ↔
        ∀ i, c * b i < (a i : ℝ) + 1 := by
  classical
  have hm : Measurable (multiplierDensity
      (fun z : Fin n → ℂ => ∑ i, ((2 * b i : ℝ) : EReal) *
        ENNReal.log (ENNReal.ofReal ‖z i‖)) c (fun z => ∏ i, z i ^ a i)) := by
    unfold multiplierDensity multiplierWeight
    fun_prop
  have hne : ∀ᵐ z : Fin n → ℂ ∂volume, ∀ i, z i ≠ 0 :=
    ae_all_iff.mpr fun i => Measure.ae_eval_ne (fun _ : Fin n => (volume : Measure ℂ)) i 0
  have hdensity : multiplierDensity
      (fun z : Fin n → ℂ => ∑ i, ((2 * b i : ℝ) : EReal) *
        ENNReal.log (ENNReal.ofReal ‖z i‖)) c (fun z => ∏ i, z i ^ a i) =ᵐ[volume]
      (fun z => ∏ i, multiplierDensity (fun w : ℂ => ((2 * b i : ℝ) : EReal) *
        ENNReal.log (ENNReal.ofReal ‖w‖)) c (fun w => w ^ a i) (z i)) := by
    filter_upwards [hne] with z hz
    exact density_eq_prod_of_coordinates_ne_zero a b c z hz
  have hint := lintegral_congr_ae (ae_restrict_of_ae hdensity
    (s := Set.univ.pi fun i => ball (0 : ℂ) (R i)))
  rw [volume_pi, Measure.restrict_pi_pi] at hint
  have hcriterion := ComplexMonomialProductIntegral.lintegral_log_monomial_prod_lt_top_iff
    a b (fun _ => c) R hR
  constructor
  · intro hL2
    apply hcriterion.mp
    rw [← hint]
    simpa only [volume_pi, Measure.restrict_pi_pi] using hL2.2
  · intro hthreshold
    refine ⟨hm.aemeasurable.restrict, ?_⟩
    rw [volume_pi, Measure.restrict_pi_pi, hint]
    exact hcriterion.mpr hthreshold

/-- The actual holomorphic integration germ has every strict coordinate threshold. -/
theorem multiplierIntegrableAt_sum_log_monomial_iff {n : ℕ}
    (a : Fin n → ℕ) (b : Fin n → ℝ) {c : ℝ} (hc : 0 < c) :
    MultiplierIntegrableAt (fun z : Fin n → ℂ => ∑ i, ((2 * b i : ℝ) : EReal) *
      ENNReal.log (ENNReal.ofReal ‖z i‖)) c (fun z => ∏ i, z i ^ a i) 0 volume ↔
        ∀ i, c * b i < (a i : ℝ) + 1 := by
  classical
  constructor
  · intro hint
    obtain ⟨U, hU, hzU, -, hL2⟩ := hint.2
    obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hU 0 hzU
    have hbox := hL2.mono hball
    rw [ball_pi _ hR] at hbox
    exact (weightedL2On_sum_log_monomial_iff a b c (fun _ => R)
      (fun _ => hR)).mp hbox
  · intro hthreshold
    refine ⟨hc, ball 0 1, isOpen_ball, by simp, ?_, ?_⟩
    · have hprod (s : Finset (Fin n)) : DifferentiableOn ℂ
          (fun z : Fin n → ℂ => ∏ i ∈ s, z i ^ a i) (ball 0 1) := by
        induction s using Finset.induction_on with
        | empty =>
          simp only [Finset.prod_empty]
          intro z _
          exact (differentiableAt_const (c := (1 : ℂ))).differentiableWithinAt
        | @insert i s hi ih =>
          simp only [Finset.prod_insert hi]
          apply DifferentiableOn.fun_mul
          · fun_prop
          · exact ih
      exact hprod Finset.univ
    · rw [ball_pi _ (by norm_num : (0 : ℝ) < 1)]
      exact (weightedL2On_sum_log_monomial_iff a b c (fun _ => 1)
        (fun _ => by norm_num)).mpr hthreshold

end
end Hironaka.SNCCoordinateMonomialMultiplier
