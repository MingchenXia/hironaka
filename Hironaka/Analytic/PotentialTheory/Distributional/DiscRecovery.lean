import Hironaka.Analytic.PotentialTheory.BallSubmean

/-! # Ball submeans for finite disc-plurisubharmonic functions

The recovery argument in Lemma 1.2 of `pshd-vibe` uses ordinary real ball
means. These follow from the project's nonnegative deficit normalization.
-/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace Hironaka.PSHD

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]

/-- A finite disc-PSH function satisfies the ordinary real ball-submean
inequality on every relatively compact ball. -/
theorem real_ball_submean {u : E → ℝ} {U : Set E}
    (hu : DiscPshOn (fun x => (u x : EReal)) U)
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (a : E) {R : ℝ} (hR : 0 < R) (hB : closedBall a R ⊆ U) :
    (μ (ball a R)).toReal * u a ≤ ∫ x in ball a R, u x ∂μ := by
  have hmassfin : μ (ball a R) < ⊤ := measure_ball_lt_top
  let : IsFiniteMeasure (μ.restrict (ball a R)) := ⟨by simpa using hmassfin⟩
  obtain ⟨C, hC⟩ := hu.exists_compact_upper_bound (isCompact_closedBall a R)
    ⟨a, mem_closedBall_self hR.le⟩ hB
  have hCa : u a ≤ C := by
    exact_mod_cast hC a (mem_closedBall_self hR.le)
  have hCy (x : E) (hx : x ∈ ball a R) : u x ≤ C := by
    exact_mod_cast hC x (ball_subset_closedBall hx)
  have hU : ball a R ⊆ U := ball_subset_closedBall.trans hB
  have hint : IntegrableOn u (ball a R) μ := by
    simpa using (hu.ae_finite_and_integrableOn_ball μ a hR hB
      (EReal.coe_ne_bot (u a))).2.1
  let d : E → ℝ≥0∞ := fun x => ((C : EReal) - (u x : EReal)).toENNReal
  have hd : AEMeasurable d (μ.restrict (ball a R)) :=
    hu.aemeasurable_deficit_restrict measurableSet_ball hU C μ
  have hdfin : ∀ᵐ x ∂μ.restrict (ball a R), d x < ⊤ := by
    filter_upwards [] with x
    simp only [d, ← EReal.coe_sub, EReal.real_coe_toENNReal]
    exact ENNReal.ofReal_lt_top
  have hdeq : ∫ x in ball a R, (d x).toReal ∂μ =
      (μ (ball a R)).toReal * C - ∫ x in ball a R, u x ∂μ := by
    have heq : (fun x => (d x).toReal) =ᶠ[ae (μ.restrict (ball a R))]
        (fun x => C - u x) := by
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      simp [d, ← EReal.coe_sub,
        ENNReal.toReal_ofReal (sub_nonneg.mpr (hCy x hx))]
    rw [integral_congr_ae heq, integral_sub (integrable_const C) hint]
    simp [integral_const, Measure.real, smul_eq_mul]
  have hmass : μ (ball (0 : E) R) = μ (ball a R) := by
    simpa using lintegral_ball_add μ (fun _ => (1 : ℝ≥0∞)) a R
  have hineq := hu.ball_deficit_le μ a R C hU
    (fun x hx => hC x (ball_subset_closedBall hx))
  have hfin : μ (ball (0 : E) R) * d a ≠ ⊤ := by
    apply ENNReal.mul_ne_top measure_ball_lt_top.ne
    simp [d, ← EReal.coe_sub]
  have hreal := ENNReal.toReal_mono hfin hineq
  change (∫⁻ x in ball a R, d x ∂μ).toReal ≤ _ at hreal
  rw [← integral_toReal hd hdfin, hdeq] at hreal
  simp only [ENNReal.toReal_mul, hmass, d, ← EReal.coe_sub,
    EReal.real_coe_toENNReal, ENNReal.toReal_ofReal (sub_nonneg.mpr hCa)] at hreal
  nlinarith

/-- Normalized real ball means dominate the central value. -/
theorem le_real_ball_average {u : E → ℝ} {U : Set E}
    (hu : DiscPshOn (fun x => (u x : EReal)) U)
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (a : E) {R : ℝ} (hR : 0 < R) (hB : closedBall a R ⊆ U) :
    u a ≤ (∫ x in ball a R, u x ∂μ) / (μ (ball a R)).toReal := by
  have hm : 0 < (μ (ball a R)).toReal :=
    ENNReal.toReal_pos (ne_of_gt (measure_ball_pos μ a hR)) measure_ball_lt_top.ne
  exact (le_div_iff₀ hm).mpr (by
    simpa only [mul_comm] using real_ball_submean hu μ a hR hB)

/-- Upper semicontinuity and the submean inequality trap all sufficiently
small normalized ball means between the central value and any larger number. -/
theorem exists_real_ball_average_bounds {u : E → ℝ} {U : Set E}
    (hu : DiscPshOn (fun x => (u x : EReal)) U)
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (a : E) (hUa : U ∈ 𝓝 a) {b : ℝ} (hb : u a < b) :
    ∃ δ > 0, ∀ r ∈ Ioo (0 : ℝ) δ,
      u a ≤ (∫ x in ball a r, u x ∂μ) / (μ (ball a r)).toReal ∧
      (∫ x in ball a r, u x ∂μ) / (μ (ball a r)).toReal ≤ b := by
  have hupper : ∀ᶠ x in 𝓝 a, u x < b := by
    have h := hu.upperSemicontinuousOn a (mem_of_mem_nhds hUa)
      (b : EReal) (EReal.coe_lt_coe_iff.mpr hb)
    rw [nhdsWithin_eq_nhds.mpr hUa] at h
    filter_upwards [h] with x hx
    exact_mod_cast hx
  have hUevent : ∀ᶠ x in 𝓝 a, x ∈ U := hUa
  obtain ⟨δ, hδ, hlocal⟩ := Metric.eventually_nhds_iff.mp (hUevent.and hupper)
  refine ⟨δ, hδ, ?_⟩
  intro r hr
  have hB : closedBall a r ⊆ U := by
    intro x hx
    exact (hlocal ((mem_closedBall.mp hx).trans_lt hr.2)).1
  refine ⟨le_real_ball_average hu μ a hr.1 hB, ?_⟩
  have hmassfin : μ (ball a r) < ⊤ := measure_ball_lt_top
  let : IsFiniteMeasure (μ.restrict (ball a r)) := ⟨by simpa using hmassfin⟩
  have hint : IntegrableOn u (ball a r) μ := by
    simpa using (hu.ae_finite_and_integrableOn_ball μ a hr.1 hB
      (EReal.coe_ne_bot (u a))).2.1
  have hle : (∫ x in ball a r, u x ∂μ) ≤ ∫ _x in ball a r, b ∂μ := by
    apply integral_mono_ae hint (integrable_const b)
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact (hlocal ((mem_ball.mp hx).trans hr.2)).2.le
  have hm : 0 < (μ (ball a r)).toReal :=
    ENNReal.toReal_pos (ne_of_gt (measure_ball_pos μ a hr.1)) hmassfin.ne
  apply (div_le_iff₀ hm).mpr
  simpa [integral_const, Measure.real, smul_eq_mul, mul_comm] using hle

/-- Shrinking real ball means recover a finite disc-PSH function at every
interior point, with the Haar normalization already used by the project. -/
theorem tendsto_real_ball_average {u : E → ℝ} {U : Set E}
    (hu : DiscPshOn (fun x => (u x : EReal)) U)
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (a : E) (hUa : U ∈ 𝓝 a) :
    Tendsto (fun r : ℝ => (∫ x in ball a r, u x ∂μ) / (μ (ball a r)).toReal)
      (𝓝[>] 0) (𝓝 (u a)) := by
  have hsmall {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo 0 δ := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hδ)] with r hr hδr
    exact ⟨hr, hδr⟩
  apply tendsto_order.mpr
  constructor
  · intro b hb
    obtain ⟨δ, hδ, hbds⟩ := exists_real_ball_average_bounds hu μ a hUa
      (b := u a + 1) (by linarith)
    filter_upwards [hsmall hδ] with r hr
    exact hb.trans_le (hbds r hr).1
  · intro b hb
    obtain ⟨c, hc, hcb⟩ := exists_between hb
    obtain ⟨δ, hδ, hbds⟩ := exists_real_ball_average_bounds hu μ a hUa hc
    filter_upwards [hsmall hδ] with r hr
    exact (hbds r hr).2.trans_lt hcb

end Hironaka.PSHD
