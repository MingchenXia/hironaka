import Hironaka.Analytic.HiepLocalUniformBound

set_option autoImplicit false

/-!
# The dimension induction of Hiep's proof: base case and glue

Hiep proves his Main theorem by induction on the dimension ("Of course, it holds for
`n = 0`", `hiep14-weighted-lct:proof-main`).  In the case `ψ_j ≤ φ` needed here, part (ii)
closes its own induction: Lemma 2.1 in dimension `n + 1` uses only (ii) in dimension `n`.
With the measure-theoretic half already proved
(`hiepStrongEffectiveOpenness_of_localUniformBound`), the induction step is therefore

  `HiepStrongEffectiveOpenness n → HiepLocalUniformBound (n + 1)`,

which is the analytic content (Lemma 2.1, standard bases, Galligo's estimate) and is **not**
proved here.  This module proves the base case `HiepLocalUniformBound 0` and the glue
`hiepStrongEffectiveOpenness_of_step`: the step in every dimension gives strong effective
openness, hence `IncreasingStrongOpenness`, in every dimension.

In dimension `0` the model space is a point of positive finite Lebesgue measure, so every
integral is a value times that measure: finite weighted mass means `f = 0` or `φ > ⊥`, and
then `ψ_j → φ` makes `ψ_j` eventually bounded below.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace Hironaka

noncomputable section

open Hironaka

/-- **Base case of Hiep's induction.** -/
theorem hiepLocalUniformBound_zero : HiepLocalUniformBound 0 := by
  let _ : MeasurableSpace (ComplexModel 0) := borel _
  have _ : BorelSpace (ComplexModel 0) := ⟨rfl⟩
  intro z R φ f c hR hφ _ hc hint ψ _ hle hL1
  have hball : ball z R = univ := eq_univ_of_forall fun x =>
    by rw [Subsingleton.elim x z]; exact mem_ball_self hR
  set m : ℝ≥0∞ := (volume : Measure (ComplexModel 0)) univ with hm
  have hm0 : m ≠ 0 := (isOpen_univ.measure_pos volume univ_nonempty).ne'
  have hmtop : m ≠ ⊤ := by
    exact measure_ne_top _ _
  have hconst : ∀ F : ComplexModel 0 → ℝ≥0∞, ∫⁻ x in ball z R, F x = F z * m := by
    intro F
    rw [hball, Measure.restrict_univ,
      lintegral_congr (g := fun _ => F z) (fun x => by rw [Subsingleton.elim x z]),
      lintegral_const]
  have hzmem : z ∈ ball z R := mem_ball_self hR
  by_cases hfz : f z = 0
  · refine ⟨R, hR, le_rfl, c + 1, by linarith, 0, ENNReal.zero_ne_top, ?_⟩
    refine Eventually.of_forall fun j => ?_
    rw [hconst, multiplierDensity_eq_zero_of_eq_zero _ _ hfz, zero_mul]
  · rw [hconst] at hint
    have hdens : multiplierDensity φ c f z ≠ ⊤ := fun h => by
      rw [h, ENNReal.top_mul hm0] at hint; exact lt_irrefl _ hint
    have hφbot : φ z ≠ ⊥ := fun h => hdens (multiplierDensity_eq_top_at_pole hc h hfz)
    have hφtop : φ z ≠ ⊤ := hφ.discPshOn.ne_top z hzmem
    have hdef : Tendsto (fun j => (φ z - ψ j z).toENNReal) atTop (𝓝 0) := by
      have h := ENNReal.Tendsto.mul_const (b := m⁻¹)
        (hL1.congr fun j => hconst (fun x => (φ x - ψ j x).toENNReal))
        (Or.inr (ENNReal.inv_ne_top.mpr hm0))
      simpa [mul_assoc, ENNReal.mul_inv_cancel hm0 hmtop] using h
    have hlim := tendsto_of_toENNReal_sub_tendsto_zero hφtop (fun j => hle j z hzmem) hdef
    set a : ℝ := (φ z).toReal - 1 with ha
    have hlt : ((a : ℝ) : EReal) < φ z := by
      rw [← EReal.coe_toReal hφtop hφbot, EReal.coe_lt_coe_iff, ha]; linarith
    refine ⟨R, hR, le_rfl, c + 1, by linarith,
      ENNReal.ofReal (‖f z‖ ^ 2) * multiplierWeight (c + 1) (a : EReal) * m,
      ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (by rw [multiplierWeight_coe]; exact ENNReal.ofReal_ne_top)) hmtop, ?_⟩
    filter_upwards [hlim.eventually (Ioi_mem_nhds hlt)] with j hj
    rw [hconst]
    gcongr
    unfold multiplierDensity
    gcongr
    exact multiplierWeight_antitone (by linarith : (0 : ℝ) ≤ c + 1) (le_of_lt hj)

/-- **The glue of Hiep's induction.**  If the analytic induction step holds in every
dimension, strong effective openness holds in every dimension. -/
theorem hiepStrongEffectiveOpenness_of_step
    (hstep : ∀ n, HiepStrongEffectiveOpenness n → HiepLocalUniformBound (n + 1)) :
    ∀ n, HiepStrongEffectiveOpenness n := by
  intro n
  induction n with
  | zero => exact hiepStrongEffectiveOpenness_of_localUniformBound 0 hiepLocalUniformBound_zero
  | succ n ih => exact hiepStrongEffectiveOpenness_of_localUniformBound (n + 1) (hstep n ih)

/-- Strong openness for increasing sequences, in every dimension, from the analytic
induction step of Hiep's proof. -/
theorem increasingStrongOpenness_of_hiepStep
    (hstep : ∀ n, HiepStrongEffectiveOpenness n → HiepLocalUniformBound (n + 1)) (n : ℕ) :
    IncreasingStrongOpenness n :=
  increasingStrongOpenness_of_hiep n (hiepStrongEffectiveOpenness_of_step hstep n)

end

end Hironaka
