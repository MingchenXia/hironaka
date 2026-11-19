import Hironaka.Analytic.PotentialTheory.BallSubmean
import Hironaka.Analytic.PotentialTheory.PshAddition

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Three estimates for the ball deficit of a plurisubharmonic function

Source: Demailly, *Complex analytic and differential geometry*, I.4 (the Harnack comparison
between the mean and the supremum) and III.5.

The Lelong number of a plurisubharmonic function is the slope at `-∞` of *either* the ball
supremum or the ball mean; the supremum is the functional that is convex, and the mean is the
functional that is **additive**.  Subadditivity of Lelong numbers is invisible to the supremum
(the supremum of a sum is not the sum of the suprema in any useful direction), so the argument
must pass through the mean.  This file records the three estimates that the passage needs,
all stated for the *unnormalised* nonnegative deficit

`∫⁻ z in ball p ρ, ((C : EReal) - u z).toENNReal ∂μ`,

which is the form in which `DiscPshOn.ball_deficit_le` already supplies the submean inequality:
no normalisation, no integrability premise, and poles allowed anywhere, including at `p`.

* `deficitInt_add` — exact additivity of the deficit integral in the potential.  This is where
  the `ℝ≥0∞`-valued formulation pays off: `lintegral` is additive with no integrability side
  condition, and `PshAddition.finiteDeficit_add` makes the integrands add pointwise.
* `deficitInt_le_of_near_center` — the **Harnack comparison**: the deficit integral over
  `ball p (K r)` is at most `μ (ball 0 ((K+1) r))` times the pointwise deficit at *any* point
  `z₀` with `‖z₀ - p‖ ≤ r`.  Applied at a point where `u` is nearly maximal on
  `closedBall p r`, this bounds the mean below by the supremum, up to the factor
  `(K/(K+1))^{dim}` which tends to `1`.
* `le_deficitInt_of_log_bound` — an admissible logarithmic bound `u ≤ γ log ‖· - p‖ + C` gives a
  lower bound for the deficit integral.  The centre `p` itself is excluded by the hypothesis and
  reinstated as a null set, which is why `Nontrivial E` appears.

No module in the root import closure imports this file.
-/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace Hironaka.PshBallDeficitComparison

open Hironaka

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [MeasurableSpace E] [BorelSpace E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]

/-- **The deficit integral is additive in the potential.**  Below separate finite upper bounds
the deficits add pointwise, and `lintegral` adds them with no integrability premise; poles of
either potential are retained (both sides are `⊤` there). -/
theorem deficitInt_add {u v : E → EReal} {U s : Set E} (hu : DiscPshOn u U)
    (hs : MeasurableSet s) (hsU : s ⊆ U) {Cu Cv : ℝ}
    (hCu : ∀ z ∈ s, u z ≤ (Cu : EReal)) (hCv : ∀ z ∈ s, v z ≤ (Cv : EReal))
    (μ : Measure E) :
    ∫⁻ z in s, (((Cu + Cv : ℝ) : EReal) - (u z + v z)).toENNReal ∂μ =
      (∫⁻ z in s, ((Cu : EReal) - u z).toENNReal ∂μ) +
        ∫⁻ z in s, ((Cv : EReal) - v z).toENNReal ∂μ := by
  have hsplit := lintegral_add_left' (μ := μ.restrict s)
    (f := fun z => ((Cu : EReal) - u z).toENNReal)
    (hu.aemeasurable_deficit_restrict hs hsU Cu μ)
    (fun z => ((Cv : EReal) - v z).toENNReal)
  rw [← hsplit]
  exact setLIntegral_congr_fun hs
    (fun z hz => finiteDeficit_add Cu Cv (hCu z hz) (hCv z hz))

/-- **The Harnack comparison.**  For every point `z₀` within distance `r` of `p`, the deficit
integral over `ball p (K r)` is controlled by `μ (ball 0 ((K+1) r))` times the *pointwise*
deficit at `z₀`.  The point `z₀` may be a pole, in which case the bound is vacuous; the content
is the case where `u z₀` is close to the supremum of `u` on `closedBall p r`. -/
theorem deficitInt_le_of_near_center {μ : Measure E} [μ.IsAddHaarMeasure] {u : E → EReal}
    {p : E} {R : ℝ} (hu : DiscPshOn u (ball p R)) {Cu : ℝ}
    (hCu : ∀ z ∈ ball p R, u z ≤ (Cu : EReal))
    {r K : ℝ} (hRr : (K + 2) * r ≤ R) {z₀ : E} (hz₀ : ‖z₀ - p‖ ≤ r) :
    ∫⁻ z in ball p (K * r), ((Cu : EReal) - u z).toENNReal ∂μ ≤
      μ (ball 0 ((K + 1) * r)) * ((Cu : EReal) - u z₀).toENNReal := by
  have hsum : (K + 1) * r + r = (K + 2) * r := by ring
  have hsub1 : ball z₀ ((K + 1) * r) ⊆ ball p R := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    rw [mem_ball, dist_eq_norm]
    calc ‖z - p‖ = ‖(z - z₀) + (z₀ - p)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖z - z₀‖ + ‖z₀ - p‖ := norm_add_le _ _
      _ < (K + 1) * r + r := by linarith
      _ ≤ R := by linarith
  have hsub2 : ball p (K * r) ⊆ ball z₀ ((K + 1) * r) := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    rw [mem_ball, dist_eq_norm]
    calc ‖z - z₀‖ = ‖(z - p) + (p - z₀)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖z - p‖ + ‖p - z₀‖ := norm_add_le _ _
      _ < K * r + r := by
          have : ‖p - z₀‖ = ‖z₀ - p‖ := norm_sub_rev p z₀
          linarith [this ▸ hz₀]
      _ = (K + 1) * r := by ring
  exact (lintegral_mono_set hsub2).trans
    (hu.ball_deficit_le μ z₀ ((K + 1) * r) Cu hsub1 fun y hy => hCu y (hsub1 hy))

/-- **An admissible logarithmic bound bounds the deficit integral from below.**  If
`w ≤ γ log ‖· - p‖ + C` on a punctured ball of radius `ρ` and `γ ≥ 0`, then on `ball p r` with
`r ≤ ρ` the potential is at most the constant `γ log r + C`, so the deficit below any constant
`Cw` is at least the corresponding constant deficit.  The excluded centre is a null set. -/
theorem le_deficitInt_of_log_bound [Nontrivial E] {μ : Measure E} [μ.IsAddHaarMeasure]
    {w : E → EReal} {p : E} {Cw γ C ρ : ℝ} (hγ : 0 ≤ γ)
    (hb : ∀ z : E, 0 < ‖z - p‖ → ‖z - p‖ < ρ →
      w z ≤ ((γ * Real.log ‖z - p‖ + C : ℝ) : EReal))
    {r : ℝ} (hrρ : r ≤ ρ) :
    ENNReal.ofReal (Cw - (γ * Real.log r + C)) * μ (ball p r) ≤
      ∫⁻ z in ball p r, ((Cw : EReal) - w z).toENNReal ∂μ := by
  have hne : ∀ᵐ z ∂μ, z ≠ p := by
    rw [ae_iff]
    simp [measure_singleton (μ := μ) p]
  have hpt : ∀ᵐ z ∂(μ.restrict (ball p r)),
      ENNReal.ofReal (Cw - (γ * Real.log r + C)) ≤ ((Cw : EReal) - w z).toENNReal := by
    filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae hne] with z hz hzne
    have h0 : 0 < ‖z - p‖ := by
      rw [norm_pos_iff, sub_ne_zero]
      exact hzne
    have hlt : ‖z - p‖ < r := by rwa [mem_ball, dist_eq_norm] at hz
    have hlog : Real.log ‖z - p‖ ≤ Real.log r := Real.log_le_log h0 hlt.le
    have hle : w z ≤ ((γ * Real.log r + C : ℝ) : EReal) :=
      (hb z h0 (hlt.trans_le hrρ)).trans
        (EReal.coe_le_coe_iff.mpr (by nlinarith))
    calc ENNReal.ofReal (Cw - (γ * Real.log r + C))
        = ((Cw : EReal) - ((γ * Real.log r + C : ℝ) : EReal)).toENNReal := by
          rw [← EReal.coe_sub, EReal.real_coe_toENNReal]
      _ ≤ ((Cw : EReal) - w z).toENNReal :=
          EReal.toENNReal_le_toENNReal (EReal.sub_le_sub le_rfl hle)
  calc ENNReal.ofReal (Cw - (γ * Real.log r + C)) * μ (ball p r)
      = ∫⁻ _z in ball p r, ENNReal.ofReal (Cw - (γ * Real.log r + C)) ∂μ :=
        (setLIntegral_const _ _).symm
    _ ≤ _ := lintegral_mono_ae hpt

end

end Hironaka.PshBallDeficitComparison
