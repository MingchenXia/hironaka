import Hironaka.Analytic.PshBallSup
import Hironaka.Analytic.ConvexSlopeAtBot
import Hironaka.Analytic.PotentialTheory.PshRegularDistribution

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The Lelong slope of the ball supremum

Source: Demailly, *Complex analytic and differential geometry*, I.4 and III.5.

`Hironaka.PshBallSup` proves that `L u p t = sup_{‖z - p‖ ≤ e^t} u` is nondecreasing and convex
in `t`.  `Hironaka.ConvexSlopeAtBot` turns those two properties into a slope `s ≥ 0` at `t = -∞`
with a two-sided asymptotic description.  This file combines them.

The output is the pair of bounds that the Lelong-number argument consumes:

* `u z ≤ s · log ‖z - p‖ + C` on a punctured ball — so `s` is an admissible Lelong exponent
  and `s ≤ ν(u, p)`;
* for every `ε > 0`, `(s + ε) · t + C' ≤ L u p t` for `t` near `-∞` — the supremum does not
  decay faster than slope `s`.  This is the bound that transfers, through the Harnack
  comparison with the ball mean, into an upper bound for the mean's slope.

Finiteness of `L u p t` for **every** admissible radius (not just one) is what makes the slope
well defined; it comes from `PlurisubharmonicOn.ae_finite` on the big ball, which places a
non-pole point in every ball of positive radius.

No module in the root import closure imports this file.
-/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace Hironaka.PshBallSupSlope

open Hironaka.PshBallSup Hironaka.ConvexSlopeAtBot

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [MeasurableSpace E] [BorelSpace E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]

/-- **Every ball around `p` meets the finiteness locus.**  A plurisubharmonic function which is
not identically `⊥` on `ball p R` is finite almost everywhere there, so its supremum over any
ball of positive radius inside is not `⊥` — even when `p` itself is a pole. -/
theorem ballSup_ne_bot {μ : Measure E} [μ.IsAddHaarMeasure] {u : E → EReal} {p : E} {R t : ℝ}
    (hu : PlurisubharmonicOn u (ball p R)) (hne : ∃ a ∈ ball p R, u a ≠ ⊥)
    (ht : Real.exp t < R) :
    ballSup u p t ≠ ⊥ := by
  have hae := hu.ae_finite μ (convex_ball p R).isPreconnected hne
  have hsub : ball p (Real.exp t) ⊆ ball p R := ball_subset_ball ht.le
  intro hbot
  have hall : ball p (Real.exp t) ⊆ {z : E | ¬ (u z ≠ ⊤ ∧ u z ≠ ⊥)} := by
    intro z hz
    have hzc : z ∈ closedBall p (Real.exp t) := ball_subset_closedBall hz
    have : u z ≤ ⊥ := hbot ▸ le_ballSup hzc
    simp [le_bot_iff.mp this]
  have h0 : μ.restrict (ball p R) (ball p (Real.exp t)) = 0 :=
    measure_mono_null hall (ae_iff.mp hae)
  rw [Measure.restrict_apply' measurableSet_ball,
    inter_eq_self_of_subset_left hsub] at h0
  exact (measure_ball_pos μ p (Real.exp_pos t)).ne' h0

/-- The real-valued ball supremum, on the range of radii where it is finite. -/
theorem ballSup_eq_coe_toReal {μ : Measure E} [μ.IsAddHaarMeasure] {u : E → EReal} {p : E}
    {R t : ℝ} (hu : PlurisubharmonicOn u (ball p R)) (hne : ∃ a ∈ ball p R, u a ≠ ⊥)
    (ht : Real.exp t < R) :
    ballSup u p t = (((ballSup u p t).toReal : ℝ) : EReal) :=
  (EReal.coe_toReal (ballSup_ne_top hu ht) (ballSup_ne_bot (μ := μ) hu hne ht)).symm

/-- **The Lelong slope of the ball supremum.**  For `u` plurisubharmonic on `ball p R` and not
identically `⊥` there, the supremum `L u p t` over the ball of radius `e^t` has a nonnegative
slope `s` at `t = -∞`, described by an affine upper bound on a punctured ball and, for each
`ε > 0`, an affine lower bound of slope `s + ε` near `-∞`. -/
theorem exists_ballSup_slope {μ : Measure E} [μ.IsAddHaarMeasure] {u : E → EReal} {p : E}
    {R : ℝ} (hR : 0 < R) (hu : PlurisubharmonicOn u (ball p R))
    (hne : ∃ a ∈ ball p R, u a ≠ ⊥) :
    ∃ s : ℝ, 0 ≤ s ∧
      (∃ C ρ : ℝ, 0 < ρ ∧ ∀ z : E, 0 < ‖z - p‖ → ‖z - p‖ < ρ →
        u z ≤ ((s * Real.log ‖z - p‖ + C : ℝ) : EReal)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ t₁ C' : ℝ, ∀ t < t₁,
        ((s + ε) * t + C' : ℝ) ≤ (ballSup u p t).toReal) := by
  set T : ℝ := Real.log R with hT
  have hexp : ∀ t : ℝ, t < T → Real.exp t < R := fun t ht => by
    rwa [hT, Real.lt_log_iff_exp_lt hR] at ht
  set L : ℝ → ℝ := fun t => (ballSup u p t).toReal with hL
  have hcoe : ∀ t : ℝ, t < T → ballSup u p t = ((L t : ℝ) : EReal) := fun t ht =>
    ballSup_eq_coe_toReal (μ := μ) hu hne (hexp t ht)
  have hmono : ∀ ⦃a b : ℝ⦄, a ≤ b → b < T → L a ≤ L b := by
    intro a b hab hb
    have ha : a < T := lt_of_le_of_lt hab hb
    have h := ballSup_mono (u := u) (p := p) hab
    rw [hcoe a ha, hcoe b hb] at h
    exact_mod_cast h
  have hchord : ∀ ⦃a b c : ℝ⦄, a < b → b < c → c < T →
      L b ≤ L a + (b - a) * (L c - L a) / (c - a) := by
    intro a b c hab hbc hc
    have ha : a < T := hab.trans (hbc.trans hc)
    have hb : b < T := hbc.trans hc
    have h := ballSup_le_chord hu hab hbc (hexp c hc)
      (ballSup_ne_bot (μ := μ) hu hne (hexp a ha))
    rw [hcoe b hb] at h
    exact_mod_cast h
  obtain ⟨s, hs0, ⟨C, t₂, ht₂T, hupper⟩, hlower⟩ := exists_slope_atBot hmono hchord
  refine ⟨s, hs0, ⟨C, Real.exp t₂, Real.exp_pos t₂, ?_⟩, hlower⟩
  intro z hz0 hzρ
  have hlog : Real.log ‖z - p‖ < t₂ := by
    have := Real.log_lt_log hz0 hzρ
    rwa [Real.log_exp] at this
  have hzmem : z ∈ closedBall p (Real.exp (Real.log ‖z - p‖)) := by
    rw [mem_closedBall, dist_eq_norm, Real.exp_log hz0]
  refine (le_ballSup hzmem).trans ?_
  have hlt : Real.log ‖z - p‖ < T := lt_of_lt_of_le hlog ht₂T
  rw [hcoe _ hlt]
  exact_mod_cast hupper _ hlog

end

end Hironaka.PshBallSupSlope
