import Hironaka.Analytic.PshLogExponentBound

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The ball supremum of a plurisubharmonic function is convex in `log r`

Source: Demailly, *Complex analytic and differential geometry*, I.4 and III.5.

`ballSup u p t` is the supremum of `u` over the closed ball of radius `exp t` about `p`.  For
`u` plurisubharmonic this is a nondecreasing **convex** function of `t`, and the Lelong number
of `u` at `p` is its slope at `-∞`.  This file records the convexity in the chord form, as a
direct consequence of the pointwise three-circle inequality of `Hironaka.PshThreeCircles`.

Convexity is the half of the Lelong-number theory that the supremum sees.  It gives finiteness
(`Hironaka.PshLogExponentBound`) and, through the slope at `-∞`, the identification of the
Lelong number.  It does **not** give subadditivity: the supremum is not additive, and the
functional that is additive is the ball mean.

No module in the root import closure imports this file.
-/

open Metric Set
open scoped Topology

namespace Hironaka.PshBallSup

open Hironaka.PshThreeCircles Hironaka.PshLogExponentBound

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The supremum of `u` over the closed ball of radius `exp t` about `p`. -/
def ballSup (u : E → EReal) (p : E) (t : ℝ) : EReal :=
  ⨆ z ∈ closedBall p (Real.exp t), u z

theorem le_ballSup {u : E → EReal} {p : E} {t : ℝ} {z : E}
    (hz : z ∈ closedBall p (Real.exp t)) : u z ≤ ballSup u p t :=
  le_iSup₂ (f := fun z (_ : z ∈ closedBall p (Real.exp t)) => u z) z hz

theorem ballSup_le {u : E → EReal} {p : E} {t : ℝ} {c : EReal}
    (h : ∀ z ∈ closedBall p (Real.exp t), u z ≤ c) : ballSup u p t ≤ c :=
  iSup₂_le h

theorem ballSup_mono {u : E → EReal} {p : E} {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    ballSup u p t₁ ≤ ballSup u p t₂ :=
  ballSup_le fun _z hz =>
    le_ballSup (closedBall_subset_closedBall (Real.exp_le_exp.mpr h) hz)

/-- The ball supremum of a plurisubharmonic function never takes the value `⊤`. -/
theorem ballSup_ne_top {u : E → EReal} {p : E} {R t : ℝ} [ProperSpace E]
    (hu : PlurisubharmonicOn u (ball p R)) (ht : Real.exp t < R) :
    ballSup u p t ≠ ⊤ := by
  have hsub : closedBall p (Real.exp t) ⊆ ball p R := fun z hz =>
    mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hz) ht)
  obtain ⟨A, -, hA⟩ :=
    hu.exists_nonnegative_compact_upper_bound (isCompact_closedBall p (Real.exp t)) hsub
  exact ne_top_of_le_ne_top (EReal.coe_ne_top A) (ballSup_le hA)

/-- **Convexity of `t ↦ ballSup u p t`,** in chord form: the value at the middle radius is at
most the affine interpolation of the values at the two outer radii.  This is Hadamard's
three-circle theorem; the only input is the pointwise inequality
`PshThreeCircles.le_log_interpolation`. -/
theorem ballSup_le_chord [ProperSpace E] {u : E → EReal} {p : E} {R : ℝ}
    (hu : PlurisubharmonicOn u (ball p R)) {t₁ t₂ t₃ : ℝ}
    (h₁₂ : t₁ < t₂) (h₂₃ : t₂ < t₃) (ht₃ : Real.exp t₃ < R)
    (hbot : ballSup u p t₁ ≠ ⊥) :
    ballSup u p t₂ ≤
      (((ballSup u p t₁).toReal +
        (t₂ - t₁) * ((ballSup u p t₃).toReal - (ballSup u p t₁).toReal) / (t₃ - t₁) :
          ℝ) : EReal) := by
  have h₁₃ : t₁ < t₃ := h₁₂.trans h₂₃
  have hexp₁ : (0:ℝ) < Real.exp t₁ := Real.exp_pos t₁
  have hexp₁₃ : Real.exp t₁ < Real.exp t₃ := Real.exp_lt_exp.mpr h₁₃
  have hball : closedBall p (Real.exp t₃) ⊆ ball p R := fun z hz =>
    mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hz) ht₃)
  have htop₁ : ballSup u p t₁ ≠ ⊤ := ballSup_ne_top hu (hexp₁₃.trans ht₃)
  have htop₃ : ballSup u p t₃ ≠ ⊤ := ballSup_ne_top hu ht₃
  have hbot₃ : ballSup u p t₃ ≠ ⊥ := fun h => hbot (le_bot_iff.mp (h ▸ ballSup_mono h₁₃.le))
  set A₁ : ℝ := (ballSup u p t₁).toReal with hA₁
  set A₃ : ℝ := (ballSup u p t₃).toReal with hA₃
  have hcoe₁ : ballSup u p t₁ = (A₁ : EReal) := (EReal.coe_toReal htop₁ hbot).symm
  have hcoe₃ : ballSup u p t₃ = (A₃ : EReal) := (EReal.coe_toReal htop₃ hbot₃).symm
  have hA₁₃ : A₁ ≤ A₃ := by
    have := ballSup_mono (u := u) (p := p) h₁₃.le
    rw [hcoe₁, hcoe₃] at this
    exact_mod_cast this
  have h1 : ∀ z : E, ‖z - p‖ = Real.exp t₁ → u z ≤ (A₁ : EReal) := fun z hz => by
    rw [← hcoe₁]
    exact le_ballSup (mem_closedBall.mpr (by rw [dist_eq_norm, hz]))
  have h3 : ∀ z : E, ‖z - p‖ = Real.exp t₃ → u z ≤ (A₃ : EReal) := fun z hz => by
    rw [← hcoe₃]
    exact le_ballSup (mem_closedBall.mpr (by rw [dist_eq_norm, hz]))
  refine ballSup_le fun z hz => ?_
  have hznorm : ‖z - p‖ ≤ Real.exp t₂ := by rwa [mem_closedBall, dist_eq_norm] at hz
  rcases le_or_gt (Real.exp t₁) ‖z - p‖ with hin | hout
  · have hz₃ : ‖z - p‖ ≤ Real.exp t₃ := hznorm.trans (Real.exp_le_exp.mpr h₂₃.le)
    have hchord := le_log_interpolation hu hexp₁ hexp₁₃ hball h1 h3 hin hz₃
    refine hchord.trans (EReal.coe_le_coe_iff.mpr ?_)
    have hlogz : Real.log ‖z - p‖ ≤ t₂ := by
      have := Real.log_le_log (lt_of_lt_of_le hexp₁ hin) hznorm
      rwa [Real.log_exp] at this
    have hlog₁ : Real.log (Real.exp t₁) = t₁ := Real.log_exp t₁
    have hlog₃ : Real.log (Real.exp t₃) = t₃ := Real.log_exp t₃
    rw [hlog₁, hlog₃]
    have hden : (0:ℝ) < t₃ - t₁ := by linarith
    have hnum : (0:ℝ) ≤ A₃ - A₁ := by linarith
    have : (Real.log ‖z - p‖ - t₁) * (A₃ - A₁) ≤ (t₂ - t₁) * (A₃ - A₁) :=
      mul_le_mul_of_nonneg_right (by linarith) hnum
    have hdiv : (Real.log ‖z - p‖ - t₁) * (A₃ - A₁) / (t₃ - t₁) ≤
        (t₂ - t₁) * (A₃ - A₁) / (t₃ - t₁) := by
      exact div_le_div_of_nonneg_right this hden.le
    linarith [hdiv]
  · have : u z ≤ (A₁ : EReal) := by
      rw [← hcoe₁]
      exact le_ballSup (mem_closedBall.mpr (by rw [dist_eq_norm]; exact hout.le))
    refine this.trans (EReal.coe_le_coe_iff.mpr ?_)
    have hden : (0:ℝ) < t₃ - t₁ := by linarith
    have hnum : (0:ℝ) ≤ A₃ - A₁ := by linarith
    have : 0 ≤ (t₂ - t₁) * (A₃ - A₁) / (t₃ - t₁) := by positivity
    linarith

end

end Hironaka.PshBallSup
