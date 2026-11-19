import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The slope at `-∞` of a nondecreasing convex function

Source: Demailly, *Complex analytic and differential geometry*, I.4 (the Lelong number as the
slope at `-∞` of the ball supremum).

This file isolates the *real-analytic* half of the identification of a Lelong number with the
slope of `t ↦ sup_{‖z - p‖ ≤ e^t} u` at `t = -∞`.  Nothing here mentions plurisubharmonicity:
the input is a function `L : ℝ → ℝ` which, below a threshold `T`, is nondecreasing and satisfies
the chord inequality

`L b ≤ L a + (b - a) * (L c - L a) / (c - a)`  for `a < b < c < T`,

and the output is a nonnegative slope `s` together with the two asymptotic bounds that the
Lelong-number argument consumes:

* an *upper* bound `L t ≤ s * t + C` valid for all `t` below a threshold — this is the bound
  that makes `s` an admissible Lelong exponent;
* an *approximate lower* bound `(s + ε) * t + C' ≤ L t`, for each `ε > 0` and all `t` below an
  `ε`-dependent threshold — this is what prevents `L` from decaying faster than the slope, and
  it is the half that a supremum alone cannot see.

Together they say `L t / t → s` as `t → -∞`, but the two one-sided forms are what the
consumers use, and stating them separately avoids any `limsup` boundedness side conditions.

No module in the root import closure imports this file.
-/

open Set

namespace Hironaka.ConvexSlopeAtBot

noncomputable section

variable {L : ℝ → ℝ} {T : ℝ}

/-- The chord slope of `L` from `t` up to the fixed right endpoint `t₀`. -/
def chordSlope (L : ℝ → ℝ) (t₀ t : ℝ) : ℝ := (L t₀ - L t) / (t₀ - t)

/-- **Chord slopes increase as the left endpoint moves right.**  This is the usual convexity
statement, derived from the chord inequality with the right endpoint held at `t₀`. -/
theorem chordSlope_mono
    (hchord : ∀ ⦃a b c : ℝ⦄, a < b → b < c → c < T →
      L b ≤ L a + (b - a) * (L c - L a) / (c - a))
    {t₀ t t' : ℝ} (ht₀ : t₀ < T) (htt' : t < t') (ht't₀ : t' < t₀) :
    chordSlope L t₀ t ≤ chordSlope L t₀ t' := by
  have hd : (0:ℝ) < t₀ - t := by linarith
  have hd' : (0:ℝ) < t₀ - t' := by linarith
  have h := hchord htt' ht't₀ ht₀
  have hcancel : (t' - t) * (L t₀ - L t) / (t₀ - t) * (t₀ - t) =
      (t' - t) * (L t₀ - L t) := div_mul_cancel₀ _ hd.ne'
  have hmul := mul_le_mul_of_nonneg_right h hd.le
  rw [add_mul, hcancel] at hmul
  rw [chordSlope, chordSlope, div_le_div_iff₀ hd hd']
  nlinarith [hmul]

/-- Chord slopes of a nondecreasing function are nonnegative. -/
theorem chordSlope_nonneg
    (hmono : ∀ ⦃a b : ℝ⦄, a ≤ b → b < T → L a ≤ L b)
    {t₀ t : ℝ} (ht₀ : t₀ < T) (htt₀ : t < t₀) :
    0 ≤ chordSlope L t₀ t :=
  div_nonneg (by linarith [hmono htt₀.le ht₀]) (by linarith)

/-- **The slope at `-∞` of a nondecreasing chord-convex function.**

The slope `s` is nonnegative, it bounds `L` from above affinely near `-∞` (so it is an
admissible exponent), and no exponent larger than `s` bounds `L` from above near `-∞`, in the
sharp form of an affine *lower* bound with slope `s + ε`. -/
theorem exists_slope_atBot
    (hmono : ∀ ⦃a b : ℝ⦄, a ≤ b → b < T → L a ≤ L b)
    (hchord : ∀ ⦃a b c : ℝ⦄, a < b → b < c → c < T →
      L b ≤ L a + (b - a) * (L c - L a) / (c - a)) :
    ∃ s : ℝ, 0 ≤ s ∧
      (∃ C t₂ : ℝ, t₂ ≤ T ∧ ∀ t < t₂, L t ≤ s * t + C) ∧
      (∀ ε : ℝ, 0 < ε → ∃ t₁ C' : ℝ, ∀ t < t₁, (s + ε) * t + C' ≤ L t) := by
  classical
  set t₀ : ℝ := T - 1 with ht₀def
  have ht₀ : t₀ < T := by simp [ht₀def]
  set S : Set ℝ := chordSlope L t₀ '' Iio t₀ with hSdef
  have hSne : S.Nonempty := ⟨chordSlope L t₀ (t₀ - 1), ⟨t₀ - 1, by simp, rfl⟩⟩
  have hSbdd : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact chordSlope_nonneg hmono ht₀ ht
  set s : ℝ := sInf S with hsdef
  have hs0 : 0 ≤ s := le_csInf hSne (by rintro _ ⟨t, ht, rfl⟩; exact chordSlope_nonneg hmono ht₀ ht)
  have hsle : ∀ t < t₀, s ≤ chordSlope L t₀ t := by
    intro t ht
    exact csInf_le hSbdd ⟨t, ht, rfl⟩
  refine ⟨s, hs0, ⟨L t₀ - s * t₀, t₀, by simp [ht₀def], ?_⟩, ?_⟩
  · intro t ht
    have h := hsle t ht
    have hd : (0:ℝ) < t₀ - t := by linarith
    rw [chordSlope, le_div_iff₀ hd] at h
    linarith
  · intro ε hε
    have hlt : s < s + ε := by linarith
    obtain ⟨y, hy, hylt⟩ := exists_lt_of_csInf_lt hSne (hsdef ▸ hlt)
    obtain ⟨t₁, ht₁, rfl⟩ := hy
    have ht₁' : t₁ < t₀ := mem_Iio.mp ht₁
    refine ⟨t₁, L t₀ - (s + ε) * t₀, ?_⟩
    intro t ht
    have hmono' : chordSlope L t₀ t ≤ chordSlope L t₀ t₁ :=
      chordSlope_mono hchord ht₀ ht ht₁'
    have hlt' : chordSlope L t₀ t < s + ε := lt_of_le_of_lt hmono' hylt
    have hd : (0:ℝ) < t₀ - t := by linarith
    rw [chordSlope, div_lt_iff₀ hd] at hlt'
    linarith

end

end Hironaka.ConvexSlopeAtBot
