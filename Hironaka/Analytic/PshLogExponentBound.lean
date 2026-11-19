import Hironaka.Analytic.PshThreeCircles

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The admissible logarithmic exponents of a plurisubharmonic germ are bounded

Source: Demailly, *Complex analytic and differential geometry*, III.5 (finiteness of the
Lelong number of a plurisubharmonic function which is not identically `-∞`).

Call `γ` *admissible* for `u` at `p` when `u ≤ γ log‖· - p‖ + C` on some punctured
neighbourhood of `p`.  The Lelong number of `u` at `p` is the supremum of the admissible
exponents (`Hironaka.lelongNumber`), so it is finite exactly when the
admissible exponents are bounded above.

They are, and the bound is explicit: if `u` is plurisubharmonic on `ball p R` and `u y₀ ≠ ⊥`
for one point `y₀ ≠ p` of that ball, then every admissible `γ` satisfies

  `γ ≤ (A - u y₀) / (log R' - log ‖y₀ - p‖)`,

where `R'` is any radius with `‖y₀ - p‖ < R' < R` and `A` bounds `u` on `closedBall p R'`.
Both hypotheses are essential: without a finite value the function may be identically `⊥`,
for which every exponent is admissible, and in dimension `0` there is no such `y₀` at all.

The proof is Hadamard's three-circle inequality (`Hironaka.PshThreeCircles`) applied to the
triple of radii `exp t < ‖y₀ - p‖ < R'`: the admissible bound controls `u` on the inner
sphere, the compactness bound controls it on the outer sphere, and the finite value at `y₀`
forbids the interpolated bound from running off to `-∞` as `t → -∞`.  The only consequence of
the interpolation used is the single inequality obtained at `z = y₀`.

No module in the root import closure imports this file.
-/

open Metric Set
open scoped Topology

namespace Hironaka.PshLogExponentBound

open Hironaka.PshThreeCircles

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [ProperSpace E]

/-- **The admissible logarithmic exponents of a plurisubharmonic germ are bounded.**
The bound `s` is produced once and for all; it does not depend on the size of the punctured
neighbourhood on which an individual exponent happens to be admissible, which is exactly what
makes it a bound for the supremum. -/
theorem exists_bound_forall_log_exponent {u : E → EReal} {p : E} {R : ℝ}
    (hu : PlurisubharmonicOn u (ball p R))
    {y₀ : E} (hy₀ : ‖y₀ - p‖ < R) (hy₀p : y₀ ≠ p) (hbot : u y₀ ≠ ⊥) :
    ∃ s : ℝ, ∀ γ C ρ : ℝ, 0 < ρ →
      (∀ z : E, 0 < ‖z - p‖ → ‖z - p‖ < ρ →
        u z ≤ ((γ * Real.log ‖z - p‖ + C : ℝ) : EReal)) → γ ≤ s := by
  have hd : 0 < ‖y₀ - p‖ := by
    rw [norm_pos_iff, sub_ne_zero]; exact hy₀p
  set R' : ℝ := (‖y₀ - p‖ + R) / 2 with hR'
  have hdR' : ‖y₀ - p‖ < R' := by rw [hR']; linarith
  have hR'R : R' < R := by rw [hR']; linarith
  have hR'pos : 0 < R' := hd.trans hdR'
  have hball : closedBall p R' ⊆ ball p R := fun z hz =>
    mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hz) hR'R)
  obtain ⟨A, -, hA⟩ :=
    hu.exists_nonnegative_compact_upper_bound (isCompact_closedBall p R') hball
  have hy₀ball : y₀ ∈ ball p R := mem_ball.mpr (by rwa [dist_eq_norm])
  have hy₀top : u y₀ ≠ ⊤ := (hu y₀ hy₀ball).ne_top
  set B : ℝ := (u y₀).toReal with hB
  have hy₀coe : u y₀ = (B : EReal) := (EReal.coe_toReal hy₀top hbot).symm
  set t₂ : ℝ := Real.log ‖y₀ - p‖ with ht₂
  set t₀ : ℝ := Real.log R' with ht₀
  have ht₂t₀ : t₂ < t₀ := Real.log_lt_log hd hdR'
  have hBA : B ≤ A := by
    have := hA y₀ (mem_closedBall.mpr (by rw [dist_eq_norm]; exact hdR'.le))
    rw [hy₀coe] at this
    exact_mod_cast this
  refine ⟨(A - B) / (t₀ - t₂), ?_⟩
  intro γ C ρ hρ hadm
  by_contra hgs
  rw [not_le] at hgs
  set P : ℝ := A - B - γ * (t₀ - t₂) with hP
  have hPneg : P < 0 := by
    have hpos : 0 < t₀ - t₂ := by linarith
    rw [hP]
    have := (div_lt_iff₀ hpos).mp hgs
    linarith
  set Q : ℝ := B * t₀ - C * (t₀ - t₂) - t₂ * A with hQ
  set t : ℝ := min (min (Real.log ρ) t₂) (-Q / P) - 1 with ht
  have htρ : t < Real.log ρ := by
    have : t ≤ Real.log ρ - 1 := by
      rw [ht]; have := min_le_left (min (Real.log ρ) t₂) (-Q / P)
      have h2 := min_le_left (Real.log ρ) t₂
      linarith [this.trans h2]
    linarith
  have htt₂ : t < t₂ := by
    have : t ≤ t₂ - 1 := by
      rw [ht]
      have h1 := min_le_left (min (Real.log ρ) t₂) (-Q / P)
      have h2 := min_le_right (Real.log ρ) t₂
      linarith [h1.trans h2]
    linarith
  have htQ : t < -Q / P := by
    have : t ≤ -Q / P - 1 := by
      rw [ht]; linarith [min_le_right (min (Real.log ρ) t₂) (-Q / P)]
    linarith
  -- the inner radius
  set r : ℝ := Real.exp t with hr
  have hrpos : 0 < r := Real.exp_pos t
  have hrρ : r < ρ := by
    rw [hr, ← Real.exp_log hρ]; exact Real.exp_lt_exp.mpr htρ
  have hrd : r < ‖y₀ - p‖ := by
    rw [hr, ← Real.exp_log hd]; exact Real.exp_lt_exp.mpr htt₂
  have hrR' : r < R' := hrd.trans hdR'
  have hlogr : Real.log r = t := Real.log_exp t
  -- the three-circle inequality on `r < ‖y₀ - p‖ < R'`
  have h1 : ∀ z : E, ‖z - p‖ = r → u z ≤ ((γ * t + C : ℝ) : EReal) := by
    intro z hz
    have := hadm z (by rw [hz]; exact hrpos) (by rw [hz]; exact hrρ)
    rwa [hz, hlogr] at this
  have h3 : ∀ z : E, ‖z - p‖ = R' → u z ≤ (A : EReal) := fun z hz =>
    hA z (mem_closedBall.mpr (by rw [dist_eq_norm, hz]))
  have hchord := le_log_interpolation hu hrpos hrR' hball h1 h3
    (z := y₀) hrd.le hdR'.le
  rw [hy₀coe, hlogr, ← ht₂, ← ht₀] at hchord
  have hreal : B ≤ γ * t + C + (t₂ - t) * (A - (γ * t + C)) / (t₀ - t) :=
    EReal.coe_le_coe_iff.mp hchord
  -- and the contradiction
  have ht₀t : 0 < t₀ - t := by linarith
  have h' : B - (γ * t + C) ≤ (t₂ - t) * (A - (γ * t + C)) / (t₀ - t) := by linarith
  have hstep : (B - (γ * t + C)) * (t₀ - t) ≤ (t₂ - t) * (A - (γ * t + C)) :=
    (le_div_iff₀ ht₀t).mp h'
  have hclear : B * (t₀ - t) ≤ (γ * t + C) * (t₀ - t₂) + (t₂ - t) * A := by nlinarith [hstep]
  have hfinal : t * P ≤ -Q := by rw [hP, hQ]; nlinarith [hclear]
  have : -Q / P ≤ t := by
    rw [div_le_iff_of_neg hPneg]
    linarith [hfinal]
  linarith

end

end Hironaka.PshLogExponentBound
