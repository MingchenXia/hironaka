import Hironaka.Analytic.HarmonicDiscPsh
import Hironaka.Analytic.PotentialTheory.PlurisubharmonicPullback
import Hironaka.Analytic.PshPuncturedLineRemovable

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Hadamard's three-circle inequality for plurisubharmonic functions

Source: Demailly, *Complex analytic and differential geometry*, I.4 (Hadamard's three-circle
theorem) and III.5 (the Lelong number as the slope of the resulting convex function).

For `u` plurisubharmonic near `x` the supremum of `u` over the sphere of radius `r` about `x`
is a convex function of `log r`.  This file proves the inequality in the pointwise form that
its consumers need: a bound on the two bounding spheres of a closed annulus propagates into the
annulus along the logarithmic chord joining the two bounds.

The proof is the classical one.  Restrict `u` to the complex line through `x` in the direction
of the test point — a *complex affine* restriction, so `PlurisubharmonicPullback` applies and no
holomorphic-pullback theorem is needed.  Compare the restriction with `a log‖λ‖ + b`, which is
harmonic away from the origin, and apply the maximum principle on the closed annulus, which
`Hironaka.PshPuncturedLineRemovable` already proves sorry-free
(`PlurisubharmonicOn.le_const_on_closedAnnulus_of_isPreconnected`, with `closedAnnulus` and
`isPreconnected_closedAnnulus`).  The annulus, not the disc, is what the argument needs: the
comparison function `a log‖λ‖` is harmonic only away from the origin.

No module in the root import closure imports this file.
-/

open Metric Set InnerProductSpace
open scoped Topology

namespace Hironaka.PshThreeCircles

open Hironaka.PshPuncturedLineRemovable

noncomputable section

/-! ### A real multiple of `log ‖·‖` is harmonic off the origin -/

/-- Any real multiple of `log ‖·‖` is harmonic on a set avoiding the origin. -/
theorem harmonicOnNhd_const_mul_log_norm (a : ℝ) {S : Set ℂ} (hS : ∀ z ∈ S, z ≠ 0) :
    HarmonicOnNhd (fun z : ℂ => a * Real.log ‖z‖) S := by
  intro z hz
  have h : HarmonicAt (fun w : ℂ => Real.log ‖w‖) z :=
    AnalyticAt.harmonicAt_log_norm (f := fun w : ℂ => w) analyticAt_id (hS z hz)
  have hfun : (a • fun w : ℂ => Real.log ‖w‖) = fun w : ℂ => a * Real.log ‖w‖ := by
    funext w; simp [Pi.smul_apply, smul_eq_mul]
  exact hfun ▸ h.const_smul (c := a)

/-! ### The three-circle inequality -/

/-- Membership in the concentric closed annulus of `Hironaka.PshPuncturedLineRemovable`. -/
theorem mem_closedAnnulus_zero {r₁ r₃ : ℝ} {lam : ℂ} :
    lam ∈ closedAnnulus 0 r₁ r₃ ↔ r₁ ≤ ‖lam‖ ∧ ‖lam‖ ≤ r₃ := by
  simp [closedAnnulus, mem_closedBall, mem_ball, dist_zero_right, not_lt, and_comm]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Hadamard's three-circle inequality**, pointwise form.  If `u` is plurisubharmonic on a
neighbourhood of the closed ball of radius `r₃` about `x`, and `u ≤ A₁` on the sphere of radius
`r₁` and `u ≤ A₃` on the sphere of radius `r₃`, then on the closed annulus between them `u` is
bounded by the affine interpolation of `A₁` and `A₃` in `log‖z - x‖`. -/
theorem le_log_interpolation {u : E → EReal} {Ω : Set E} (hu : PlurisubharmonicOn u Ω)
    {x : E} {r₁ r₃ : ℝ} (hr₁ : 0 < r₁) (hr : r₁ < r₃) (hΩ : closedBall x r₃ ⊆ Ω)
    {A₁ A₃ : ℝ}
    (h1 : ∀ z, ‖z - x‖ = r₁ → u z ≤ (A₁ : EReal))
    (h3 : ∀ z, ‖z - x‖ = r₃ → u z ≤ (A₃ : EReal))
    {z : E} (hz1 : r₁ ≤ ‖z - x‖) (hz3 : ‖z - x‖ ≤ r₃) :
    u z ≤ ((A₁ + (Real.log ‖z - x‖ - Real.log r₁) * (A₃ - A₁) /
      (Real.log r₃ - Real.log r₁) : ℝ) : EReal) := by
  set w : E := z - x with hw
  have hwpos : 0 < ‖w‖ := lt_of_lt_of_le hr₁ hz1
  set v : E := ((‖w‖⁻¹ : ℝ) : ℂ) • w with hv
  have hvnorm : ‖v‖ = 1 := by
    rw [hv, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖w‖⁻¹)]
    field_simp
  set L : ℂ →L[ℂ] E := (ContinuousLinearMap.id ℂ ℂ).smulRight v with hL
  have hLapply : ∀ lam : ℂ, L lam = lam • v := fun lam => rfl
  have hLnorm : ∀ lam : ℂ, ‖L lam‖ = ‖lam‖ := by
    intro lam; rw [hLapply, norm_smul, hvnorm, mul_one]
  set K : Set ℂ := closedAnnulus 0 r₁ r₃ with hK
  have hKsub : K ⊆ (fun lam : ℂ => x + L lam) ⁻¹' Ω := by
    intro lam hlam
    refine hΩ ?_
    simp only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, hLnorm]
    exact (mem_closedAnnulus_zero.mp hlam).2
  have hg : PlurisubharmonicOn (fun lam : ℂ => u (x + L lam)) K := fun lam hlam =>
    PlurisubharmonicAt.comp_affine L x (hu (x + L lam) (hKsub hlam))
  set a : ℝ := (A₃ - A₁) / (Real.log r₃ - Real.log r₁) with ha
  set b : ℝ := A₁ - a * Real.log r₁ with hb
  have hlogpos : Real.log r₁ < Real.log r₃ := Real.log_lt_log hr₁ hr
  have hlogne : Real.log r₃ - Real.log r₁ ≠ 0 := sub_ne_zero.mpr (ne_of_gt hlogpos)
  have hak : a * (Real.log r₃ - Real.log r₁) = A₃ - A₁ := by
    rw [ha]; field_simp
  have hharm : HarmonicOnNhd (fun lam : ℂ => a * Real.log ‖lam‖) K := by
    refine harmonicOnNhd_const_mul_log_norm a ?_
    intro lam hlam hzero
    have h0 : r₁ ≤ ‖lam‖ := (mem_closedAnnulus_zero.mp hlam).1
    rw [hzero, norm_zero] at h0
    linarith
  have hpsh : PlurisubharmonicOn
      (fun lam : ℂ => u (x + L lam) - ((a * Real.log ‖lam‖ : ℝ) : EReal)) K :=
    hg.sub_harmonic hharm
  have hpoint : ∀ lam : ℂ, ‖(x + L lam) - x‖ = ‖lam‖ := by
    intro lam; rw [add_sub_cancel_left, hLnorm]
  have hinner : ∀ lam ∈ sphere (0 : ℂ) r₁,
      u (x + L lam) - ((a * Real.log ‖lam‖ : ℝ) : EReal) ≤ (b : EReal) := by
    intro lam hlam
    have hc : ‖lam‖ = r₁ := mem_sphere_zero_iff_norm.mp hlam
    have hle : u (x + L lam) ≤ (A₁ : EReal) := h1 _ (by rw [hpoint, hc])
    rw [hc]
    refine le_trans (EReal.sub_le_sub hle le_rfl) ?_
    rw [← EReal.coe_sub]
  have houter : ∀ lam ∈ sphere (0 : ℂ) r₃,
      u (x + L lam) - ((a * Real.log ‖lam‖ : ℝ) : EReal) ≤ (b : EReal) := by
    intro lam hlam
    have hc : ‖lam‖ = r₃ := mem_sphere_zero_iff_norm.mp hlam
    have hle : u (x + L lam) ≤ (A₃ : EReal) := h3 _ (by rw [hpoint, hc])
    rw [hc]
    refine le_trans (EReal.sub_le_sub hle le_rfl) ?_
    rw [← EReal.coe_sub]
    refine EReal.coe_le_coe_iff.mpr ?_
    have hexp : a * Real.log r₃ - a * Real.log r₁ = A₃ - A₁ := by rw [← hak]; ring
    rw [hb]; linarith
  have hmain := PlurisubharmonicOn.le_const_on_closedAnnulus_of_isPreconnected
    hpsh hr₁ hr subset_rfl (isPreconnected_closedAnnulus hr₁) houter hinner
  set lam₀ : ℂ := ((‖w‖ : ℝ) : ℂ) with hlam₀
  have hlam₀K : lam₀ ∈ K := by
    refine mem_closedAnnulus_zero.mpr ⟨?_, ?_⟩ <;>
      simp [hlam₀, Complex.norm_real, hz1, hz3]
  have hLlam₀ : x + L lam₀ = z := by
    rw [hLapply, hv, smul_smul, hlam₀]
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (ne_of_gt hwpos)]
    simp [hw]
  have hnorm₀ : ‖lam₀‖ = ‖w‖ := by
    simp [hlam₀, Complex.norm_real]
  have := hmain lam₀ hlam₀K
  rw [hLlam₀, hnorm₀] at this
  have hfinal : u z ≤ ((b + a * Real.log ‖w‖ : ℝ) : EReal) := by
    have h := (EReal.sub_le_iff_le_add (a := u z) (b := ((a * Real.log ‖w‖ : ℝ) : EReal))
      (c := (b : EReal)) (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))).mp this
    rwa [← EReal.coe_add] at h
  refine hfinal.trans (EReal.coe_le_coe_iff.mpr (le_of_eq ?_))
  rw [hb, ha]
  field_simp
  ring

end

end Hironaka.PshThreeCircles
