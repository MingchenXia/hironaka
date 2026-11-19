import Hironaka.Analytic.RegularizedMaxEReal

set_option autoImplicit false

/-!
# Convexity of the regularized maximum, and its extended-real order calculus

Source: Demailly, *Complex analytic and differential geometry*, I.5.18 (the
regularized maximum `M_δ`).

`SmoothMax.posPart` is the primitive of the smooth transition `SmoothMax.trans`,
so it is
**convex**: its derivative is monotone.  The whole plurisubharmonicity of
Demailly's regularized maximum rests on two consequences of that, and this file
proves exactly those two, at the real level and then at the extended-real level.

* `posPart_tangent`: the tangent-line minorant `P(s) + P'(s)(s' - s) ≤ P(s')`.
  Transported to `realRegularizedMax` this says that

      M_δ(a', b') ≥ λ·a' + (1 - λ)·b' + c,   λ = trans((a-b)/δ) ∈ [0, 1],

  with equality at `(a', b') = (a, b)` (`tangent_eq_realRegularizedMax`).  Thus
  `M_δ(u, v)` is, at each point, touched from below by a *convex combination*
  of `u` and `v` shifted by a constant — and convex combinations of PSH
  functions are PSH.  This is what replaces the Jensen inequality.

* `eregularizedMax_mono` and `eregularizedMax_add_coe`: monotonicity in each
  variable and equivariance under a common real translation.  Together they
  give upper semicontinuity of `M_δ(u, v)` with no loss: a translation by `ε`
  raises the value by exactly `ε`, so the `δ`-gap between `M_δ` and `max` never
  enters the semicontinuity estimate.

The two degenerate slopes are recorded separately: `λ = 0` forces `s ≤ -1` and
`λ = 1` forces `1 ≤ s`, and in both cases the additive constant `c` vanishes and
the tangent minorant degenerates to `v`, respectively `u`, themselves.  This is
what keeps the minorant meaningful when one of the two potentials has a pole.
-/

open Real

namespace Hironaka.RegularizedMaxConvexity

open Hironaka.ScaledSmoothMax
open Hironaka.RegularizedMaxEReal

noncomputable section

/-! ### The real transition and its primitive -/

/-- `SmoothMax.trans` vanishes exactly on `(-∞, -1]`. -/
theorem trans_eq_zero_iff (t : ℝ) : SmoothMax.trans t = 0 ↔ t ≤ -1 := by
  show smoothTransition ((t + 1) / 2) = 0 ↔ t ≤ -1
  rw [smoothTransition.zero_iff_nonpos]
  constructor <;> intro h <;> linarith

/-- `SmoothMax.trans` equals `1` exactly on `[1, ∞)`. -/
theorem trans_eq_one_iff (t : ℝ) : SmoothMax.trans t = 1 ↔ 1 ≤ t := by
  show smoothTransition ((t + 1) / 2) = 1 ↔ 1 ≤ t
  rw [smoothTransition.eq_one_iff_one_le]
  constructor <;> intro h <;> linarith

private theorem intervalIntegrable_trans (a b : ℝ) :
    IntervalIntegrable SmoothMax.trans MeasureTheory.volume a b :=
  SmoothMax.continuous_trans.intervalIntegrable a b

/-- **The tangent-line minorant of the smooth positive part.**  `SmoothMax.posPart` is a
primitive of the monotone function `SmoothMax.trans`, hence convex, and this is the
convexity inequality in the form the regularized maximum needs. -/
theorem posPart_tangent (s s' : ℝ) :
    SmoothMax.posPart s + SmoothMax.trans s * (s' - s) ≤ SmoothMax.posPart s' := by
  have hsplit : SmoothMax.posPart s' - SmoothMax.posPart s = ∫ t in s..s', SmoothMax.trans t := by
    unfold SmoothMax.posPart
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_trans (-1) s) (intervalIntegrable_trans s s')]
    ring
  rcases le_total s s' with h | h
  · have hmono : (∫ _t in s..s', SmoothMax.trans s) ≤ ∫ t in s..s', SmoothMax.trans t := by
      refine intervalIntegral.integral_mono_on h intervalIntegrable_const
        (intervalIntegrable_trans s s') ?_
      intro x hx
      exact SmoothMax.trans_monotone hx.1
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    linarith
  · have hmono : (∫ t in s'..s, SmoothMax.trans t) ≤ ∫ _t in s'..s, SmoothMax.trans s := by
      refine intervalIntegral.integral_mono_on h (intervalIntegrable_trans s' s)
        intervalIntegrable_const ?_
      intro x hx
      exact SmoothMax.trans_monotone hx.2
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    rw [intervalIntegral.integral_symm] at hsplit
    linarith

/-! ### The tangent minorant of the real regularized maximum -/

/-- The slope of the tangent minorant of `realRegularizedMax δ · ·` at `(a, b)`. -/
def tangentSlope (δ a b : ℝ) : ℝ := SmoothMax.trans ((a - b) / δ)

/-- The additive constant of the tangent minorant at `(a, b)`. -/
def tangentConst (δ a b : ℝ) : ℝ :=
  δ * (SmoothMax.posPart ((a - b) / δ) - ((a - b) / δ) * SmoothMax.trans ((a - b) / δ))

theorem tangentSlope_nonneg (δ a b : ℝ) : 0 ≤ tangentSlope δ a b :=
  SmoothMax.trans_nonneg _

theorem tangentSlope_le_one (δ a b : ℝ) : tangentSlope δ a b ≤ 1 :=
  SmoothMax.trans_le_one _

/-- **The tangent minorant.**  A convex combination of the two branches, with
weight `tangentSlope`, shifted by `tangentConst`, never exceeds the regularized
maximum. -/
theorem tangent_le_realRegularizedMax {δ : ℝ} (hδ : 0 < δ) (a b a' b' : ℝ) :
    tangentSlope δ a b * a' + (1 - tangentSlope δ a b) * b' + tangentConst δ a b
      ≤ realRegularizedMax δ a' b' := by
  rw [realRegularizedMax_apply, tangentSlope, tangentConst]
  set s : ℝ := (a - b) / δ with hsdef
  set s' : ℝ := (a' - b') / δ with hs'def
  have hmul := mul_le_mul_of_nonneg_left (posPart_tangent s s') hδ.le
  have hab' : a' - b' = δ * s' := by rw [hs'def]; field_simp
  have hrw : SmoothMax.trans s * a' + (1 - SmoothMax.trans s) * b'
        + δ * (SmoothMax.posPart s - s * SmoothMax.trans s)
      = b' + SmoothMax.trans s * (a' - b')
        + δ * (SmoothMax.posPart s - s * SmoothMax.trans s) := by ring
  rw [hrw, hab']
  have hrw2 : b' + SmoothMax.trans s * (δ * s')
        + δ * (SmoothMax.posPart s - s * SmoothMax.trans s)
      = b' + δ * (SmoothMax.posPart s + SmoothMax.trans s * (s' - s)) := by ring
  rw [hrw2]
  linarith [hmul]

/-- The tangent minorant is *exact* at its base point. -/
theorem tangent_eq_realRegularizedMax {δ : ℝ} (hδ : 0 < δ) (a b : ℝ) :
    tangentSlope δ a b * a + (1 - tangentSlope δ a b) * b + tangentConst δ a b
      = realRegularizedMax δ a b := by
  rw [realRegularizedMax_apply, tangentSlope, tangentConst]
  set s : ℝ := (a - b) / δ with hsdef
  have hab : a - b = δ * s := by rw [hsdef]; field_simp
  have hrw : SmoothMax.trans s * a + (1 - SmoothMax.trans s) * b
        + δ * (SmoothMax.posPart s - s * SmoothMax.trans s)
      = b + SmoothMax.trans s * (a - b)
        + δ * (SmoothMax.posPart s - s * SmoothMax.trans s) := by ring
  rw [hrw, hab]
  ring

/-- A vanishing slope forces a vanishing constant: the minorant is then the
right branch itself, which still makes sense when the left branch is a pole. -/
theorem tangentConst_eq_zero_of_slope_eq_zero {δ a b : ℝ}
    (h : tangentSlope δ a b = 0) : tangentConst δ a b = 0 := by
  have hs : (a - b) / δ ≤ -1 := (trans_eq_zero_iff _).mp h
  rw [tangentConst, SmoothMax.posPart_eq_zero hs]
  rw [tangentSlope] at h
  rw [h]
  ring

/-- A unit slope forces a vanishing constant: the minorant is then the left
branch itself, which still makes sense when the right branch is a pole. -/
theorem tangentConst_eq_zero_of_slope_eq_one {δ a b : ℝ}
    (h : tangentSlope δ a b = 1) : tangentConst δ a b = 0 := by
  have hs : 1 ≤ (a - b) / δ := (trans_eq_one_iff _).mp h
  rw [tangentConst, SmoothMax.posPart_eq_self hs]
  rw [tangentSlope] at h
  rw [h]
  ring

/-! ### Order calculus of the extended-real regularized maximum -/

/-- **Monotonicity in both branches**, including the pole values. -/
theorem eregularizedMax_mono {δ : ℝ} (hδ : 0 < δ) {a a' b b' : EReal}
    (ha : a ≤ a') (hb : b ≤ b') (ha' : a' ≠ ⊤) (hb' : b' ≠ ⊤) :
    eregularizedMax δ a b ≤ eregularizedMax δ a' b' := by
  have hmax : max a' b' ≤ eregularizedMax δ a' b' :=
    max_le_eregularizedMax hδ ha' hb'
  by_cases hab : a = ⊥
  · rw [hab, eregularizedMax_bot_left]
    exact hb.trans ((le_max_right a' b').trans hmax)
  by_cases hbb : b = ⊥
  · rw [hbb, eregularizedMax_bot_right]
    exact ha.trans ((le_max_left a' b').trans hmax)
  -- both `a` and `b` are finite
  have hatop : a ≠ ⊤ := fun h => ha' (top_le_iff.mp (h ▸ ha))
  have hbtop : b ≠ ⊤ := fun h => hb' (top_le_iff.mp (h ▸ hb))
  have ha'b : a' ≠ ⊥ := fun h => hab (le_bot_iff.mp (h ▸ ha))
  have hb'b : b' ≠ ⊥ := fun h => hbb (le_bot_iff.mp (h ▸ hb))
  rw [eregularizedMax_eq_coe_realRegularizedMax hatop hab hbtop hbb,
    eregularizedMax_eq_coe_realRegularizedMax ha' ha'b hb' hb'b]
  rw [EReal.coe_le_coe_iff]
  have haR : a.toReal ≤ a'.toReal := by
    rw [← EReal.coe_le_coe_iff, EReal.coe_toReal hatop hab, EReal.coe_toReal ha' ha'b]
    exact ha
  have hbR : b.toReal ≤ b'.toReal := by
    rw [← EReal.coe_le_coe_iff, EReal.coe_toReal hbtop hbb, EReal.coe_toReal hb' hb'b]
    exact hb
  exact scaledSmoothMax_mono (E := Unit) hδ (z := ()) haR hbR

/-- **Equivariance under a common real translation.**  This is what makes the
upper-semicontinuity estimate lossless. -/
theorem eregularizedMax_add_coe (δ : ℝ) (a b : EReal) (c : ℝ) :
    eregularizedMax δ (a + (c : EReal)) (b + (c : EReal))
      = eregularizedMax δ a b + (c : EReal) := by
  by_cases hab : a = ⊥
  · subst a
    simp
  by_cases hbb : b = ⊥
  · subst b
    simp
  by_cases hatop : a = ⊤
  · subst a
    simp
  by_cases hbtop : b = ⊤
  · subst b
    simp
  have hac : a + (c : EReal) ≠ ⊥ := by simp [EReal.add_eq_bot_iff, hab]
  have hbc : b + (c : EReal) ≠ ⊥ := by simp [EReal.add_eq_bot_iff, hbb]
  have hact : a + (c : EReal) ≠ ⊤ := EReal.add_ne_top hatop (EReal.coe_ne_top c)
  have hbct : b + (c : EReal) ≠ ⊤ := EReal.add_ne_top hbtop (EReal.coe_ne_top c)
  rw [eregularizedMax_eq_coe_realRegularizedMax hact hac hbct hbc,
    eregularizedMax_eq_coe_realRegularizedMax hatop hab hbtop hbb]
  have hAR : (a + (c : EReal)).toReal = a.toReal + c := by
    conv_lhs => rw [← EReal.coe_toReal hatop hab]
    rw [← EReal.coe_add, EReal.toReal_coe]
  have hBR : (b + (c : EReal)).toReal = b.toReal + c := by
    conv_lhs => rw [← EReal.coe_toReal hbtop hbb]
    rw [← EReal.coe_add, EReal.toReal_coe]
  rw [hAR, hBR, ← EReal.coe_add, EReal.coe_eq_coe_iff,
    realRegularizedMax_apply, realRegularizedMax_apply]
  ring_nf

end

end Hironaka.RegularizedMaxConvexity
