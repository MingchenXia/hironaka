import Hironaka.Analytic.RegularizedMaxConvexity
import Hironaka.Analytic.PshConvexCone

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Demailly's regularized maximum of plurisubharmonic functions is plurisubharmonic

Source: Demailly, *Complex analytic and differential geometry*, I.5.18.

`RegularizedMaxEReal.eregularizedMax δ` is the extended-real regularized maximum
`M_δ(a, b) = b + δ P((a - b)/δ)`, with `P = SmoothMax.posPart`.  This file proves
the analytic theorem that the workspace was missing:

> if `p` and `q` are plurisubharmonic on `U`, so is `M_δ(p, q)`.

Both regularity fields of the disc criterion are proved, poles included.

* **Upper semicontinuity** uses only that `M_δ` is monotone in each branch and
  *equivariant* under a common real translation (`RegularizedMaxConvexity`).
  The naive route through `max(p, q) ≤ M_δ(p, q) ≤ max(p, q) + δ` loses exactly
  `δ` and proves nothing; the translation identity loses nothing.

* **The submean inequality** avoids a two-variable Jensen inequality entirely.
  At each centre `x` the convexity of `P` supplies an *exact affine minorant* of
  `M_δ` at `(p x, q x)`: a convex combination `λ p + (1-λ) q + c` which lies
  below `M_δ(p, q)` everywhere and agrees with it at `x`
  (`tangentMinorant_le`, `tangentMinorant_self`).  Convex combinations are
  already known to be plurisubharmonic, and a function dominating a submean
  minorant that is exact at the centre inherits the submean inequality
  (`hasDiscSubmeanOn_of_tangentMinorants`).

The degenerate slopes are where the poles are handled: `λ = 0` makes the
minorant `q` itself and `λ = 1` makes it `p` itself, and the pole cases
`p x = ⊥`, `q x = ⊥` are given the same degenerate minorants directly.  So no
step ever multiplies a pole by the coefficient `0`.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Hironaka.RegularizedMaxPsh

open Hironaka
open Hironaka.RegularizedMaxEReal
open Hironaka.RegularizedMaxConvexity
open Hironaka.ScaledSmoothMax

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-! ### Two auxiliary facts -/

/-- A finite constant satisfies the disc criterion on every set. -/
theorem discPshOn_const (c : ℝ) (U : Set E) :
    DiscPshOn (fun _ : E => (c : EReal)) U := by
  refine ⟨fun _ _ => EReal.coe_ne_top c, ?_, ?_⟩
  · exact continuous_const.continuousOn.upperSemicontinuousOn
  · intro x v r hr _ C _
    have hcalc : circleDeficit (fun _ : E => (c : EReal)) x v r C
        = ((C : EReal) - (c : EReal)).toENNReal * ENNReal.ofReal (2 * Real.pi) := by
      simp only [circleDeficit]
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc]
      simp
    rw [hcalc, mul_comm]

/-- A common real translation of both branches. -/
theorem realRegularizedMax_add_const (δ a b c : ℝ) :
    realRegularizedMax δ (a + c) (b + c) = realRegularizedMax δ a b + c := by
  simp only [realRegularizedMax_apply]
  ring_nf

/-! ### The tangent minorant at a centre -/

/-- An affine combination of two potentials: `λ p + (1-λ) q + c`. -/
def affineComb (lam c : ℝ) (p q : E → EReal) : E → EReal :=
  fun y => (lam : EReal) * p y + ((1 - lam : ℝ) : EReal) * q y + (c : EReal)

@[simp]
theorem affineComb_apply (lam c : ℝ) (p q : E → EReal) (y : E) :
    affineComb lam c p q y
      = (lam : EReal) * p y + ((1 - lam : ℝ) : EReal) * q y + (c : EReal) := rfl

/-- A genuine convex combination of two potentials satisfies the disc
criterion. -/
theorem discPshOn_affineComb {lam c : ℝ} {p q : E → EReal} {U : Set E}
    (hp : DiscPshOn p U) (hq : DiscPshOn q U) (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    DiscPshOn (affineComb lam c p q) U :=
  ((hp.const_mul hlam0).add (hq.const_mul (by linarith))).add (discPshOn_const c U)

/-- The exact affine minorant of `M_δ(p, q)` at the point `x`.

Away from the poles it is the convex combination with weight
`tangentSlope δ (p x).toReal (q x).toReal`, shifted by `tangentConst`.  At a
pole of either branch, and at a degenerate slope, it is one of the two branches
itself — which is exactly what makes it a legitimate extended-real function. -/
def tangentMinorant (δ : ℝ) (p q : E → EReal) (x : E) : E → EReal :=
  if p x = ⊥ then q else
  if q x = ⊥ then p else
  if tangentSlope δ (p x).toReal (q x).toReal = 0 then q else
  if tangentSlope δ (p x).toReal (q x).toReal = 1 then p else
  affineComb (tangentSlope δ (p x).toReal (q x).toReal)
    (tangentConst δ (p x).toReal (q x).toReal) p q

/-- The minorant satisfies the disc criterion whenever both branches do. -/
theorem discPshOn_tangentMinorant {δ : ℝ} {p q : E → EReal} {U : Set E}
    (hp : DiscPshOn p U) (hq : DiscPshOn q U) (x : E) :
    DiscPshOn (tangentMinorant δ p q x) U := by
  unfold tangentMinorant
  split_ifs with h1 h2 h3 h4
  · exact hq
  · exact hp
  · exact hq
  · exact hp
  · exact discPshOn_affineComb hp hq
      (lt_of_le_of_ne (tangentSlope_nonneg _ _ _) (Ne.symm h3))
      (lt_of_le_of_ne (tangentSlope_le_one _ _ _) h4)

/-- The minorant never exceeds the regularized maximum. -/
theorem tangentMinorant_le {δ : ℝ} (hδ : 0 < δ) {p q : E → EReal} {U : Set E}
    (hpt : ∀ y ∈ U, p y ≠ ⊤) (hqt : ∀ y ∈ U, q y ≠ ⊤) (x : E) {y : E} (hy : y ∈ U) :
    tangentMinorant δ p q x y ≤ eregularizedMax δ (p y) (q y) := by
  have hmax : max (p y) (q y) ≤ eregularizedMax δ (p y) (q y) :=
    max_le_eregularizedMax hδ (hpt y hy) (hqt y hy)
  have hpy : p y ≤ eregularizedMax δ (p y) (q y) := (le_max_left _ _).trans hmax
  have hqy : q y ≤ eregularizedMax δ (p y) (q y) := (le_max_right _ _).trans hmax
  unfold tangentMinorant
  split_ifs with h1 h2 h3 h4
  · exact hqy
  · exact hpy
  · exact hqy
  · exact hpy
  · have hlam0 : 0 < tangentSlope δ (p x).toReal (q x).toReal :=
      lt_of_le_of_ne (tangentSlope_nonneg _ _ _) (Ne.symm h3)
    have hlam1 : tangentSlope δ (p x).toReal (q x).toReal < 1 :=
      lt_of_le_of_ne (tangentSlope_le_one _ _ _) h4
    rw [affineComb_apply]
    by_cases hpby : p y = ⊥
    · rw [hpby, EReal.coe_mul_bot_of_pos hlam0]
      simp
    by_cases hqby : q y = ⊥
    · rw [hqby, EReal.coe_mul_bot_of_pos (show (0:ℝ) < 1 - _ by linarith)]
      simp
    have hpe : p y = (((p y).toReal : ℝ) : EReal) := (EReal.coe_toReal (hpt y hy) hpby).symm
    have hqe : q y = (((q y).toReal : ℝ) : EReal) := (EReal.coe_toReal (hqt y hy) hqby).symm
    set A : ℝ := (p y).toReal with hAdef
    set B : ℝ := (q y).toReal with hBdef
    rw [hpe, hqe, eregularizedMax_eq_coe_realRegularizedMax
      (EReal.coe_ne_top A) (EReal.coe_ne_bot A) (EReal.coe_ne_top B) (EReal.coe_ne_bot B)]
    simp only [EReal.toReal_coe, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
    exact tangent_le_realRegularizedMax hδ _ _ A B

/-- The minorant is exact at its centre. -/
theorem tangentMinorant_self {δ : ℝ} (hδ : 0 < δ) {p q : E → EReal} {U : Set E}
    (hpt : ∀ y ∈ U, p y ≠ ⊤) (hqt : ∀ y ∈ U, q y ≠ ⊤) {x : E} (hx : x ∈ U) :
    tangentMinorant δ p q x x = eregularizedMax δ (p x) (q x) := by
  unfold tangentMinorant
  split_ifs with h1 h2 h3 h4
  · rw [h1, eregularizedMax_bot_left]
  · rw [h2, eregularizedMax_bot_right]
  · have hpe : p x = (((p x).toReal : ℝ) : EReal) := (EReal.coe_toReal (hpt x hx) h1).symm
    have hqe : q x = (((q x).toReal : ℝ) : EReal) := (EReal.coe_toReal (hqt x hx) h2).symm
    set A : ℝ := (p x).toReal with hAdef
    set B : ℝ := (q x).toReal with hBdef
    have hkey := tangent_eq_realRegularizedMax hδ A B
    rw [h3, tangentConst_eq_zero_of_slope_eq_zero h3,
      show (0:ℝ) * A + (1 - 0) * B + 0 = B by ring] at hkey
    rw [eregularizedMax_eq_coe_realRegularizedMax (hpt x hx) h1 (hqt x hx) h2,
      ← hAdef, ← hBdef, ← hkey]
    exact hqe
  · have hpe : p x = (((p x).toReal : ℝ) : EReal) := (EReal.coe_toReal (hpt x hx) h1).symm
    have hqe : q x = (((q x).toReal : ℝ) : EReal) := (EReal.coe_toReal (hqt x hx) h2).symm
    set A : ℝ := (p x).toReal with hAdef
    set B : ℝ := (q x).toReal with hBdef
    have hkey := tangent_eq_realRegularizedMax hδ A B
    rw [h4, tangentConst_eq_zero_of_slope_eq_one h4,
      show (1:ℝ) * A + (1 - 1) * B + 0 = A by ring] at hkey
    rw [eregularizedMax_eq_coe_realRegularizedMax (hpt x hx) h1 (hqt x hx) h2,
      ← hAdef, ← hBdef, ← hkey]
    exact hpe
  · have hpe : p x = (((p x).toReal : ℝ) : EReal) := (EReal.coe_toReal (hpt x hx) h1).symm
    have hqe : q x = (((q x).toReal : ℝ) : EReal) := (EReal.coe_toReal (hqt x hx) h2).symm
    set A : ℝ := (p x).toReal with hAdef
    set B : ℝ := (q x).toReal with hBdef
    rw [affineComb_apply, hpe, hqe, eregularizedMax_eq_coe_realRegularizedMax
      (EReal.coe_ne_top A) (EReal.coe_ne_bot A) (EReal.coe_ne_top B) (EReal.coe_ne_bot B)]
    simp only [EReal.toReal_coe, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_eq_coe_iff]
    exact tangent_eq_realRegularizedMax hδ A B

/-! ### The submean inequality from exact minorants -/

/-- **A function touched from below at every centre by a submean minorant is
itself submean.**  This is the device that replaces a two-variable Jensen
inequality. -/
theorem hasDiscSubmeanOn_of_tangentMinorants {f : E → EReal} {U : Set E}
    (h : ∀ x ∈ U, ∃ g : E → EReal, HasDiscSubmeanOn g U ∧
      (∀ y ∈ U, g y ≤ f y) ∧ g x = f x) :
    HasDiscSubmeanOn f U := by
  intro x v r hr hD C hC
  have hxU : x ∈ U := hD (center_mem_affineClosedDisc x v hr.le)
  obtain ⟨g, hg, hle, heq⟩ := h x hxU
  have hstep : circleDeficit f x v r C ≤ circleDeficit g x v r C :=
    circleDeficit_antitone (u := g) (w := f) x v r C
      (fun t => hle _ (hD (circle_mem_affineClosedDisc x v hr.le t)))
  have hgC : ∀ y ∈ affineClosedDisc x v r, g y ≤ (C : EReal) :=
    fun y hy => (hle y (hD hy)).trans (hC y hy)
  have hsub := hg x v r hr hD C hgC
  rw [heq] at hsub
  exact hstep.trans hsub

/-! ### The theorem -/

/-- **Upper semicontinuity of the regularized maximum.**  Monotonicity plus the
translation identity; the `δ`-gap over the ordinary maximum never appears. -/
theorem upperSemicontinuousOn_eregularizedMax {δ : ℝ} (hδ : 0 < δ)
    {p q : E → EReal} {U : Set E}
    (hp : UpperSemicontinuousOn p U) (hq : UpperSemicontinuousOn q U)
    (hpt : ∀ x ∈ U, p x ≠ ⊤) (hqt : ∀ x ∈ U, q x ≠ ⊤) :
    UpperSemicontinuousOn (fun y => eregularizedMax δ (p y) (q y)) U := by
  intro x hx M hM
  replace hM : eregularizedMax δ (p x) (q x) < M := hM
  obtain ⟨A, B, hA, hB, hAB⟩ :
      ∃ A B : ℝ, p x < (A : EReal) ∧ q x < (B : EReal) ∧
        eregularizedMax δ ((A : ℝ) : EReal) ((B : ℝ) : EReal) < M := by
    have hcoe : ∀ A B : ℝ, eregularizedMax δ ((A : ℝ) : EReal) ((B : ℝ) : EReal)
        = ((realRegularizedMax δ A B : ℝ) : EReal) := fun A B => by
      rw [eregularizedMax_eq_coe_realRegularizedMax (by simp) (by simp) (by simp) (by simp)]
      simp
    by_cases hpb : p x = ⊥
    · by_cases hqb : q x = ⊥
      · obtain ⟨t, _, htM⟩ := EReal.lt_iff_exists_real_btwn.mp
          (show (⊥ : EReal) < M from lt_of_le_of_lt bot_le hM)
        refine ⟨t - δ, t, by rw [hpb]; exact EReal.bot_lt_coe _,
          by rw [hqb]; exact EReal.bot_lt_coe _, ?_⟩
        rw [hcoe]
        have : realRegularizedMax δ (t - δ) t = t :=
          scaledSmoothMax_eq_right (E := Unit) hδ (z := ()) (by simp)
        rwa [this]
      · have hfx : eregularizedMax δ (p x) (q x) = q x := by rw [hpb, eregularizedMax_bot_left]
        rw [hfx] at hM
        obtain ⟨t, hqt', htM⟩ := EReal.lt_iff_exists_real_btwn.mp hM
        refine ⟨t - δ, t, by rw [hpb]; exact EReal.bot_lt_coe _, hqt', ?_⟩
        rw [hcoe]
        have : realRegularizedMax δ (t - δ) t = t :=
          scaledSmoothMax_eq_right (E := Unit) hδ (z := ()) (by simp)
        rwa [this]
    · by_cases hqb : q x = ⊥
      · have hfx : eregularizedMax δ (p x) (q x) = p x := by rw [hqb, eregularizedMax_bot_right]
        rw [hfx] at hM
        obtain ⟨t, hpt', htM⟩ := EReal.lt_iff_exists_real_btwn.mp hM
        refine ⟨t, t - δ, hpt', by rw [hqb]; exact EReal.bot_lt_coe _, ?_⟩
        rw [hcoe]
        have : realRegularizedMax δ t (t - δ) = t :=
          scaledSmoothMax_eq_left (E := Unit) hδ (z := ()) (by simp)
        rwa [this]
      · have hpe : p x = ((p x).toReal : EReal) := (EReal.coe_toReal (hpt x hx) hpb).symm
        have hqe : q x = ((q x).toReal : EReal) := (EReal.coe_toReal (hqt x hx) hqb).symm
        have hfx : eregularizedMax δ (p x) (q x)
            = ((realRegularizedMax δ (p x).toReal (q x).toReal : ℝ) : EReal) := by
          conv_lhs => rw [hpe, hqe]
          rw [hcoe]
        rw [hfx] at hM
        obtain ⟨t, hrt, htM⟩ := EReal.lt_iff_exists_real_btwn.mp hM
        rw [EReal.coe_lt_coe_iff] at hrt
        set eps : ℝ := t - realRegularizedMax δ (p x).toReal (q x).toReal with hepsdef
        have heps : 0 < eps := by rw [hepsdef]; linarith
        refine ⟨(p x).toReal + eps, (q x).toReal + eps, ?_, ?_, ?_⟩
        · conv_lhs => rw [hpe]
          exact EReal.coe_lt_coe_iff.mpr (by linarith)
        · conv_lhs => rw [hqe]
          exact EReal.coe_lt_coe_iff.mpr (by linarith)
        · rw [hcoe, realRegularizedMax_add_const]
          have : realRegularizedMax δ (p x).toReal (q x).toReal + eps = t := by
            rw [hepsdef]; ring
          rwa [this]
  filter_upwards [hp x hx (A : EReal) hA, hq x hx (B : EReal) hB] with y hyA hyB
  exact lt_of_le_of_lt
    (eregularizedMax_mono hδ hyA.le hyB.le (EReal.coe_ne_top A) (EReal.coe_ne_top B)) hAB

/-- **The regularized maximum satisfies the disc criterion.** -/
theorem discPshOn_eregularizedMax {δ : ℝ} (hδ : 0 < δ) {p q : E → EReal} {U : Set E}
    (hp : DiscPshOn p U) (hq : DiscPshOn q U) :
    DiscPshOn (fun y => eregularizedMax δ (p y) (q y)) U := by
  refine ⟨fun x hx => eregularizedMax_ne_top (hp.ne_top x hx) (hq.ne_top x hx),
    upperSemicontinuousOn_eregularizedMax hδ hp.upperSemicontinuousOn hq.upperSemicontinuousOn
      hp.ne_top hq.ne_top, ?_⟩
  refine hasDiscSubmeanOn_of_tangentMinorants (fun x hx => ?_)
  exact ⟨tangentMinorant δ p q x, (discPshOn_tangentMinorant hp hq x).submean,
    fun y hy => tangentMinorant_le hδ hp.ne_top hq.ne_top x hy,
    tangentMinorant_self hδ hp.ne_top hq.ne_top hx⟩

/-- **Demailly's regularized maximum of two PSH germs is a PSH germ.** -/
theorem plurisubharmonicAt_eregularizedMax {δ : ℝ} (hδ : 0 < δ) {p q : E → EReal} {x : E}
    (hp : PlurisubharmonicAt p x) (hq : PlurisubharmonicAt q x) :
    PlurisubharmonicAt (fun y => eregularizedMax δ (p y) (q y)) x := by
  obtain ⟨U, hU, hxU, hdp⟩ := hp
  obtain ⟨V, hV, hxV, hdq⟩ := hq
  exact ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩,
    discPshOn_eregularizedMax hδ (hdp.mono inter_subset_left) (hdq.mono inter_subset_right)⟩

/-- **Demailly, CADG I.5.18.**  The regularized maximum of two plurisubharmonic
functions is plurisubharmonic. -/
theorem plurisubharmonicOn_eregularizedMax {δ : ℝ} (hδ : 0 < δ) {p q : E → EReal} {U : Set E}
    (hp : PlurisubharmonicOn p U) (hq : PlurisubharmonicOn q U) :
    PlurisubharmonicOn (fun y => eregularizedMax δ (p y) (q y)) U :=
  fun x hx => plurisubharmonicAt_eregularizedMax hδ (hp x hx) (hq x hx)

end

end Hironaka.RegularizedMaxPsh
