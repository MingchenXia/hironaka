import Hironaka.Analytic.PotentialTheory.MultiplierIdealsBasic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

set_option autoImplicit false

/-!
# Hiep's three-term estimate: a uniform bound at a higher exponent gives `L¹` convergence

The last step of both parts of the Main theorem of Hiep, *The weighted log canonical
threshold* (`hiep14-weighted-lct:proof-i`, `hiep14-weighted-lct:proof-ii`) is measure
theory only.  Once the `L²` extension argument has produced a uniform bound

  `∫ |f|² e^{-2c̃ψ_j} ≤ M`   for some `c̃ > c` and all large `j`,

and `ψ_j → φ` almost everywhere with `φ ≤ 0` (or only `φ ≤ C`), Hiep concludes
`|f|² e^{-2cψ_j} → |f|² e^{-2cφ}` in `L¹` from

  `∫ |f|² |e^{-2cψ_j} - e^{-2cφ}|
     ≤ ∫_{|ψ_j| ≤ A} |f|² |e^{-2cψ_j} - e^{-2cφ}| + ∫_{ψ_j < -A} |f|² e^{-2cφ}
       + e^{-2(c̃-c)A} ∫_{ψ_j < -A} |f|² e^{-2c̃ψ_j}`.

This module proves that step, `tendsto_lintegral_sub_of_uniform_bound`, for an arbitrary
measure, an arbitrary nonnegative factor `g` in place of `|f|²`, and the project's weight
`multiplierWeight c = exp (-c ·)` (Hiep's exponent `2c` is `c` here).  The split is
organized slightly differently from Hiep's, to stay inside `ℝ≥0∞` and to avoid a
difference of possibly infinite integrals: the one-sided difference
`D_j = g e^{-cψ_j} - g e^{-cφ}` (truncated at `0`) satisfies

  `D_j ≤ min (D_j, e^{cA} g) + e^{-(c̃-c)A} g e^{-c̃ψ_j}`,

the first term tends to `0` in `L¹` by dominated convergence (dominated by `e^{cA} g`,
which is integrable because `e^{-cφ} ≥ e^{-cC}`), and the second is at most `e^{-(c̃-c)A} M`
for large `j`; letting `A → ∞` finishes.  No inequality `ψ_j ≤ φ` is needed for this
one-sided statement; under `ψ_j ≤ φ` the truncated difference is the full `L¹` distance.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Hironaka

/-! ### Pointwise weight comparisons -/

theorem continuous_multiplierWeight {c : ℝ} (hc : 0 < c) :
    Continuous (multiplierWeight c) := by
  have hmul : Continuous fun a : EReal => (c : EReal) * a := by
    refine continuous_iff_continuousAt.mpr fun a => ?_
    exact (EReal.continuousAt_mul (p := ((c : EReal), a))
      (Or.inl (by simpa using hc.ne')) (Or.inl (by simpa using hc.ne'))
      (Or.inl (EReal.coe_ne_bot c)) (Or.inl (EReal.coe_ne_top c))).comp
      (continuousAt_const.prodMk continuousAt_id)
  exact ENNReal.continuous_exp.comp (continuous_neg.comp hmul)

theorem one_le_multiplierWeight_of_nonpos {c : ℝ} (hc : 0 ≤ c) {a : EReal}
    (ha : a ≤ 0) : 1 ≤ multiplierWeight c a := by
  have h := multiplierWeight_antitone hc ha
  simpa [multiplierWeight] using h

/-- Below a finite majorant `C`, the weight is at least `e^{-cC}`, so a factor is
controlled by its weighted value. -/
theorem le_ofReal_exp_mul_multiplierWeight {c C : ℝ} (hc : 0 ≤ c) {a : EReal}
    (ha : a ≤ (C : EReal)) (g : ℝ≥0∞) :
    g ≤ ENNReal.ofReal (Real.exp (c * C)) * (g * multiplierWeight c a) := by
  have hW := multiplierWeight_antitone hc ha
  rw [multiplierWeight_coe] at hW
  calc g = g * (ENNReal.ofReal (Real.exp (c * C)) * ENNReal.ofReal (Real.exp (-(c * C)))) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_neg_cancel,
          Real.exp_zero, ENNReal.ofReal_one, mul_one]
    _ ≤ g * (ENNReal.ofReal (Real.exp (c * C)) * multiplierWeight c a) := by gcongr
    _ = ENNReal.ofReal (Real.exp (c * C)) * (g * multiplierWeight c a) := by ring

/-- Above the level `-A`, the weight is at most `e^{cA}`. -/
theorem multiplierWeight_le_of_neg_le {c A : ℝ} (hc : 0 ≤ c) {a : EReal}
    (ha : ((-A : ℝ) : EReal) ≤ a) :
    multiplierWeight c a ≤ ENNReal.ofReal (Real.exp (c * A)) := by
  have h := multiplierWeight_antitone hc ha
  rw [multiplierWeight_coe] at h
  simpa using h

/-- Below the level `-A`, a lower exponent costs a factor `e^{-(d-c)A}` against a higher
one. -/
theorem multiplierWeight_le_mul_of_le_neg {c d A : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    {a : EReal} (ha : a ≤ ((-A : ℝ) : EReal)) :
    multiplierWeight c a ≤
      ENNReal.ofReal (Real.exp (-((d - c) * A))) * multiplierWeight d a := by
  induction a using EReal.rec with
  | bot =>
      rw [multiplierWeight_bot hc, multiplierWeight_bot (hc.trans_le hcd),
        ENNReal.mul_top (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne']
  | top => exact absurd ha (by simp)
  | coe b =>
      have hb : b ≤ -A := EReal.coe_le_coe_iff.mp ha
      rw [multiplierWeight_coe, multiplierWeight_coe,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      nlinarith

/-- The pointwise three-term split. -/
theorem sub_le_min_add_of_le {c d A : ℝ} (hc : 0 < c) (hcd : c ≤ d) (g : ℝ≥0∞)
    (a b : EReal) :
    g * multiplierWeight c a - g * multiplierWeight c b ≤
      min (g * multiplierWeight c a - g * multiplierWeight c b)
          (g * ENNReal.ofReal (Real.exp (c * A))) +
        ENNReal.ofReal (Real.exp (-((d - c) * A))) * (g * multiplierWeight d a) := by
  rcases le_total a ((-A : ℝ) : EReal) with ha | ha
  · refine le_trans ?_ le_add_self
    calc g * multiplierWeight c a - g * multiplierWeight c b
        ≤ g * multiplierWeight c a := tsub_le_self
      _ ≤ g * (ENNReal.ofReal (Real.exp (-((d - c) * A))) * multiplierWeight d a) := by
          gcongr; exact multiplierWeight_le_mul_of_le_neg hc hcd ha
      _ = ENNReal.ofReal (Real.exp (-((d - c) * A))) * (g * multiplierWeight d a) := by
          ring
  · refine le_trans (le_of_eq ?_) le_self_add
    refine (min_eq_left ?_).symm
    calc g * multiplierWeight c a - g * multiplierWeight c b
        ≤ g * multiplierWeight c a := tsub_le_self
      _ ≤ g * ENNReal.ofReal (Real.exp (c * A)) := by
          gcongr; exact multiplierWeight_le_of_neg_le hc.le ha

/-! ### The estimate -/

/-- **Hiep's three-term estimate.**  If `ψ_j → φ` almost everywhere, `φ ≤ C`,
`g e^{-cφ}` is integrable, and `∫ g e^{-dψ_j}` is bounded for large `j` at some
exponent `d > c`, then the one-sided `L¹` distance from `g e^{-cψ_j}` to `g e^{-cφ}`
tends to zero. -/
theorem tendsto_lintegral_sub_of_uniform_bound {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {g : α → ℝ≥0∞} {φ : α → EReal} {ψ : ℕ → α → EReal}
    {c d C : ℝ} {M : ℝ≥0∞} (hc : 0 < c) (hcd : c < d)
    (hg : AEMeasurable g μ) (hφm : AEMeasurable φ μ) (hψm : ∀ j, AEMeasurable (ψ j) μ)
    (hφC : ∀ᵐ x ∂μ, φ x ≤ (C : EReal))
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun j => ψ j x) atTop (𝓝 (φ x)))
    (hint : ∫⁻ x, g x * multiplierWeight c (φ x) ∂μ ≠ ∞)
    (hM : M ≠ ∞)
    (hunif : ∀ᶠ j in atTop, ∫⁻ x, g x * multiplierWeight d (ψ j x) ∂μ ≤ M) :
    Tendsto (fun j => ∫⁻ x, (g x * multiplierWeight c (ψ j x) -
      g x * multiplierWeight c (φ x)) ∂μ) atTop (𝓝 0) := by
  have hWc := (continuous_multiplierWeight hc).measurable
  have hWd := (continuous_multiplierWeight (hc.trans hcd)).measurable
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  -- Choose the cut level `A` so that the tail term is at most `ε / 2`.
  have hsmall : Tendsto (fun A : ℝ => ENNReal.ofReal (Real.exp (-((d - c) * A))) * M)
      atTop (𝓝 0) := by
    have hexp : Tendsto (fun A : ℝ => Real.exp (-((d - c) * A))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp (Tendsto.const_mul_atTop (sub_pos.mpr hcd) tendsto_id))
    have h := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal hexp) (b := M) (Or.inr hM)
    simpa using h
  obtain ⟨A, hA⟩ := (hsmall.eventually (Iic_mem_nhds hε2)).exists
  set E : ℝ≥0∞ := ENNReal.ofReal (Real.exp (c * A)) with hE
  set D : ℕ → α → ℝ≥0∞ := fun j x =>
    g x * multiplierWeight c (ψ j x) - g x * multiplierWeight c (φ x) with hD
  have hDmeas : ∀ j, AEMeasurable (D j) μ := fun j =>
    (hg.mul (hWc.comp_aemeasurable (hψm j))).sub (hg.mul (hWc.comp_aemeasurable hφm))
  -- The truncated first term tends to zero by dominated convergence.
  have hdom : Tendsto (fun j => ∫⁻ x, min (D j x) (g x * E) ∂μ) atTop (𝓝 0) := by
    have hgfin : ∫⁻ x, g x ∂μ ≠ ∞ := by
      refine ne_top_of_le_ne_top
        (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := Real.exp (c * C))) hint) ?_
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono_ae ?_
      filter_upwards [hφC] with x hx
      exact le_ofReal_exp_mul_multiplierWeight hc.le hx (g x)
    have hlim0 : ∀ᵐ x ∂μ, Tendsto (fun j => min (D j x) (g x * E)) atTop (𝓝 0) := by
      filter_upwards [hlim, hφC,
        ae_lt_top' (hg.mul (hWc.comp_aemeasurable hφm)) hint] with x hx hx0 hxfin
      have h1 : Tendsto (fun j => multiplierWeight c (ψ j x)) atTop
          (𝓝 (multiplierWeight c (φ x))) :=
        ((continuous_multiplierWeight hc).tendsto _).comp hx
      have hpos : 0 < multiplierWeight c (C : EReal) := by
        rw [multiplierWeight_coe]; exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)
      have hne : multiplierWeight c (φ x) ≠ 0 :=
        (lt_of_lt_of_le hpos (multiplierWeight_antitone hc.le hx0)).ne'
      have h2 := ENNReal.Tendsto.const_mul h1 (a := g x) (Or.inl hne)
      have h3 := ENNReal.Tendsto.sub h2 (tendsto_const_nhds (x := g x * multiplierWeight c (φ x)))
        (Or.inl hxfin.ne)
      rw [tsub_self] at h3
      have h4 := h3.min (tendsto_const_nhds (x := g x * E))
      simpa using h4
    have h := tendsto_lintegral_of_dominated_convergence' (μ := μ)
      (F := fun j x => min (D j x) (g x * E)) (f := fun _ => 0) (fun x => g x * E)
      (fun j => (hDmeas j).min (hg.mul_const E))
      (fun j => ae_of_all _ fun x => min_le_right _ _)
      (by rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
          exact ENNReal.mul_ne_top hgfin ENNReal.ofReal_ne_top)
      hlim0
    simpa using h
  filter_upwards [hdom.eventually (Iic_mem_nhds hε2), hunif] with j hj hjM
  calc ∫⁻ x, D j x ∂μ
      ≤ ∫⁻ x, (min (D j x) (g x * E) +
          ENNReal.ofReal (Real.exp (-((d - c) * A))) *
            (g x * multiplierWeight d (ψ j x))) ∂μ :=
        lintegral_mono fun x => sub_le_min_add_of_le hc hcd.le (g x) (ψ j x) (φ x)
    _ = (∫⁻ x, min (D j x) (g x * E) ∂μ) +
          ENNReal.ofReal (Real.exp (-((d - c) * A))) *
            ∫⁻ x, g x * multiplierWeight d (ψ j x) ∂μ := by
        rw [lintegral_add_left' ((hDmeas j).min (hg.mul_const E)),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ε / 2 + ENNReal.ofReal (Real.exp (-((d - c) * A))) * M := by
        gcongr
    _ ≤ ε / 2 + ε / 2 := by gcongr
    _ = ε := ENNReal.add_halves ε

end Hironaka
