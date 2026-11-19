import Hironaka.Analytic.QuantitativeRegularizationTruncationLimit
import Hironaka.Analytic.HolomorphicPullback

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# From smooth weights to an arbitrary plurisubharmonic one

Source: Copy-4, `lem:regularization`, Step 2 (`transcendental-nakamaye-copy4-20260911`);
blueprint `ana:regularization`.

`QuantitativeRegularizationTruncationLimit` passes from the truncations `max (u, -k)` to
`u`.  The truncations are plurisubharmonic and locally bounded, but not smooth, and every
quantitative Bergman estimate in the project needs a *smooth* weight.  This module adds
the second and last layer: `HolomorphicPullback.exists_decreasingMollifierApproximation`
regularizes a locally bounded plurisubharmonic function by a decreasing sequence of
smooth plurisubharmonic ones on a relatively compact subdomain, and
`QuantitativeRegularizationSingularWeight.bergmanSup_iSup_weight` again turns that into a
decreasing limit of Bergman kernels.

The endpoint is `bergmanSup_multiplierWeight_le_mul_of_smoothPsh`:

> if two Bergman kernels are comparable with ONE constant `C` for **every** weight
> `e^{-cg}` with `g` smooth plurisubharmonic and bounded below on `A`, then they are
> comparable with the same `C` for `e^{-cu}` with `u` merely plurisubharmonic on a
> neighbourhood of `A`.

That is precisely the hypothesis-to-conclusion step Copy-4 performs between its Step-2
overlap estimate and its application to `ϕ = m Ψ`, and the constant of
`BergmanOverlapFixedCover.exists_overlapConst_finite` is already quantified in the
required order: it is fixed by the cover, before the weight.  The two hypotheses that
the smooth approximants must satisfy — smooth plurisubharmonic, and bounded below — are
exactly the two that the mollifier family does satisfy: `IsDecreasingApproximation`
gives smoothness and plurisubharmonicity, and the approximants dominate their limit,
which for the `k`-th truncation is bounded below by `-k`.
-/

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace Hironaka.QuantitativeRegularizationSmoothWeightLimit

noncomputable section

open Hironaka.MongeAmpere BergmanSupWeight
open Hironaka.QuantitativeRegularizationSingularWeight
open Hironaka.QuantitativeRegularizationTruncationLimit

variable {d : ℕ} [MeasurableSpace (ComplexModel d)] [BorelSpace (ComplexModel d)]

variable {A : Opens (ComplexModel d)} {p : ComplexModel d → ℝ}
  {f : ℕ → ComplexModel d → ℝ} {c : ℝ}

/-- A decreasing approximation dominates its limit. -/
theorem le_of_isDecreasingApproximation (hf : IsDecreasingApproximation A p f) (j : ℕ)
    {z : ComplexModel d} (hz : z ∈ A) : p z ≤ f j z :=
  le_of_tendsto (hf.2.2 z hz) (eventually_atTop.2 ⟨j, fun _ hl => hf.2.1 z hz hl⟩)

/-- Smoothing from above lowers the weight, so the weights of a decreasing approximation
**increase**. -/
theorem smoothWeight_monotone (hf : IsDecreasingApproximation A p f) (hc : 0 ≤ c)
    {z : ComplexModel d} (hz : z ∈ A) :
    Monotone fun j => multiplierWeight c ((f j z : ℝ) : EReal) := fun _ _ hij =>
  multiplierWeight_antitone hc (EReal.coe_le_coe_iff.mpr (hf.2.1 z hz hij))

/-- The smooth weights exhaust the weight of the limit. -/
theorem iSup_smoothWeight (hf : IsDecreasingApproximation A p f) (hc : 0 ≤ c)
    {z : ComplexModel d} (hz : z ∈ A) :
    multiplierWeight c ((p z : ℝ) : EReal)
      = ⨆ j, multiplierWeight c ((f j z : ℝ) : EReal) :=
  tendsto_nhds_unique
    (((continuous_multiplierWeight_coe c).tendsto _).comp (hf.2.2 z hz))
    (tendsto_atTop_iSup (smoothWeight_monotone hf hc hz))

/-- Each smooth weight is a.e.-measurable on a measurable subdomain. -/
theorem aemeasurable_smoothWeight (hf : IsDecreasingApproximation A p f) (j : ℕ)
    {D : Set (ComplexModel d)} (hD : MeasurableSet D) (hDA : D ⊆ A) :
    AEMeasurable (fun z => multiplierWeight c ((f j z : ℝ) : EReal))
      (volume.restrict D) :=
  ((continuous_multiplierWeight_coe c).measurable).comp_aemeasurable
    ((((hf.1 j).1.continuousOn).mono hDA).aemeasurable hD)

/-- The zeroth smooth weight is locally bounded below by a positive constant: a smooth
function is locally bounded above. -/
theorem exists_lower_bound_smoothWeight_zero (hf : IsDecreasingApproximation A p f)
    (hc : 0 ≤ c) {x : ComplexModel d} (hx : x ∈ A) :
    ∃ r > 0, ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∈ ball x r, ENNReal.ofReal δ ≤ multiplierWeight c ((f 0 y : ℝ) : EReal) := by
  obtain ⟨r, hr, hrA⟩ := Metric.mem_nhds_iff.mp (A.isOpen.mem_nhds hx)
  have hcb : closedBall x (r / 2) ⊆ (A : Set (ComplexModel d)) :=
    (closedBall_subset_ball (by linarith)).trans hrA
  obtain ⟨C, hC⟩ := (isCompact_closedBall x (r / 2)).exists_bound_of_continuousOn
    (((hf.1 0).1.continuousOn).mono hcb)
  refine ⟨r / 2, by linarith, Real.exp (-(c * C)), Real.exp_pos _, fun y hy => ?_⟩
  have hyC : f 0 y ≤ C :=
    (abs_le.mp ((Real.norm_eq_abs _) ▸ hC y (ball_subset_closedBall hy))).2
  have hmono : -(c * C) ≤ -(c * f 0 y) := by
    have := mul_le_mul_of_nonneg_left hyC hc
    linarith
  simpa [multiplierWeight_coe] using
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hmono)

/-- **The Bergman kernel of a locally bounded plurisubharmonic weight is the decreasing
limit of the kernels of its smooth regularizations.** -/
theorem bergmanSup_multiplierWeight_eq_iInf_smoothWeight
    (hf : IsDecreasingApproximation A p f) (hc : 0 ≤ c)
    {D : Set (ComplexModel d)} (hDo : IsOpen D) (hDA : D ⊆ A)
    {y : ComplexModel d} (hy : y ∈ D) :
    bergmanSup D (fun z => multiplierWeight c ((p z : ℝ) : EReal)) y
      = ⨅ j, bergmanSup D (fun z => multiplierWeight c ((f j z : ℝ) : EReal)) y :=
  bergmanSup_iSup_weight hDo (fun _ hz => smoothWeight_monotone hf hc (hDA hz))
    (fun j => aemeasurable_smoothWeight hf j hDo.measurableSet hDA)
    (fun _ hx => exists_lower_bound_smoothWeight_zero hf hc (hDA hx))
    (fun _ hz => iSup_smoothWeight hf hc (hDA hz)) hy

/-- A comparison uniform in the regularization level passes to the limit. -/
theorem bergmanSup_multiplierWeight_le_mul_of_smoothWeight
    (hf : IsDecreasingApproximation A p f) (hc : 0 ≤ c)
    {D₁ D₂ : Set (ComplexModel d)} (hD₁ : MeasurableSet D₁) (hD₁A : D₁ ⊆ A)
    (hD₂ : IsOpen D₂) (hD₂A : D₂ ⊆ A)
    {C : ℝ≥0∞} (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    {y : ComplexModel d} (hy : y ∈ D₂)
    (hcomp : ∀ j : ℕ,
      bergmanSup D₁ (fun z => multiplierWeight c ((f j z : ℝ) : EReal)) y ≤
        C * bergmanSup D₂ (fun z => multiplierWeight c ((f j z : ℝ) : EReal)) y) :
    bergmanSup D₁ (fun z => multiplierWeight c ((p z : ℝ) : EReal)) y ≤
      C * bergmanSup D₂ (fun z => multiplierWeight c ((p z : ℝ) : EReal)) y :=
  bergmanSup_le_mul_of_iSup_weight hD₁ hD₂
    (fun _ hz => smoothWeight_monotone hf hc (hD₂A hz))
    (fun j => aemeasurable_smoothWeight hf j hD₂.measurableSet hD₂A)
    (fun _ hx => exists_lower_bound_smoothWeight_zero hf hc (hD₂A hx))
    (fun _ hz => iSup_smoothWeight hf hc (hD₁A hz))
    (fun _ hz => iSup_smoothWeight hf hc (hD₂A hz)) hC0 hCtop hy hcomp

/-! ### The two layers together -/

variable {Ω : Opens (ComplexModel d)} {u : ComplexModel d → EReal}

/-- **The singular-weight gap, closed for the two-domain comparison.**  A comparison of two
weighted Bergman kernels that holds, with one constant, for every smooth plurisubharmonic
weight bounded below on `A`, holds for `e^{-cu}` with `u` an arbitrary plurisubharmonic
function on a neighbourhood `Ω` of `A` — in particular for Copy-4's `ϕ = m Ψ`, which is
`-∞` on a polar set.

The mollifier layer supplies the smooth approximants of each truncation
`max (u, -k)`, which are bounded below by `-k`; the truncation layer then removes the
truncation. -/
theorem bergmanSup_multiplierWeight_le_mul_of_smoothPsh
    (hA : RelativelyCompactIn A Ω) (hu : PlurisubharmonicOn u Ω) (hc : 0 < c)
    {D₁ D₂ : Set (ComplexModel d)} (hD₁ : MeasurableSet D₁) (hD₁A : D₁ ⊆ A)
    (hD₂ : IsOpen D₂) (hD₂A : D₂ ⊆ A)
    {C : ℝ≥0∞} (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    {y : ComplexModel d} (hy : y ∈ D₂)
    (hcomp : ∀ g : ComplexModel d → ℝ, IsSmoothPshOn A g →
      (∃ B : ℝ, ∀ z ∈ A, B ≤ g z) →
      bergmanSup D₁ (fun z => multiplierWeight c ((g z : ℝ) : EReal)) y ≤
        C * bergmanSup D₂ (fun z => multiplierWeight c ((g z : ℝ) : EReal)) y) :
    bergmanSup D₁ (fun z => multiplierWeight c (u z)) y ≤
      C * bergmanSup D₂ (fun z => multiplierWeight c (u z)) y := by
  have hAΩ : (A : Set (ComplexModel d)) ⊆ Ω := subset_closure.trans hA.2
  -- the comparison at each truncation level, from the mollifier layer
  have hlevel : ∀ k : ℕ,
      bergmanSup D₁ (truncationWeight c u k) y ≤
        C * bergmanSup D₂ (truncationWeight c u k) y := by
    intro k
    obtain ⟨f, hf⟩ := HolomorphicPullback.exists_decreasingMollifierApproximation
      (truncationReal_isLocallyBoundedPshOn hu k) hA
    -- the `k`-th truncation is bounded below by `-k`, hence so is every approximant
    have hfloor : ∀ (j : ℕ), ∀ z ∈ (A : Set (ComplexModel d)), -(k : ℝ) ≤ f j z := by
      intro j z hz
      refine le_trans ?_ (le_of_isDecreasingApproximation hf j hz)
      apply EReal.coe_le_coe_iff.mp
      rw [coe_truncationReal hu k (hAΩ hz)]
      exact truncation_lower_bound u k z
    exact bergmanSup_multiplierWeight_le_mul_of_smoothWeight hf hc.le hD₁ hD₁A hD₂ hD₂A
      hC0 hCtop hy fun j => hcomp (f j) (hf.1 j) ⟨-(k : ℝ), hfloor j⟩
  exact bergmanSup_multiplierWeight_le_mul_of_truncationWeight hu hc hD₁ (hD₁A.trans hAΩ)
    hD₂ (hD₂A.trans hAΩ) hC0 hCtop hy hlevel

end

end Hironaka.QuantitativeRegularizationSmoothWeightLimit
