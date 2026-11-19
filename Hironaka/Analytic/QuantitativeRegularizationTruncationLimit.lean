import Hironaka.Analytic.QuantitativeRegularizationSingularWeight
import Hironaka.Analytic.OhsawaTakegoshiRegularReduction
import Hironaka.Analytic.ChartWeightedL2Transfer

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The Bergman kernel of `e^{-cu}` from the kernels of the truncations `max (u, -k)`

Source: Copy-4, `lem:regularization`, Step 2 (`transcendental-nakamaye-copy4-20260911`);
blueprint `ana:regularization`.

`QuantitativeRegularizationSingularWeight.bergmanSup_iSup_weight` is the abstract limit:
for weights increasing on `D` and locally bounded below there, the kernel of their
supremum is the infimum of the kernels.  This module runs it on the approximating
sequence the manuscript actually uses, the plurisubharmonic truncations
`truncationReal u k = (max (u, -k)).toReal` of `Hironaka.MongeAmpere`:

  `bergmanSup D (e^{-cu}) y = ⨅ k, bergmanSup D (e^{-c·max (u,-k)}) y`.

Each hypothesis of the abstract theorem is discharged from plurisubharmonicity of `u`
alone:

* monotone — `truncationReal` is antitone in `k` and `multiplierWeight c` is antitone
  (`multiplierWeight_antitone`);
* supremum — `OhsawaTakegoshiRegularReduction.multiplierWeight_le_iSup_truncationReal`
  gives `≥`, and truncation only raises the potential, which gives `≤`;
* a.e.-measurable — the truncations are plurisubharmonic, hence upper semicontinuous,
  hence a.e.-measurable on an open set
  (`ChartWeightedL2.aemeasurable_restrict_of_upperSemicontinuousOn`);
* locally bounded below — `truncationReal_isLocallyBoundedPshOn`: the truncation is
  locally bounded *above*, so `e^{-c·truncation}` is locally bounded *below* by a
  positive constant.

`bergmanSup_multiplierWeight_le_mul_of_truncation` is the consequence: a comparison of
two Bergman kernels with one constant, valid for every truncation, is a comparison for
the singular weight itself.  This is the shape in which Copy-4's `eq:reg-overlap` is
consumed, `C_B` being fixed by the cover before the weight
(`BergmanOverlapFixedCover.exists_overlapConst_finite`).

The remaining half of frontier item 1 is the *smoothness* of the approximating weight:
the truncations are plurisubharmonic and locally bounded but not smooth, so one further
layer, `HolomorphicPullback.exists_decreasingMollifierApproximation` on a relatively
compact subdomain, is needed before the overlap estimate itself applies.  That layer is
another instance of the same abstract theorem, and is not done here.
-/

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace Hironaka.QuantitativeRegularizationTruncationLimit

noncomputable section

open Hironaka.MongeAmpere BergmanSupWeight
open Hironaka.QuantitativeRegularizationSingularWeight

variable {d : ℕ} [MeasurableSpace (ComplexModel d)] [BorelSpace (ComplexModel d)]

/-- The weight of the truncation, as a function of the truncation level. -/
def truncationWeight (c : ℝ) (u : ComplexModel d → EReal) (k : ℕ) :
    ComplexModel d → ℝ≥0∞ :=
  fun z => multiplierWeight c ((truncationReal u k z : ℝ) : EReal)

variable {Ω : Opens (ComplexModel d)} {u : ComplexModel d → EReal} {c : ℝ}

/-- Truncating raises the potential, so it lowers the weight: the truncated weights
**increase** with the truncation level.  This is the direction that makes the kernels
decrease, and it is why no monotone-convergence argument closes the gap. -/
theorem truncationWeight_monotone (hu : PlurisubharmonicOn u Ω) (hc : 0 ≤ c)
    {z : ComplexModel d} (hz : z ∈ Ω) :
    Monotone fun k : ℕ => truncationWeight c u k z := fun _ _ hkl =>
  multiplierWeight_antitone hc
    (EReal.coe_le_coe_iff.mpr (truncationReal_antitone hu hz hkl))

/-- The truncated weights exhaust the singular weight. -/
theorem iSup_truncationWeight (hu : PlurisubharmonicOn u Ω) (hc : 0 < c)
    {z : ComplexModel d} (hz : z ∈ Ω) :
    multiplierWeight c (u z) = ⨆ k : ℕ, truncationWeight c u k z := by
  refine le_antisymm (multiplierWeight_le_iSup_truncationReal hu hc hz)
    (iSup_le fun k => multiplierWeight_antitone hc.le ?_)
  rw [coe_truncationReal hu k hz]
  exact le_max_left _ _

/-- Each truncated weight is a.e.-measurable on an open subdomain: the truncation is
plurisubharmonic, hence upper semicontinuous, and the weight is a continuous function of
it. -/
theorem aemeasurable_truncationWeight (hu : PlurisubharmonicOn u Ω) (k : ℕ)
    {D : Set (ComplexModel d)} (hDo : IsOpen D) (hDΩ : D ⊆ Ω) :
    AEMeasurable (truncationWeight c u k) (volume.restrict D) := by
  have husc : UpperSemicontinuousOn (fun z => ((truncationReal u k z : ℝ) : EReal)) D :=
    ((truncationReal_plurisubharmonicOn hu k).upperSemicontinuousOn).mono hDΩ
  have h1 : AEMeasurable (fun z => ((truncationReal u k z : ℝ) : EReal))
      (volume.restrict D) :=
    ChartWeightedL2.aemeasurable_restrict_of_upperSemicontinuousOn husc hDo
  have h2 : AEMeasurable (fun z => truncationReal u k z) (volume.restrict D) := by
    simpa using h1.ereal_toReal
  exact ((continuous_multiplierWeight_coe c).measurable).comp_aemeasurable h2

/-- The zeroth truncated weight is locally bounded below by a positive constant: the
truncation `max (u, 0)` is locally bounded above. -/
theorem exists_lower_bound_truncationWeight_zero (hu : PlurisubharmonicOn u Ω)
    (hc : 0 ≤ c) {x : ComplexModel d} (hx : x ∈ Ω) :
    ∃ r > 0, ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∈ ball x r, ENNReal.ofReal δ ≤ truncationWeight c u 0 y := by
  obtain ⟨V, hxV, -, C, hC⟩ := (truncationReal_isLocallyBoundedPshOn hu 0).2 x hx
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.mp (V.isOpen.mem_nhds hxV)
  refine ⟨r, hr, Real.exp (-(c * C)), Real.exp_pos _, fun y hy => ?_⟩
  have hyC : truncationReal u 0 y ≤ C := (abs_le.mp (hC y (hrV hy))).2
  have : -(c * C) ≤ -(c * truncationReal u 0 y) := by
    have := mul_le_mul_of_nonneg_left hyC hc
    linarith
  simpa [truncationWeight, multiplierWeight_coe] using
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr this)

/-- **The Bergman kernel of `e^{-cu}` is the decreasing limit of the kernels of the
truncated weights.**  No smoothness and no boundedness of `u` is assumed: `u` may be
`-∞` on a polar set, which is exactly the situation of Copy-4's `ϕ = m Ψ`. -/
theorem bergmanSup_multiplierWeight_eq_iInf_truncationWeight
    (hu : PlurisubharmonicOn u Ω) (hc : 0 < c)
    {D : Set (ComplexModel d)} (hDo : IsOpen D) (hDΩ : D ⊆ Ω)
    {y : ComplexModel d} (hy : y ∈ D) :
    bergmanSup D (fun z => multiplierWeight c (u z)) y
      = ⨅ k : ℕ, bergmanSup D (truncationWeight c u k) y :=
  bergmanSup_iSup_weight hDo
    (fun _ hz => truncationWeight_monotone hu hc.le (hDΩ hz))
    (fun k => aemeasurable_truncationWeight hu k hDo hDΩ)
    (fun _ hx => exists_lower_bound_truncationWeight_zero hu hc.le (hDΩ hx))
    (fun _ hz => iSup_truncationWeight hu hc (hDΩ hz)) hy

/-- **A comparison uniform in the truncation level passes to the singular weight.**  The
right-hand domain carries the limit; the left-hand one only has to be measurable. -/
theorem bergmanSup_multiplierWeight_le_mul_of_truncationWeight
    (hu : PlurisubharmonicOn u Ω) (hc : 0 < c)
    {D₁ D₂ : Set (ComplexModel d)} (hD₁ : MeasurableSet D₁) (hD₁Ω : D₁ ⊆ Ω)
    (hD₂ : IsOpen D₂) (hD₂Ω : D₂ ⊆ Ω)
    {C : ℝ≥0∞} (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    {y : ComplexModel d} (hy : y ∈ D₂)
    (hcomp : ∀ k : ℕ, bergmanSup D₁ (truncationWeight c u k) y ≤
      C * bergmanSup D₂ (truncationWeight c u k) y) :
    bergmanSup D₁ (fun z => multiplierWeight c (u z)) y ≤
      C * bergmanSup D₂ (fun z => multiplierWeight c (u z)) y :=
  bergmanSup_le_mul_of_iSup_weight hD₁ hD₂
    (fun _ hz => truncationWeight_monotone hu hc.le (hD₂Ω hz))
    (fun k => aemeasurable_truncationWeight hu k hD₂ hD₂Ω)
    (fun _ hx => exists_lower_bound_truncationWeight_zero hu hc.le (hD₂Ω hx))
    (fun _ hz => iSup_truncationWeight hu hc (hD₁Ω hz))
    (fun _ hz => iSup_truncationWeight hu hc (hD₂Ω hz)) hC0 hCtop hy hcomp

end

end Hironaka.QuantitativeRegularizationTruncationLimit
