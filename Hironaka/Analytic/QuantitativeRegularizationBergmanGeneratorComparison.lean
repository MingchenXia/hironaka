import Hironaka.Analytic.QuantitativeRegularizationBergmanLogBranchBound

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# A patch's generators and its Bergman weight agree up to additive constants

Source: Copy-4, `lem:regularization`, Steps 2–3
(`transcendental-nakamaye-copy4-20260911`); blueprint `ana:regularization`.

`QuantitativeRegularizationBergmanUnitBallDomination` proves one inequality: the uniform
weighted unit-ball domination carried by a `UniformLocalBergmanPatch` bounds its Bergman
weight **above** by the patch's own `generatorLog`.  This module proves the other, which is
immediate and needs nothing but the membership of the generators in that unit ball:

> `generatorLog g ≤ bergmanLog D w + log (N + 1)` whenever every `gₗ ∈ bergmanBall D w`,

since `∑ₗ |gₗ(y)|² ≤ N · bergmanSup D w y`.  Applied to a patch (whose generators lie in
`bergmanUnitBall centre radius = bergmanBall (ball centre (2·radius))`) the two inequalities
together say:

> on the patch domain, `generatorLog (patch generators)` and
> `bergmanLog (ball centre (2·radius)) (e^{-m·weight})` differ by a bounded amount.

That is the structural fact the global gluing needs.  The overlap comparison of two Bergman
weights against a common weight is already proved —
`QuantitativeRegularizationBergmanOverlap.bergmanLog_le_add_log_of_pointExtension`, Copy-4
Step 2, with a constant fixed by the cover alone — whereas no such comparison is available
directly for two *generator* families, which are selected independently on each patch.  The
equivalence proved here is what transports Step 2's comparison onto the manifold branches
`bergmanBranch D` that Step 3 actually glues, and hence onto the `Cplus`/`Cminus` data that
`FiniteShiftedBergmanCollarDataOfComparisons` consumes.

Note the two containments are opposite, and both are sharp:

* the **upper** bound (`…BergmanUnitBallDomination`) needs `ball centre (2·radius) ⊆ Bⱼ`, so
  that every competitor for `Bⱼ` is still a competitor for the patch's own ball;
* the **lower** bound here needs `Bⱼ ⊆ ball centre (2·radius)`, so that the patch's
  generators are still competitors for `Bⱼ`.

They meet exactly at `Bⱼ = ball centre (2·radius)`, which is the patch's own Bergman domain.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal BigOperators

namespace Hironaka.QuantitativeRegularizationBergmanGeneratorComparison

open BergmanSupWeight
open DemaillyAnalyticType
open QuasiEquisingularBergmanAtlas
open QuasiEquisingularBergmanBranch
open Hironaka.QuantitativeRegularizationBergmanUnitBallDomination

noncomputable section

/-! ### The model inequality -/

section Model

variable {d : ℕ} [MeasurableSpace (ComplexModel d)] [BorelSpace (ComplexModel d)]

/-- **A finite family inside the weighted unit ball is dominated by the Bergman weight.**

Each member is bounded at `y` by the kernel, so the sum of `N` of them is bounded by
`N · bergmanSup`; `N + 1` is used instead of `N` only so that the additive constant is a
genuine real logarithm also for the empty family. -/
theorem generatorLog_le_bergmanLog_add_of_mem_bergmanBall
    {D : Set (ComplexModel d)} {w : ComplexModel d → ℝ≥0∞} {N : ℕ}
    {g : Fin N → ComplexModel d → ℂ}
    (hg : ∀ l, g l ∈ bergmanBall D w) (y : ComplexModel d) :
    generatorLog g y ≤ bergmanLog D w y + (Real.log ((N : ℝ) + 1) : EReal) := by
  have hNle : (N : ℝ≥0∞) ≤ ENNReal.ofReal ((N : ℝ) + 1) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hsum : ENNReal.ofReal (∑ l, ‖g l y‖ ^ 2)
      ≤ ENNReal.ofReal ((N : ℝ) + 1) * bergmanSup D w y := by
    calc ENNReal.ofReal (∑ l, ‖g l y‖ ^ 2)
        = ∑ l, ENNReal.ofReal (‖g l y‖ ^ 2) :=
          ENNReal.ofReal_sum_of_nonneg (fun l _ => sq_nonneg _)
      _ ≤ ∑ _l : Fin N, bergmanSup D w y :=
          Finset.sum_le_sum fun l _ => le_bergmanSup (hg l) y
      _ = (N : ℝ≥0∞) * bergmanSup D w y := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ENNReal.ofReal ((N : ℝ) + 1) * bergmanSup D w y := by gcongr
  calc generatorLog g y
      = ENNReal.log (ENNReal.ofReal (∑ l, ‖g l y‖ ^ 2)) := generatorLog_eq_log_sum g y
    _ ≤ ENNReal.log (ENNReal.ofReal ((N : ℝ) + 1) * bergmanSup D w y) :=
        ENNReal.log_monotone hsum
    _ = ENNReal.log (ENNReal.ofReal ((N : ℝ) + 1)) + bergmanLog D w y :=
        ENNReal.log_mul_add
    _ = bergmanLog D w y + (Real.log ((N : ℝ) + 1) : EReal) := by
        rw [ENNReal.log_ofReal_of_pos (by positivity)]
        exact add_comm _ _

end Model

/-! ### The patch form, and the branch consequence -/

section Patch

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **A patch's generator weight is below its Bergman weight, up to a constant.**

`Bⱼ` is any Bergman domain *contained* in the ball the patch's weighted unit ball integrates
over, so that the patch's generators are still competitors for `Bⱼ`.  Unlike the companion
upper bound this holds at every point of `ℂⁿ`, not only on the patch domain: no domination
field is used, only the membership of the generators in the unit ball. -/
theorem UniformLocalBergmanPatch.generatorLog_le_bergmanLog_add
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (D : UniformLocalBergmanPatch θ u m)
    (Bj : Set (ComplexModel n)) (hBj : Bj ⊆ ball D.center (2 * D.radius))
    (y : ComplexModel n) : by
      letI : MeasurableSpace (ComplexModel n) := borel _
      letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
      exact generatorLog D.patch.generator y
        ≤ bergmanLog Bj (fun z => multiplierWeight (m : ℝ) (D.weight z)) y
          + (Real.log ((D.patch.N : ℝ) + 1) : EReal) := by
  let _ : MeasurableSpace (ComplexModel n) := borel _
  let _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
  refine generatorLog_le_bergmanLog_add_of_mem_bergmanBall (fun l => ?_) y
  refine bergmanBall_subset_of_subset hBj ?_
  have hl := D.generator_unitBall l
  rwa [bergmanUnitBall_eq_bergmanBall] at hl

/-- **The manifold branch is below the Bergman weight, up to a constant.**

Together with
`QuantitativeRegularizationBergmanLogBranchBound.UniformLocalBergmanPatch.exists_const_bergmanLog_le_bergmanBranch`
(which is the reverse, for a Bergman domain *containing* the patch ball), this says that on a
neighbourhood of any point of a patch source the branch `bergmanBranch D.patch` and
`m⁻¹ · bergmanLog ∘ chart` differ by a bounded amount.  Taking `Bⱼ = ball centre (2·radius)`
makes both available at once. -/
theorem UniformLocalBergmanPatch.exists_const_bergmanBranch_le_bergmanLog
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (D : UniformLocalBergmanPatch θ u m)
    (Bj : Set (ComplexModel n)) (hBj : Bj ⊆ ball D.center (2 * D.radius))
    {x : M} (hx : x ∈ D.patch.source) :
    ∃ C : ℝ, ∀ᶠ y in 𝓝 x, by
      letI : MeasurableSpace (ComplexModel n) := borel _
      letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
      exact bergmanBranch D.patch y
          ≤ (((m : ℝ)⁻¹ : ℝ) : EReal) *
              bergmanLog Bj (fun z => multiplierWeight (m : ℝ) (D.weight z))
                (D.patch.chart.val y) + (C : EReal) := by
  classical
  let _ : MeasurableSpace (ComplexModel n) := borel _
  let _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
  have hbounded : BoundedRealGermAt D.patch.potential (D.patch.chart.val x) :=
    boundedRealGermAt_of_continuousAt
      ((D.patch.localPotential.2.2.1 (D.patch.chart.val x) hx.2).contDiffAt
        (D.patch.localPotential.1.mem_nhds hx.2)).continuousAt
  obtain ⟨Cpot, _hCnonneg, hCpot⟩ := hbounded
  have hminv : (0 : ℝ) ≤ (m : ℝ)⁻¹ := by positivity
  refine ⟨(m : ℝ)⁻¹ * Real.log ((D.patch.N : ℝ) + 1) + Cpot, ?_⟩
  filter_upwards [D.patch.source.isOpen.mem_nhds hx,
    (D.patch.chart.val.continuousAt hx.1) hCpot] with y hy hyC
  set z : ComplexModel n := D.patch.chart.val y with hz
  set B : EReal := (((m : ℝ)⁻¹ : ℝ) : EReal) *
    bergmanLog Bj (fun w => multiplierWeight (m : ℝ) (D.weight w)) z with hB
  have hpot : -Cpot ≤ D.patch.potential z := neg_le_of_abs_le hyC
  have hbranch : bergmanBranch D.patch y =
      (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog D.patch.generator z -
        ((D.patch.potential z : ℝ) : EReal) := by
    rw [bergmanBranch]
    split
    · rfl
    · rename_i hy'
      exact (hy' hy).elim
  -- scale the generator comparison by `m⁻¹`
  have h1 : (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog D.patch.generator z
      ≤ B + (((m : ℝ)⁻¹ * Real.log ((D.patch.N : ℝ) + 1) : ℝ) : EReal) := by
    have hmul := mul_le_mul_of_nonneg_left
      (UniformLocalBergmanPatch.generatorLog_le_bergmanLog_add D Bj hBj z)
      (EReal.coe_nonneg.mpr hminv)
    refine hmul.trans_eq ?_
    rw [EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hminv)
      (EReal.coe_ne_top _), ← EReal.coe_mul, hB]
  rw [hbranch]
  refine (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _))
    (Or.inl (EReal.coe_ne_top _))).2 (h1.trans ?_)
  rw [add_assoc, ← EReal.coe_add]
  have hle : (m : ℝ)⁻¹ * Real.log ((D.patch.N : ℝ) + 1)
      ≤ (m : ℝ)⁻¹ * Real.log ((D.patch.N : ℝ) + 1) + Cpot + D.patch.potential z := by
    linarith
  exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr hle)

end Patch

end

end Hironaka.QuantitativeRegularizationBergmanGeneratorComparison
