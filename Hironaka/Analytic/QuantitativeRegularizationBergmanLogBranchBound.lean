import Hironaka.Analytic.QuantitativeRegularizationBergmanUnitBallDomination

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# From the Bergman weight to the manifold branch

Source: Copy-4, `lem:regularization`, Steps 3–4
(`transcendental-nakamaye-copy4-20260911`); blueprint `ana:regularization`.

The local half of the lemma produces, for an arbitrary finite family `g` of germs of
`𝓘(mφ)`, a bound of the shape

> `m⁻¹ · generatorLog g - C ≤ m⁻¹ · bergmanLog B_j (e^{-mΨ})`

(`QuantitativeRegularizationMultiplierGermFamily`,
`QuantitativeRegularizationManifoldGermFamily`).  The global half glues the manifold
branches `bergmanBranch D`, which are built from the *selected* generators of a patch
(`QuantitativeRegularizationFiniteGluing`).  This module closes the gap between the two
right-hand sides: on a neighbourhood of any point of a patch source,

> `m⁻¹ · bergmanLog B_j (e^{-m·D.weight}) ∘ chart - C' ≤ bergmanBranch D.patch`.

Composed with the local half, this is exactly the branch lower bound
`exists_branch_generator_lowerBound` provides for the patch's own generator family, but now
for an **arbitrary** germ family of the multiplier ideal — no statement that the selected
generators generate `𝓘(mφ)` is used anywhere, so the local half needs no coherence input.

Two ingredients only:

* `UniformLocalBergmanPatch.exists_const_bergmanLog_le_generatorLog`
  (`QuantitativeRegularizationBergmanUnitBallDomination`) — the patch's uniform weighted
  unit-ball domination, in logarithmic form, valid on the whole patch domain;
* the smooth local potential `D.patch.potential` is continuous, hence bounded near the
  chart image of the point.  This is the same `BoundedRealGermAt` step that
  `QuantitativeRegularizationLocalBergman.exists_branch_generator_lowerBound` performs, and
  it is what turns the *domain-wide* comparison into the *germwise* one the collar gluing
  consumes.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace Hironaka.QuantitativeRegularizationBergmanLogBranchBound

open BergmanSupWeight
open DemaillyAnalyticType
open QuasiEquisingularBergmanAtlas
open QuasiEquisingularBergmanBranch
open Hironaka.QuantitativeRegularizationBergmanUnitBallDomination

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Subtracting and then adding a real constant is one shift by their difference.  Both
constants are finite, so no `⊥ + ⊤` case arises and the identity holds for every `Y`,
including `Y = ⊥`. -/
theorem sub_coe_add_coe (Y : EReal) (p q : ℝ) :
    Y - (p : EReal) + (q : EReal) = Y + ((-p + q : ℝ) : EReal) := by
  rw [sub_eq_add_neg, ← EReal.coe_neg, add_assoc, ← EReal.coe_add]

/-- **The Bergman weight of a patch is below that patch's branch, up to a constant.**

`B_j` is any Bergman domain containing the ball the patch's weighted unit ball integrates
over; enlarging the domain only shrinks the competitor class, so the patch's own
domination still applies.  The constant collects the patch's uniform domination constant,
scaled by `m⁻¹`, and a bound for the smooth local potential near `x`. -/
theorem UniformLocalBergmanPatch.exists_const_bergmanLog_le_bergmanBranch
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (D : UniformLocalBergmanPatch θ u m)
    (Bj : Set (ComplexModel n)) (hBj : ball D.center (2 * D.radius) ⊆ Bj)
    {x : M} (hx : x ∈ D.patch.source) :
    ∃ C : ℝ, ∀ᶠ y in 𝓝 x, by
      letI : MeasurableSpace (ComplexModel n) := borel _
      letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
      exact (((m : ℝ)⁻¹ : ℝ) : EReal) *
            bergmanLog Bj (fun z => multiplierWeight (m : ℝ) (D.weight z))
              (D.patch.chart.val y) - (C : EReal)
          ≤ bergmanBranch D.patch y := by
  classical
  let _ : MeasurableSpace (ComplexModel n) := borel _
  let _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
  obtain ⟨A, hApos, hA⟩ :=
    QuantitativeRegularizationBergmanUnitBallDomination.UniformLocalBergmanPatch.exists_const_bergmanLog_le_generatorLog D
  have hbounded : BoundedRealGermAt D.patch.potential (D.patch.chart.val x) :=
    boundedRealGermAt_of_continuousAt
      ((D.patch.localPotential.2.2.1 (D.patch.chart.val x) hx.2).contDiffAt
        (D.patch.localPotential.1.mem_nhds hx.2)).continuousAt
  obtain ⟨Cpot, _hCnonneg, hCpot⟩ := hbounded
  have hminv : (0 : ℝ) ≤ (m : ℝ)⁻¹ := by positivity
  refine ⟨(m : ℝ)⁻¹ * Real.log A + Cpot, ?_⟩
  filter_upwards [D.patch.source.isOpen.mem_nhds hx,
    (D.patch.chart.val.continuousAt hx.1) hCpot] with y hy hyC
  set z : ComplexModel n := D.patch.chart.val y with hz
  set X : EReal := (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog D.patch.generator z with hX
  have hyd : z ∈ D.patch.domain := hy.2
  have hpot : D.patch.potential z ≤ Cpot := (le_abs_self _).trans hyC
  -- the branch, evaluated on the patch source
  have hbranch : bergmanBranch D.patch y = X - ((D.patch.potential z : ℝ) : EReal) := by
    rw [bergmanBranch]
    split
    · rfl
    · rename_i hy'
      exact (hy' hy).elim
  -- the domination, multiplied by `m⁻¹`
  have h1 : (((m : ℝ)⁻¹ : ℝ) : EReal) *
        bergmanLog Bj (fun w => multiplierWeight (m : ℝ) (D.weight w)) z
      ≤ X + (((m : ℝ)⁻¹ * Real.log A : ℝ) : EReal) := by
    have hmul := mul_le_mul_of_nonneg_left (hA Bj hBj z hyd)
      (EReal.coe_nonneg.mpr hminv)
    refine hmul.trans_eq ?_
    rw [EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hminv)
      (EReal.coe_ne_top _), ← EReal.coe_mul, hX]
  rw [hbranch]
  refine (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _))
    (Or.inl (EReal.coe_ne_top _))).2 (h1.trans ?_)
  rw [sub_coe_add_coe]
  have hle : (m : ℝ)⁻¹ * Real.log A
      ≤ -D.patch.potential z + ((m : ℝ)⁻¹ * Real.log A + Cpot) := by linarith
  exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr hle)

end

end Hironaka.QuantitativeRegularizationBergmanLogBranchBound
