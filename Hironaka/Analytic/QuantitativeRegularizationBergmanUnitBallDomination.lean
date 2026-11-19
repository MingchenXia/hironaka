import Hironaka.Analytic.QuantitativeRegularizationLocalBergman
import Hironaka.Analytic.UniformLocalBergmanPatch
import Hironaka.Analytic.BergmanSupWeight

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The Bergman weight of a patch is dominated by that patch's own generators

Source: Copy-4, `lem:regularization`, Step 3
(`transcendental-nakamaye-copy4-20260911`); blueprint `ana:regularization`.

Step 4 of the lemma, proved for an **arbitrary** finite family `g` of germs of `𝓘(mφ)`
in `QuantitativeRegularizationMultiplierGermFamily`, ends at the Bergman weight:

> `m⁻¹ · generatorLog g - C ≤ m⁻¹ · bergmanLog B_j (e^{-mΨ})`  near the point.

Step 3, on the other hand, glues the **branches** `bergmanBranch D`, which are built from
the finitely many selected generators of the patch `D`, not from the Bergman weight.  The
two halves therefore only compose once the Bergman weight is bounded *above* by the
patch's own generators.  That is what this module proves, and it is the step that removes
the "the selected generators generate `𝓘(mφ)`" obligation — the one flagged in the
docstring of `QuantitativeRegularizationFiniteGluing` — from the local half of the lemma.
Nothing here needs coherence: the comparison is a pointwise consequence of the uniform
weighted-unit-ball domination already carried by `UniformLocalBergmanPatch`.

The three ingredients, in order:

* `bergmanBall_subset_of_subset` — the weighted unit ball is **antitone** in the domain:
  enlarging the domain both restricts holomorphy and enlarges the mass integral.  Hence
  `bergmanSup` and `bergmanLog` are antitone as well.  This is what lets a bound proved
  for `bergmanUnitBall z R w = bergmanBall (ball z (2R)) w` be used for any Bergman domain
  `B_j ⊇ ball z (2R)`.
* `bergmanLog_le_generatorLog_add_of_domination` — a pointwise domination of the whole
  unit ball by `M · ∑ₗ |gₗ|²` passes to the supremum defining the kernel, and then to its
  logarithm as an additive `log M`.
* `UniformLocalBergmanPatch.exists_const_bergmanLog_le_generatorLog` — the patch form,
  with the constant made positive so that its logarithm is defined.

Only the domination field of the patch is used; no analyticity, no exponent, and no
property of the weight `w` beyond its being a fixed `ℝ≥0∞`-valued function.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace Hironaka.QuantitativeRegularizationBergmanUnitBallDomination

open BergmanSupWeight
open QuasiEquisingularBergmanAtlas

noncomputable section

/-! ### The weighted unit ball is antitone in the domain -/

section Model

variable {d : ℕ} [MeasurableSpace (ComplexModel d)] [BorelSpace (ComplexModel d)]

/-- **Antitonicity of the weighted Bergman unit ball.**  A function holomorphic on the
larger domain with weighted mass at most one there is holomorphic on the smaller one with
weighted mass at most one there. -/
theorem bergmanBall_subset_of_subset {D D' : Set (ComplexModel d)}
    {w : ComplexModel d → ℝ≥0∞} (h : D ⊆ D') :
    bergmanBall D' w ⊆ bergmanBall D w := by
  rintro f ⟨hdiff, hint⟩
  exact ⟨hdiff.mono h, (lintegral_mono_set h).trans hint⟩

/-- Consequently the Bergman kernel on the diagonal is antitone in the domain. -/
theorem bergmanSup_le_of_subset {D D' : Set (ComplexModel d)}
    {w : ComplexModel d → ℝ≥0∞} (h : D ⊆ D') (y : ComplexModel d) :
    bergmanSup D' w y ≤ bergmanSup D w y :=
  bergmanSup_le fun _ hf => le_bergmanSup (bergmanBall_subset_of_subset h hf) y

/-- And so is the Bergman weight. -/
theorem bergmanLog_le_of_subset {D D' : Set (ComplexModel d)}
    {w : ComplexModel d → ℝ≥0∞} (h : D ⊆ D') (y : ComplexModel d) :
    bergmanLog D' w y ≤ bergmanLog D w y :=
  ENNReal.log_monotone (bergmanSup_le_of_subset h y)

/-- The weighted unit ball of `BergmanGenerators` is the Bergman unit ball of the
doubled ball.  This is definitional; it is recorded so that the two namespaces can be
used interchangeably. -/
theorem bergmanUnitBall_eq_bergmanBall (z : ComplexModel d) (R : ℝ)
    (w : ComplexModel d → ℝ≥0∞) :
    BergmanGenerators.bergmanUnitBall z R w = bergmanBall (ball z (2 * R)) w := rfl

/-! ### Domination of the kernel by a finite generator family -/

/-- **A pointwise domination of the unit ball passes to the Bergman kernel.** -/
theorem bergmanSup_le_ofReal_mul_generatorNormSq {D S : Set (ComplexModel d)}
    {w : ComplexModel d → ℝ≥0∞} {N : ℕ} {g : Fin N → ComplexModel d → ℂ}
    {Mc : ℝ}
    (hdom : ∀ f ∈ bergmanBall D w, ∀ y ∈ S, ‖f y‖ ^ 2 ≤ Mc * generatorNormSq g y)
    {y : ComplexModel d} (hy : y ∈ S) :
    bergmanSup D w y ≤ ENNReal.ofReal (Mc * generatorNormSq g y) :=
  bergmanSup_le fun f hf => ENNReal.ofReal_le_ofReal (hdom f hf y hy)

/-- **The Bergman weight is dominated by the logarithmic weight of a dominating family.**

If every member of the weighted unit ball of `D` is bounded on `S` by `Mc` times the
squared norm of the family `g`, then on `S`

> `bergmanLog D w ≤ generatorLog g + log Mc`.

No holomorphy or analyticity of `g` is used. -/
theorem bergmanLog_le_generatorLog_add_of_domination {D S : Set (ComplexModel d)}
    {w : ComplexModel d → ℝ≥0∞} {N : ℕ} {g : Fin N → ComplexModel d → ℂ}
    {Mc : ℝ} (hMc : 0 < Mc)
    (hdom : ∀ f ∈ bergmanBall D w, ∀ y ∈ S, ‖f y‖ ^ 2 ≤ Mc * generatorNormSq g y)
    {y : ComplexModel d} (hy : y ∈ S) :
    bergmanLog D w y ≤ generatorLog g y + (Real.log Mc : EReal) := by
  calc bergmanLog D w y
      ≤ ENNReal.log (ENNReal.ofReal (Mc * generatorNormSq g y)) :=
        ENNReal.log_monotone (bergmanSup_le_ofReal_mul_generatorNormSq hdom hy)
    _ = ENNReal.log (ENNReal.ofReal Mc * ENNReal.ofReal (generatorNormSq g y)) := by
        rw [ENNReal.ofReal_mul hMc.le]
    _ = ENNReal.log (ENNReal.ofReal Mc) +
          ENNReal.log (ENNReal.ofReal (generatorNormSq g y)) := ENNReal.log_mul_add
    _ = generatorLog g y + (Real.log Mc : EReal) := by
        rw [ENNReal.log_ofReal_of_pos hMc, generatorLog_eq_log_sum]
        exact add_comm _ _

end Model

/-! ### The patch form -/

section Patch

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **The Bergman weight of a uniform local Bergman patch is dominated, on the patch
domain, by the patch's own generators.**

The constant is the one already carried by the patch, made positive.  The Bergman domain
`Bj` is arbitrary subject to containing the ball `B(centre, 2·radius)` that the patch's
weighted unit ball integrates over: enlarging the domain only shrinks the unit ball, so
the patch's domination still applies to every competitor.

This is the inequality that composes Step 4 (which ends at `bergmanLog`) with Step 3
(which glues the generator branches), and it needs no statement that the generators
generate the multiplier ideal. -/
theorem UniformLocalBergmanPatch.exists_const_bergmanLog_le_generatorLog
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (D : UniformLocalBergmanPatch θ u m) :
    ∃ A : ℝ, 0 < A ∧ ∀ Bj : Set (ComplexModel n),
      ball D.center (2 * D.radius) ⊆ Bj → ∀ y ∈ D.patch.domain, by
        letI : MeasurableSpace (ComplexModel n) := borel _
        letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
        exact bergmanLog Bj (fun z => multiplierWeight (m : ℝ) (D.weight z)) y
          ≤ generatorLog D.patch.generator y + (Real.log A : EReal) := by
  let _ : MeasurableSpace (ComplexModel n) := borel _
  let _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
  refine ⟨max D.uniform_constant 0 + 1, by linarith [le_max_right D.uniform_constant 0],
    fun Bj hBj y hy => ?_⟩
  set A : ℝ := max D.uniform_constant 0 + 1 with hA
  have hApos : 0 < A := by
    rw [hA]; linarith [le_max_right D.uniform_constant 0]
  have hAle : D.uniform_constant ≤ A := by
    rw [hA]; linarith [le_max_left D.uniform_constant 0]
  have hdom : ∀ f ∈ bergmanBall Bj (fun z => multiplierWeight (m : ℝ) (D.weight z)),
      ∀ z ∈ (D.patch.domain : Set (ComplexModel n)),
        ‖f z‖ ^ 2 ≤ A * generatorNormSq D.patch.generator z := by
    intro f hf z hz
    have hf' : f ∈ BergmanGenerators.bergmanUnitBall D.center D.radius
        (fun x => multiplierWeight (m : ℝ) (D.weight x)) :=
      bergmanBall_subset_of_subset hBj hf
    have hsum : 0 ≤ generatorNormSq D.patch.generator z :=
      generatorNormSq_nonneg _ _
    exact (D.uniform_domination f hf' z hz).trans
      (mul_le_mul_of_nonneg_right hAle hsum)
  exact bergmanLog_le_generatorLog_add_of_domination hApos hdom hy

end Patch

end

end Hironaka.QuantitativeRegularizationBergmanUnitBallDomination
