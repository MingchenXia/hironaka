import Hironaka.Analytic.QuantitativeRegularizationBergmanGeneratorComparison

set_option autoImplicit false

/-!
# Two Borel structures on `ℂᵈ`, one Bergman kernel

`UniformLocalBergmanPatch` declares its measure-theoretic fields (`generator_unitBall`,
`uniform_domination`) under `letI : MeasurableSpace (ComplexModel n) := borel _`.  Every
statement that consumes such a field and still mentions `bergmanBall` / `bergmanSup` /
`bergmanLog` in its **conclusion** therefore carries the `borel (ComplexModel n)` instance,
while a statement elaborated with no such `letI` in scope — for instance everything in
`QuantitativeRegularizationMultiplierGermFamily` and
`QuantitativeRegularizationManifoldGermFamily` — carries the canonical
`WithLp.measurableSpace`.  The two are propositionally equal but not definitionally so, and
an `exact` between them fails.

This is a genuine obstruction to composing the two halves of `lem:regularization`, not a
cosmetic one, and this module removes it once and for all rather than at each call site.

`bergmanBall_congr_instance` and its two consequences say that the Bergman objects do not
depend on which Borel structure is used: `BorelSpace.measurable_eq` identifies each instance
with `borel`, substituting both leaves two proofs of the same proposition, and proof
irrelevance closes the goal by `rfl`.  Nothing here is specific to this project; the same
argument applies to any object defined from `volume` on `ComplexModel d`.

The three patch-level results of
`QuantitativeRegularizationBergmanUnitBallDomination`,
`QuantitativeRegularizationBergmanLogBranchBound` and
`QuantitativeRegularizationBergmanGeneratorComparison` are then restated in whatever
instance the ambient context supplies.  Downstream code should use the `'` forms below; the
original statements are unchanged and are what these are proved from.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace Hironaka.QuantitativeRegularizationBergmanInstanceTransport

open BergmanSupWeight
open QuasiEquisingularBergmanAtlas
open QuasiEquisingularBergmanBranch

noncomputable section

/-! ### The Bergman objects do not depend on the Borel structure -/

/-- Any two Borel measurable structures on `ℂᵈ` give the same weighted Bergman unit ball. -/
theorem bergmanBall_congr_instance {d : ℕ}
    (i₁ : MeasurableSpace (ComplexModel d)) (b₁ : @BorelSpace _ _ i₁)
    (i₂ : MeasurableSpace (ComplexModel d)) (b₂ : @BorelSpace _ _ i₂)
    (D : Set (ComplexModel d)) (w : ComplexModel d → ℝ≥0∞) :
    @bergmanBall d i₁ b₁ D w = @bergmanBall d i₂ b₂ D w := by
  have h₁ : i₁ = borel (ComplexModel d) := b₁.measurable_eq
  have h₂ : i₂ = borel (ComplexModel d) := b₂.measurable_eq
  subst h₁
  subst h₂
  rfl

/-- The same for the kernel on the diagonal. -/
theorem bergmanSup_congr_instance {d : ℕ}
    (i₁ : MeasurableSpace (ComplexModel d)) (b₁ : @BorelSpace _ _ i₁)
    (i₂ : MeasurableSpace (ComplexModel d)) (b₂ : @BorelSpace _ _ i₂)
    (D : Set (ComplexModel d)) (w : ComplexModel d → ℝ≥0∞) (y : ComplexModel d) :
    @bergmanSup d i₁ b₁ D w y = @bergmanSup d i₂ b₂ D w y := by
  have h₁ : i₁ = borel (ComplexModel d) := b₁.measurable_eq
  have h₂ : i₂ = borel (ComplexModel d) := b₂.measurable_eq
  subst h₁
  subst h₂
  rfl

/-- And for the Bergman weight. -/
theorem bergmanLog_congr_instance {d : ℕ}
    (i₁ : MeasurableSpace (ComplexModel d)) (b₁ : @BorelSpace _ _ i₁)
    (i₂ : MeasurableSpace (ComplexModel d)) (b₂ : @BorelSpace _ _ i₂)
    (D : Set (ComplexModel d)) (w : ComplexModel d → ℝ≥0∞) (y : ComplexModel d) :
    @bergmanLog d i₁ b₁ D w y = @bergmanLog d i₂ b₂ D w y := by
  have h₁ : i₁ = borel (ComplexModel d) := b₁.measurable_eq
  have h₂ : i₂ = borel (ComplexModel d) := b₂.measurable_eq
  subst h₁
  subst h₂
  rfl

/-- The rewrite rule used below, oriented so that `rw` on the goal replaces the ambient
Bergman weight by the `borel` one that the patch-side facts carry. -/
theorem bergmanLog_ambient_eq_borel {d : ℕ} [MeasurableSpace (ComplexModel d)]
    [BorelSpace (ComplexModel d)] (D : Set (ComplexModel d))
    (w : ComplexModel d → ℝ≥0∞) (y : ComplexModel d) :
    bergmanLog D w y =
      @bergmanLog d (borel (ComplexModel d))
        (@BorelSpace.mk (ComplexModel d) _ (borel (ComplexModel d)) rfl) D w y :=
  bergmanLog_congr_instance _ _ (borel (ComplexModel d))
    (@BorelSpace.mk (ComplexModel d) _ (borel (ComplexModel d)) rfl) D w y

/-! ### The patch results in the ambient instance -/

section Patch

variable {n : ℕ} [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- `…BergmanUnitBallDomination.UniformLocalBergmanPatch.exists_const_bergmanLog_le_generatorLog`
in the ambient Borel structure. -/
theorem UniformLocalBergmanPatch.exists_const_bergmanLog_le_generatorLog'
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (D : UniformLocalBergmanPatch θ u m) :
    ∃ A : ℝ, 0 < A ∧ ∀ Bj : Set (ComplexModel n),
      ball D.center (2 * D.radius) ⊆ Bj → ∀ y ∈ D.patch.domain,
        bergmanLog Bj (fun z => multiplierWeight (m : ℝ) (D.weight z)) y
          ≤ generatorLog D.patch.generator y + (Real.log A : EReal) := by
  obtain ⟨A, hA, h⟩ :=
    QuantitativeRegularizationBergmanUnitBallDomination.UniformLocalBergmanPatch.exists_const_bergmanLog_le_generatorLog
      D
  refine ⟨A, hA, fun Bj hBj y hy => ?_⟩
  rw [bergmanLog_ambient_eq_borel]
  exact h Bj hBj y hy

/-- `…BergmanGeneratorComparison.UniformLocalBergmanPatch.generatorLog_le_bergmanLog_add`
in the ambient Borel structure. -/
theorem UniformLocalBergmanPatch.generatorLog_le_bergmanLog_add'
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (D : UniformLocalBergmanPatch θ u m)
    (Bj : Set (ComplexModel n)) (hBj : Bj ⊆ ball D.center (2 * D.radius))
    (y : ComplexModel n) :
    generatorLog D.patch.generator y
      ≤ bergmanLog Bj (fun z => multiplierWeight (m : ℝ) (D.weight z)) y
        + (Real.log ((D.patch.N : ℝ) + 1) : EReal) := by
  rw [bergmanLog_ambient_eq_borel]
  exact
    QuantitativeRegularizationBergmanGeneratorComparison.UniformLocalBergmanPatch.generatorLog_le_bergmanLog_add
      D Bj hBj y

/-- `…BergmanLogBranchBound.UniformLocalBergmanPatch.exists_const_bergmanLog_le_bergmanBranch`
in the ambient Borel structure. -/
theorem UniformLocalBergmanPatch.exists_const_bergmanLog_le_bergmanBranch'
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (D : UniformLocalBergmanPatch θ u m)
    (Bj : Set (ComplexModel n)) (hBj : ball D.center (2 * D.radius) ⊆ Bj)
    {x : M} (hx : x ∈ D.patch.source) :
    ∃ C : ℝ, ∀ᶠ y in 𝓝 x,
      (((m : ℝ)⁻¹ : ℝ) : EReal) *
          bergmanLog Bj (fun z => multiplierWeight (m : ℝ) (D.weight z))
            (D.patch.chart.val y) - (C : EReal)
        ≤ bergmanBranch D.patch y := by
  obtain ⟨C, hC⟩ :=
    QuantitativeRegularizationBergmanLogBranchBound.UniformLocalBergmanPatch.exists_const_bergmanLog_le_bergmanBranch
      D Bj hBj hx
  refine ⟨C, ?_⟩
  filter_upwards [hC] with y hy
  rw [bergmanLog_ambient_eq_borel]
  exact hy

/-- `…BergmanGeneratorComparison.UniformLocalBergmanPatch.exists_const_bergmanBranch_le_bergmanLog`
in the ambient Borel structure. -/
theorem UniformLocalBergmanPatch.exists_const_bergmanBranch_le_bergmanLog'
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (D : UniformLocalBergmanPatch θ u m)
    (Bj : Set (ComplexModel n)) (hBj : Bj ⊆ ball D.center (2 * D.radius))
    {x : M} (hx : x ∈ D.patch.source) :
    ∃ C : ℝ, ∀ᶠ y in 𝓝 x,
      bergmanBranch D.patch y
        ≤ (((m : ℝ)⁻¹ : ℝ) : EReal) *
            bergmanLog Bj (fun z => multiplierWeight (m : ℝ) (D.weight z))
              (D.patch.chart.val y) + (C : EReal) := by
  obtain ⟨C, hC⟩ :=
    QuantitativeRegularizationBergmanGeneratorComparison.UniformLocalBergmanPatch.exists_const_bergmanBranch_le_bergmanLog
      D Bj hBj hx
  refine ⟨C, ?_⟩
  filter_upwards [hC] with y hy
  rw [bergmanLog_ambient_eq_borel]
  exact hy

end Patch

end

end Hironaka.QuantitativeRegularizationBergmanInstanceTransport
