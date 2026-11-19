import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.QuantitativeRegularizationFixedCover

set_option autoImplicit false

/-!
# Demailly's quantitative multiplier-ideal regularization: source boundary

This is the global output of Demailly's Bergman-kernel regularization:
Demailly, *Regularization of closed positive currents and intersection theory*,
J. Algebraic Geom. 1 (1992), Theorem 1.1 and its multiplier-ideal Bergman
construction.  It is also the statement `lem:regularization` in Copy-4
(`transcendental-nakamaye-copy4-20260911`) and blueprint
`ana:regularization`.

The theorem below was a named, source-anchored interface for the global
construction.  It is now proved, following Copy-4's proof of `lem:regularization`:
`QuantitativeRegularizationFixedCover.exists_regularization_multiplierIdeal_lowerBound`
fixes a finite cover by chart balls before the form `ζ`, takes on each ball the
Bergman branch of the corrected weight (`QuantitativeRegularizationChartBranch`),
compares overlapping branches across charts with one constant
(`QuantitativeRegularizationChartOverlap`), and glues them with the plain maximum
(`QuantitativeRegularizationMaxGluing`).  The statement is unchanged; the name
records its source.
-/

open Set Filter
open scoped Topology

namespace Hironaka.QuantitativeRegularization

open Hironaka.PositiveClasses Hironaka.HolomorphicIdealSheaves

noncomputable section

variable {d : ℕ} {Z : Type*} [TopologicalSpace Z]
  [ChartedSpace (ComplexModel d) Z] [IsComplexManifold d Z]

/-- **Demailly 1992, Theorem 1.1**, in the one-sided multiplier-ideal form used by
Copy-4 `lem:regularization`; proved in
`QuantitativeRegularizationFixedCover.exists_regularization_multiplierIdeal_lowerBound`. -/
theorem demailly1992_exists_regularization_multiplierIdeal_lowerBound
    [CompactSpace Z] [ConnectedSpace Z] (omegaZ : KahlerBackground d Z) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (ζ : ClosedRealOneOneForm d Z) (φ : Z → EReal),
        IsThetaPshPotential ζ.val φ →
        ∀ m : ℕ, 1 ≤ m →
          ∃ φm : Z → EReal,
            IsThetaPshPotential (ζ + (c / (m : ℝ)) • omegaZ.form).val φm ∧
            ∀ (x : Z) (N : ℕ) (g : Fin N → Z → ℂ),
              (∀ i, (multiplierIdeal (n := d) (m : ℝ) φ).mem x (g i)) →
              ∃ C : ℝ, ∀ᶠ y in 𝓝 x,
                (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog g y - (C : EReal) ≤ φm y :=
  QuantitativeRegularizationFixedCover.exists_regularization_multiplierIdeal_lowerBound omegaZ

end

end Hironaka.QuantitativeRegularization
