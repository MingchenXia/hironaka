import Hironaka.Analytic.QuantitativeRegularizationInterface

set_option autoImplicit false

/-!
# Quantitative regularization with a one-sided ideal bound

Source: Copy-4, `lem:regularization` (`transcendental-nakamaye-copy4-20260911`);
blueprint `ana:regularization`.

For a connected compact Kähler manifold `(Z, ω_Z)` there is `c > 0`, depending
only on `(Z, ω_Z)`, such that for every smooth closed real `(1,1)`-form `ζ`,
every `φ ∈ PSH(Z, ζ)` and every integer `m ≥ 1` there is a quasi-psh `φ_m` with

* `ζ + ddᶜ φ_m ≥ -(c/m) ω_Z`, and
* locally `φ_m ≥ m⁻¹ ψ_{𝓘(mφ)} + O(1)`.

The first-pass encoding of the second inequality: for every point `x` and every
finite family `g` of germs of `𝓘(mφ)` at `x`, `φ_m ≥ m⁻¹ log ∑ |gᵢ|² - C` near `x`.
Taking `g` to be local generators gives the manuscript's inequality (Nadel
coherence of `𝓘(mφ)` supplies them), and conversely every finite family of
germs of the stalk is a holomorphic combination of the generators, so its
`log ∑ |gᵢ|²` is bounded above by `ψ_{𝓘(mφ)} + O(1)`.  The quasi-psh function
`φ_m` with the lower curvature bound is `IsThetaPshPotential (ζ + (c/m) ω_Z) φ_m`,
which includes local nondegeneracy.  The quantifier order is `∃ c, ∀ ζ φ m, ∃ φ_m`.

The statement is `Hironaka.QuantitativeRegularizationInterface`'s theorem, which is
proved in `Hironaka.QuantitativeRegularizationFixedCover` (fixed cover, chart Bergman
branches, cross-chart overlap, maximum gluing).
-/

open Set Filter
open scoped Topology

namespace Hironaka.QuantitativeRegularization

open Hironaka.PositiveClasses Hironaka.HolomorphicIdealSheaves

noncomputable section

variable {d : ℕ} {Z : Type*} [TopologicalSpace Z]
  [ChartedSpace (ComplexModel d) Z] [IsComplexManifold d Z]

/-- **Quantitative regularization with a one-sided ideal bound**
(Copy-4, `lem:regularization`), as a wrapper around Demailly's global
source-boundary theorem. -/
theorem exists_regularization_multiplierIdeal_lowerBound
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
  demailly1992_exists_regularization_multiplierIdeal_lowerBound omegaZ

end

end Hironaka.QuantitativeRegularization
