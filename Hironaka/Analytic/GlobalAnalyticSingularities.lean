import Hironaka.Analytic.HolomorphicIdealSheaves

set_option autoImplicit false

/-!
# Analytic singularities of type `(c, 𝔞)`

Source: Copy-4, `sec:prelim` (the paragraph defining analytic singularities) and
`sec:nK` (`transcendental-nakamaye-copy4-20260911`).

New definition of this first pass (recorded in the blueprint,
`ana:ideal-sheaves`):

* `HasAnalyticSingularitiesOfType φ c 𝔞`: the manuscript's convention, following
  XiaSGPT, Definition 1.6.1.  Here `c` is a positive rational, `𝔞 ⊆ 𝒪_M` is a
  coherent ideal sheaf, and locally `φ = c ψ_𝔞 + R` with `R` merely bounded, where
  `ψ_𝔞 = log ∑ |gᵢ|²` for local generators `gᵢ` of `𝔞`.  Different generator
  families change `ψ_𝔞` by a bounded amount, so it suffices that the identity
  holds for one family of generators near each point.

Unlike `NumericalRestrictedVolumeScaffold.HasManifoldSmoothAnalyticSingularities`
(the CT22 convention with a real coefficient and a smooth remainder, varying from
chart to chart), the coefficient and the ideal here are global and the remainder
is only bounded.  Quasi-plurisubharmonicity is not part of the definition.
-/

open Set
open scoped Manifold

namespace Hironaka.GlobalAnalyticSingularities

noncomputable section

open HolomorphicIdealSheaves

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- `φ` has analytic singularities of type `(c, 𝔞)`: `c ∈ ℚ_{>0}`, `𝔞` coherent,
and near every point `φ = c log ∑ |gᵢ|² + R` for holomorphic generators `gᵢ` of
`𝔞` and a bounded real remainder `R`. -/
def HasAnalyticSingularitiesOfType (φ : M → EReal) (c : ℚ) (𝔞 : GermIdeal n M) :
    Prop :=
  0 < c ∧ 𝔞.IsCoherent ∧
    ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ (N : ℕ) (g : Fin N → M → ℂ),
      (∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (g i) U) ∧
      (∀ y ∈ U, ∀ h, 𝔞.mem y h ↔ IsInSpanAt (n := n) (· ∈ range g) y h) ∧
      ∃ (R : M → ℝ) (C : ℝ), (∀ y ∈ U, |R y| ≤ C) ∧
        ∀ y ∈ U, φ y = ((c : ℝ) : EReal) * generatorLog g y + (R y : EReal)

/-- `φ` has analytic singularities of some type. -/
def HasAnalyticSingularities (φ : M → EReal) : Prop :=
  ∃ (c : ℚ) (𝔞 : GermIdeal n M), HasAnalyticSingularitiesOfType φ c 𝔞

end

end Hironaka.GlobalAnalyticSingularities
