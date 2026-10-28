/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.MarkedIdeal.CodimOneSupportAlong

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.CodimOneSupportAlong

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder
  RelativePrincipalizationSpan MarkedIdeals CodimOneSupport TangentDirectionAlong GiraudAlong
  HomogenizedIdealAlong AnalyticDimensionBasics RegularPointDimension DerivativeIdealAlongCoherent
  CodimOneCentreAlong TransformOffCentre DerivativeIdealAlong

noncomputable section

variable {n : ℕ}

section Support

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {N : Set M} {𝔞 : GermIdeal n M} {μ : ℕ}

/-- **Near a point of the codimension-one part along `N`, the support is `N ∩ V(u)` for any tangent
direction `u` along `N`.** -/
theorem eventually_mem_codimOnePartAlong_iff_eq_zero (h𝔞 : 𝔞.IsCoherent)
    (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ) {U : Set M} {u : M → ℂ}
    (hu : IsTangentDirectionAlong N 𝔞 μ U u) {x : M} (hxU : x ∈ U)
    (hx : x ∈ codimOnePartAlong N 𝔞 μ) :
    ∀ᶠ y in 𝓝 x, y ∈ codimOnePartAlong N 𝔞 μ ↔ y ∈ N ∧ u y = 0 := by
  obtain ⟨k, hNk, hS⟩ := hx
  filter_upwards [eventually_mem_codimOnePartAlong_iff ⟨k, hNk, hS⟩,
    eventually_mem_iff_of_locDimGE_along h𝔞 hN hμ (isComplexAnalyticSubset_cosupport_along h𝔞 hN hμ)
      subset_rfl hu hxU hNk (locDimGE_of_regularAtDim hS)] with y h1 h2
  rw [h1, h2]

end Support

end

end Hironaka.CodimOneSupportAlong
