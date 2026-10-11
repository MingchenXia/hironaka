/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaDimensionGlobalComponents
import Hironaka.MarkedIdeal.CodimOneSupportAlong

set_option autoImplicit false

/-!
# Actual global analytic extension of a regular order stratum

Blueprint `hironaka-analytic-centre-extension.tex`. Genuine derivative-ideal
analyticity and actual dimension components produce the global extension.
Smoothification of the extension outside the selected open set, and global
noncompact resolution scheduling, remain separate open obligations.
-/

open Set
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaAnalyticCentreExtension

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open HironakaEmbeddedDimensionParts HironakaDimensionGlobalComponents
  AnalyticDimensionBasics GlobalComponents RegularLocusComponent GermIdealOrder

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Actual regularity of one dimension on a trace proves that taking the
corresponding global dimension part preserves that exact trace. -/
theorem dimensionPart_inter_eq_of_regularOn {A U : Set M} (hA : IsClosed A) (q : ℕ)
    (hreg : ∀ x ∈ A, x ∈ U → RegularAtDim (n := n) A x q) :
    dimensionPart (n := n) A q ∩ U = A ∩ U := by
  apply Subset.antisymm
  · rintro x ⟨hx, hxU⟩
    exact ⟨dimensionPart_subset (n := n) hA q hx, hxU⟩
  · rintro x ⟨hxA, hxU⟩
    exact ⟨subset_closure (hreg x hxA hxU), hxU⟩

/-- The actual order superlevel produces its genuine global pure-dimensional
analytic extension, its exact regular trace, and its real component dictionary. -/
theorem exists_pure_global_extension_of_regular_order_superlevel
    (𝔞 : GermIdeal n M) (h𝔞 : 𝔞.IsCoherent) (N : Set M)
    (hN : IsClosedSubmanifold n N) (μ : ℕ) (hμ : 1 ≤ μ) (q : ℕ)
    (U : Set M) (_hU : IsOpen U)
    (hreg : ∀ x ∈ cosupport n N 𝔞 μ, x ∈ U →
      RegularAtDim (n := n) (cosupport n N 𝔞 μ) x q) :
    ∃ T : Set M, IsComplexAnalyticSubset (n := n) T ∧
      IsPureDim (n := n) T q ∧ T ⊆ cosupport n N 𝔞 μ ∧
      T ∩ U = cosupport n N 𝔞 μ ∩ U ∧
      (∀ x ∈ T, x ∈ U → RegularAtDim (n := n) T x q) ∧
      T = ⋃₀ {B | B ∈ globalComponents (n := n) (cosupport n N 𝔞 μ) ∧
        IsPureDim (n := n) B q} := by
  have hA := CodimOneSupportAlong.isComplexAnalyticSubset_cosupport_along h𝔞 hN hμ
  refine ⟨dimensionPart (n := n) (cosupport n N 𝔞 μ) q,
    isComplexAnalyticSubset_dimensionPart hA q,
    HironakaDimensionGlobalComponents.isPureDim_dimensionPart hA q,
    dimensionPart_subset hA.isClosed q,
    dimensionPart_inter_eq_of_regularOn hA.isClosed q hreg, ?_,
    dimensionPart_eq_sUnion_globalComponents hA q⟩
  intro x hxT hxU
  exact regularAtDim_dimensionPart_of_regularAtDim hA.isClosed
    (hreg x (dimensionPart_subset hA.isClosed q hxT) hxU)

end

end Hironaka.HironakaAnalyticCentreExtension
