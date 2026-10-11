/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.CompanionReduction
import Hironaka.Invariant.OrderTaylorCosupport
import Hironaka.MarkedIdeal.MaximalOrderDefinition

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.CompanionReduction
noncomputable section
open Hironaka HolomorphicIdealSheaves GermIdealOrder DerivativeIdeal OrderTaylor
variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Outside the zero locus of a coherent ideal: a germ nonvanishing at the point. -/
theorem exists_mem_ne_zero_of_notMem_zeroLocus {Z : Type*} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel n) Z] {J : GermIdeal n Z} {y : Z}
    (hy : y ∉ J.zeroLocus) : ∃ g, J.mem y g ∧ g y ≠ 0 := by
  by_contra! h
  exact hy h


/-- A coherent ideal with a germ nonvanishing at `x` contains the unit germ at `x`. -/
theorem one_mem_of_apply_ne_zero {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) {x : M} {g : M → ℂ}
    (hg : 𝔞.mem x g) (hgx : g x ≠ 0) : 𝔞.mem x (fun _ => 1) := by
  have hgh : HolomorphicAt n g x := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  refine GermIdealTotalTransform.mem_of_isInSpanAt_mem h𝔞
    (HolomorphicIdealSheaves.isInSpanAt_of_eq_mul hg (holomorphicAt_const 1)
      (RelativePrincipalizationSpan.holomorphicAt_inv hgh hgx) ?_)
  filter_upwards [hgh.continuousAt.eventually (isOpen_ne.mem_nhds hgx)] with y hy
  exact (inv_mul_cancel₀ hy).symm

/-- **Maximal order from orders**: if `ord_x 𝔞 ≤ μ` at every point (`x ∉ cosupp(𝔞, μ + 1)`), then `(𝔞, μ)` is of maximal
order in TN23's sense (`𝓓^μ 𝔞 = 𝒪`). -/
theorem isMaximalOrder_of_forall_notMem {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) {μ : ℕ}
    (h : ∀ x, x ∉ cosupport n univ 𝔞 (μ + 1)) : MaximalContact.IsMaximalOrder 𝔞 μ := by
  intro x
  have hhol : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  have hx := h x
  rw [cosupport_succ_eq_zeroLocus_iterDerivIdeal hhol] at hx
  obtain ⟨g, hg, hgx⟩ := exists_mem_ne_zero_of_notMem_zeroLocus hx
  exact one_mem_of_apply_ne_zero (isCoherent_iterDerivIdeal h𝔞 μ) hg hgx


end
end Hironaka.CompanionReduction
