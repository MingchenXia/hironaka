/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.CodimOneCentre
import Hironaka.MarkedIdeal.MaximalOrderDefinition

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.CodimOneCentre
noncomputable section
open Hironaka HolomorphicIdealSheaves GermIdealOrder MaximalContact
variable {n : ℕ}

/-- **A marked ideal of maximal order has order at most `μ` everywhere**:
`cosupp(𝔞, μ + 1) = ∅` when `D^μ 𝔞 = 𝒪`. -/
theorem notMem_cosupport_succ_of_isMaximalOrder {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] {𝔞 : GermIdeal n M} {μ : ℕ}
    (hmax : IsMaximalOrder 𝔞 μ) (x : M) : x ∉ cosupport n univ 𝔞 (μ + 1) := by
  intro hx
  have h := cosupport_add_subset_cosupport_iterDerivIdeal 𝔞 1 μ (by rwa [Nat.add_comm] at hx)
  have h1 := (vanishesToOrderOn_one_iff (mem_univ x) (holomorphicAt_const 1)).mp (h.2 _ (hmax x))
  exact one_ne_zero h1


end
end Hironaka.CodimOneCentre
