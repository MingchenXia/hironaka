/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.OrderTaylorCosupport
import Hironaka.MarkedIdeal.GermIdealOrderBounds

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.OrderInvariance
open Hironaka HolomorphicIdealSheaves
noncomputable section
open GermIdealOrder OrderTaylor
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **Upper semicontinuity of the order** of a coherent ideal (`N = M`): near `x`, `ord_y 𝔞 ≤ ord_x 𝔞`. -/
theorem eventually_order_le {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) (x : M) :
    ∀ᶠ y in 𝓝 x, order n univ 𝔞 y ≤ order n univ 𝔞 x := by
  have hhol : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x := fun x g hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  by_cases htop : order n univ 𝔞 x = ⊤
  · exact Eventually.of_forall fun _ => htop ▸ le_top
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp htop
  have hx : x ∉ cosupport n univ 𝔞 (m + 1) := by
    rintro ⟨-, hx⟩
    have := (le_order_iff (hhol x)).mpr hx
    rw [← hm] at this
    exact absurd (by exact_mod_cast this : m + 1 ≤ m) (Nat.not_succ_le_self m)
  filter_upwards [(isClosed_cosupport h𝔞 (m + 1)).isOpen_compl.mem_nhds hx] with y hy
  rw [← hm]
  by_contra hlt
  have h1 : ((m + 1 : ℕ) : ℕ∞) ≤ order n univ 𝔞 y := by
    have : (m : ℕ∞) < order n univ 𝔞 y := lt_of_not_ge hlt
    exact_mod_cast Order.add_one_le_of_lt this
  exact hy ⟨mem_univ y, (le_order_iff (hhol y)).mp h1⟩

end
end Hironaka.OrderInvariance
