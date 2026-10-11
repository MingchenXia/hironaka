/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.GermIdealOrderValue

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.GermIdealOrder
open Hironaka HolomorphicIdealSheaves
noncomputable section
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] {N : Set M} {x : M} {𝔞 : GermIdeal n M}

/-- **`q ≤ ord_x(𝔞|_N)` iff `ord_x(𝔞|_N) ≥ q`** (for an ideal of holomorphic germs). -/
theorem le_order_iff (h𝔞 : ∀ g, 𝔞.mem x g → HolomorphicAt n g x) {q : ℕ} :
    (q : ℕ∞) ≤ order n N 𝔞 x ↔ OrderGE n N 𝔞 x q := by
  constructor
  · intro hq
    by_contra hnot
    have hlt : ∀ k : ℕ, OrderGE n N 𝔞 x k → k < q := fun k hk => by
      by_contra hkq
      exact hnot (hk.mono (not_lt.mp hkq))
    rcases Nat.eq_zero_or_pos q with rfl | hq0
    · exact hnot (orderGE_zero h𝔞)
    have hle : order n N 𝔞 x ≤ ((q - 1 : ℕ) : ℕ∞) :=
      iSup₂_le fun k hk => by exact_mod_cast Nat.le_sub_one_of_lt (hlt k hk)
    have := hq.trans hle
    have : q ≤ q - 1 := by exact_mod_cast this
    omega
  · intro hq
    exact le_iSup₂ (f := fun (k : ℕ) (_ : OrderGE n N 𝔞 x k) => (k : ℕ∞)) q hq


end
end Hironaka.GermIdealOrder
