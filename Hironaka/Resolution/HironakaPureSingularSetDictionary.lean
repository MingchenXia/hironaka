/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaEmbeddedReducible

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaEmbeddedReducible
open Hironaka
noncomputable section
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **For a set of pure dimension `d`, the non-regular set is the set of non-manifold points**: a point of `W` at which `W`
is a submanifold of some dimension `k` has nearby points of `W` regular of dimension `k`, among them a point regular of
dimension `d` (density), so `k = d`. -/
theorem diff_regularLocus_eq_of_pure {W : Set M} {d : ℕ} (hpure : W ⊆ closure (regularLocus (n := n) W d)) :
    W \ regularLocus (n := n) W d = {x | x ∈ W ∧ ∀ k, ¬ RegularAtDim (n := n) W x k} := by
  ext x
  refine ⟨fun hx => ⟨hx.1, fun k hk => hx.2 ?_⟩, fun hx => ⟨hx.1, hx.2 d⟩⟩
  obtain ⟨U, hUev, hUo, hxU⟩ := mem_nhds_iff.mp (RegularPatchNeighborhood.eventually_regularAtDim hk)
  obtain ⟨z, hzU, hzd⟩ := mem_closure_iff.mp (hpure hx.1) U hUo hxU
  have hzk : RegularAtDim (n := n) W z k := hUev hzU hzd.2.1
  have hkd : k = d := RegularPointDimension.eq_of_regularAtDim hzk hzd
  rw [← hkd]
  exact hk


end
end Hironaka.HironakaEmbeddedReducible
