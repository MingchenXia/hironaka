/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupTowerTransforms

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.BlowupTowerTransforms
open Hironaka HolomorphicIdealSheaves
open RelativePrincipalizationSpan
noncomputable section
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **A coherent ideal vanishing on `C` lies in `𝓘_C`.** -/
theorem le_vanishingIdeal_of_subset_zeroLocus {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent)
    {C : Set M} (hC : C ⊆ 𝔞.zeroLocus) : 𝔞.Le (vanishingIdeal (n := n) C) := by
  intro x g hg
  refine ⟨GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg, ?_⟩
  obtain ⟨U, hU, hxU, N, s, hs, hgen⟩ := h𝔞 x
  obtain ⟨-, K, t, a, ht, ha, hsum⟩ := (hgen x hxU g).mp hg
  -- near `x`, the same combination exhibits `g` as a germ of `𝔞` at every nearby point
  have hev : ∀ᶠ y in 𝓝 x, y ∈ U ∧ (∀ i, HolomorphicAt n (a i) y) ∧
      HolomorphicAt n g y ∧ g =ᶠ[𝓝 y] fun z => ∑ i, a i z * t i z := by
    filter_upwards [hU.mem_nhds hxU, eventually_all.mpr fun i => (ha i).eventually,
      (GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg).eventually, hsum.eventually_nhds]
      with y hyU hya hyg hysum
    exact ⟨hyU, hya, hyg, hysum⟩
  filter_upwards [hev] with y ⟨hyU, hya, hyg, hysum⟩ hyC
  have hmem : 𝔞.mem y g := (hgen y hyU g).mpr ⟨hyg, K, t, a, ht, hya, hysum⟩
  exact hC hyC g hmem


end
end Hironaka.BlowupTowerTransforms
