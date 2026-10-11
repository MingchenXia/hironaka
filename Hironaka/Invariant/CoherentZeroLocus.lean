/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.OrderTaylor

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.OrderTaylor
open Hironaka HolomorphicIdealSheaves
open RelativePrincipalizationSpan
noncomputable section
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The zero locus of a coherent ideal is closed. -/
theorem isClosed_zeroLocus_of_isCoherent {𝔟 : GermIdeal n M} (h𝔟 : 𝔟.IsCoherent) :
    IsClosed 𝔟.zeroLocus := by
  refine isOpen_compl_iff.mp (isOpen_iff_mem_nhds.mpr fun x hx => ?_)
  obtain ⟨g, hg, hgx⟩ : ∃ g, 𝔟.mem x g ∧ g x ≠ 0 := by
    by_contra! h
    exact hx h
  obtain ⟨U, hUo, hxU, N, s, hs, hgen⟩ := h𝔟 x
  obtain ⟨-, K, t, a, ht, -, hsum⟩ := (hgen x hxU g).mp hg
  obtain ⟨i, hi⟩ : ∃ i, t i x ≠ 0 := by
    by_contra! h
    exact hgx (by rw [hsum.self_of_nhds]; simp [h])
  obtain ⟨r, hr⟩ := ht i
  have hshol : ∀ z ∈ U, HolomorphicAt n (s r) z := fun z hz =>
    eventually_of_mem (hUo.mem_nhds hz) fun w hw => (hs r w hw).mdifferentiableAt (hUo.mem_nhds hw)
  have hne : ∀ᶠ y in 𝓝 x, s r y ≠ 0 :=
    (hshol x hxU).continuousAt.eventually (isOpen_ne.mem_nhds (hr ▸ hi))
  filter_upwards [hUo.mem_nhds hxU, hne] with y hyU hy hyV
  refine hy (hyV (s r) ((hgen y hyU (s r)).mpr ?_))
  exact isInSpanAt_of_eq_mul ⟨r, rfl⟩ (hshol y hyU) (holomorphicAt_const 1)
    (Eventually.of_forall fun _ => (one_mul _).symm)


end
end Hironaka.OrderTaylor
