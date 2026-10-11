/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.PositiveDimensionalComponent

set_option autoImplicit false
namespace Hironaka.PositiveDimensionalComponent
open Hironaka
open Set Filter
open scoped Topology
noncomputable section
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- A preconnected set of `0`-dimensional regular points is a subsingleton. -/
theorem subset_singleton_of_isPreconnected {A G : Set M} (hGA : G ⊆ A)
    (hG : IsPreconnected G) (hreg : ∀ y ∈ G, RegularAtDim (n := n) A y 0) {g : M}
    (hg : g ∈ G) : G ⊆ {g} := by
  obtain ⟨O, hO, hgO, hAO⟩ :=
    exists_isOpen_inter_subset_singleton_of_regularAtDim_zero (hreg g hg)
  have hcover : G ⊆ O ∪ {g}ᶜ := by
    intro z _
    by_cases hzg : z = g
    · exact Or.inl (hzg ▸ hgO)
    · exact Or.inr hzg
  have hdisj : G ∩ (O ∩ {g}ᶜ) = ∅ := by
    refine eq_empty_iff_forall_notMem.mpr ?_
    rintro z ⟨hzG, hzO, hzg⟩
    exact hzg (hAO ⟨hGA hzG, hzO⟩)
  have hGO : G ⊆ O := by
    rcases isPreconnected_iff_subset_of_disjoint.mp hG O {g}ᶜ hO isOpen_compl_singleton
      hcover hdisj with h | h
    · exact h
    · exact absurd (h hg) (by simp)
  exact fun z hz => hAO ⟨hGA hz, hGO hz⟩


end
end Hironaka.PositiveDimensionalComponent
