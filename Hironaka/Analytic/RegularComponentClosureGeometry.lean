/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.RegularLocusComponent
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace Hironaka.RegularLocusComponent
open Hironaka RegularLocusDense
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

theorem regularAtDim_closure_component {A : Set M} {c : M} {k : ℕ}
    (hc : RegularAtDim (n := n) A c k) {y : M} (hy : y ∈ component (n := n) A c) :
    RegularAtDim (n := n) (closure (component (n := n) A c)) y k := by
  have hyk := regularAtDim_of_mem_component hc hy
  obtain ⟨W, hW, hyW, hWC, -, hWcl⟩ := exists_isOpen_inter_subset hy hyk
  refine RegularPointDimension.regularAtDim_of_inter_eq hW hyW ?_ hyk
  apply Subset.antisymm
  · exact fun x hx => ⟨subset_closure (hWC hx), hx.2⟩
  · rintro x ⟨hxcl, hxW⟩
    have h1 : x ∈ closure (W ∩ component (n := n) A c) := hW.inter_closure ⟨hxW, hxcl⟩
    have h2 : W ∩ component (n := n) A c ⊆ A ∩ W :=
      fun z hz => ⟨component_subset (n := n) A c hz.2, hz.1⟩
    exact ⟨hWcl ⟨hxW, closure_mono h2 h1⟩, hxW⟩

end Hironaka.RegularLocusComponent
