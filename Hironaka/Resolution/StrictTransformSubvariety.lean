/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.ExceptionalImageCodimension
import Hironaka.Analytic.PureDimension
import Hironaka.Analytic.AnalyticSubsetPreimage
import Hironaka.Analytic.RegularAtDimTransport
import Hironaka.Analytic.ComponentComplementConnected
import Hironaka.Analytic.AnalyticIrreducibleComponents
import Hironaka.Analytic.AnalyticSubsetTopology
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.ClosureDifferenceAnalytic
import Hironaka.Analytic.RegularLocusComponent
set_option autoImplicit false

/-!
# The strict transform of a subvariety under one blowup

Source: CT22, Section 4; Griffiths--Harris, Ch. 1 §4.

Let `g : Z → Y` be the blowup of a compact complex manifold along a smooth centre, `T` the
image of its exceptional locus, and `W ⊆ Y` a closed irreducible analytic subvariety with
`W ⊄ T`.  Then the strict transform `W̃ = closure (g⁻¹ W \ Exc g)` is a closed irreducible
analytic subvariety with `dim W̃ = dim W`.

* Analyticity: `Exc g = g⁻¹ T` (`ExceptionalFibres`), so `W̃ = closure (g⁻¹ W \ g⁻¹ T)`
  is the closure of a difference of analytic sets.
* Dimension: pick a regular point `c ∉ T` of `W` of dimension `dim W`; its unique preimage
  `c̃` is not exceptional, `W̃` agrees with `g⁻¹ W` off `Exc g`, and regularity transports
  across the local biholomorphism.
* Irreducibility: `W` is the closure of the connected component `K` of its regular locus
  through `c` (`eq_closure_component`); `K \ T` is connected and dense in `K`
  (`ComponentComplementConnected`); since `g` restricted to `Z \ Exc g` is an injective
  open map, `g⁻¹ (K \ T)` is a connected set of regular points of `W̃`, hence lies in the component `K̃` through `c̃`, and it is dense in `W̃`. So `W̃ = closure K̃` is irreducible.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.StrictTransformSubvariety

open Hironaka.BlowupSequences RegularLocusComponent

noncomputable section

section Irreducible

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- An irreducible analytic set is the closure of the component of its regular locus through
any regular point. -/
theorem eq_closure_component {A : Set M} (hA : IsComplexAnalyticallyIrreducible (n := n) A)
    {c : M} {k : ℕ} (hc : RegularAtDim (n := n) A c k) :
    A = closure (component (n := n) A c) := by
  have hK := isComplexAnalyticSubset_closure_component hA.analytic hc
  have hS := ClosureDifferenceAnalytic.isComplexAnalyticSubset_closure_diff hA.analytic hK
  have hKA : closure (component (n := n) A c) ⊆ A :=
    closure_minimal (component_subset (n := n) A c) hA.analytic.isClosed
  have hSA : closure (A \ closure (component (n := n) A c)) ⊆ A :=
    closure_minimal sdiff_subset hA.analytic.isClosed
  have hunion : A = closure (component (n := n) A c) ∪
      closure (A \ closure (component (n := n) A c)) := by
    refine Subset.antisymm (fun x hx => ?_) (union_subset hKA hSA)
    by_cases hxK : x ∈ closure (component (n := n) A c)
    · exact Or.inl hxK
    · exact Or.inr (subset_closure ⟨hx, hxK⟩)
  rcases hA.eq_left_or_eq_right hK hS hKA hSA hunion with h | h
  · exact h
  · exfalso
    obtain ⟨W, hW, hcW, hWK⟩ := exists_open_inter_subset_component hc (mem_component_self hc)
    have hc' : c ∈ closure (A \ closure (component (n := n) A c)) := h ▸ hc.2.1
    obtain ⟨x, hxW, hxA, hxK⟩ := mem_closure_iff.mp hc' W hW hcW
    exact hxK (subset_closure (hWK ⟨hxA, hxW⟩))

end Irreducible

end

end Hironaka.StrictTransformSubvariety
