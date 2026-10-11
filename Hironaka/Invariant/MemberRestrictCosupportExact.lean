/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.InvDomainMemberRestriction

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.InvDomainMemberRestriction
open Hironaka MarkedIdeals MarkedIdeals.MarkedIdeal CoefficientIdealRestriction BoundaryCount
variable {n : ℕ} {X : Type u} [TopologicalSpace X]
 [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

theorem cosupp_memberRestrict {𝔪 : MarkedIdeal n X} (h𝔪 : 𝔪.IsWellFormed) (hd : 1 ≤ 𝔪.d)
    (S : Finset (Fin 𝔪.E.length)) : (memberRestrict 𝔪 S).cosupp = 𝔪.cosupp ∩ memberInter 𝔪.E S := by
  have h := CoefficientIdealAlongRestriction.cosupp_coeffMarkedAlong_withN h𝔪.isClosedSubmanifold_N.2
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔪.isCoherent hg) hd
    (S := 𝔪.N ∩ memberInter 𝔪.E S) inter_subset_left
  have h' : (memberRestrict 𝔪 S).cosupp = 𝔪.cosupp ∩ (𝔪.N ∩ memberInter 𝔪.E S) := h
  rw [h']
  ext x
  exact ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, 𝔪.cosupp_subset_N hx.1, hx.2⟩⟩

end Hironaka.InvDomainMemberRestriction
