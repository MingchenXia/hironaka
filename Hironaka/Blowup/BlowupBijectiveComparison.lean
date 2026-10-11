/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupUniqueness

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.BlowupUniqueness
open Hironaka HolomorphicIdealSheaves
noncomputable section
open BlowupSequences
universe u
variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] {Y₁ : Type u} [TopologicalSpace Y₁] [ChartedSpace (ComplexModel n) Y₁] [IsComplexManifold n Y₁] {Y₂ : Type u} [TopologicalSpace Y₂] [ChartedSpace (ComplexModel n) Y₂] [IsComplexManifold n Y₂]

/-- The comparison map is a bijection. -/
theorem bijective_comparison {C : Set X} {π₁ : Y₁ → X} {π₂ : Y₂ → X}
    (h₁ : IsBlowupAlong n C π₁) (h₂ : IsBlowupAlong n C π₂) :
    ∃ e : Y₁ → Y₂, Function.Bijective e ∧
      ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e ∧ π₂ ∘ e = π₁ := by
  obtain ⟨e, f, he, -, hπe, -, hfe, hef⟩ := exists_biholomorphism_over h₁ h₂
  exact ⟨e, Function.bijective_iff_has_inverse.mpr
    ⟨f, congrFun hfe, congrFun hef⟩, he, hπe⟩

end
end Hironaka.BlowupUniqueness
