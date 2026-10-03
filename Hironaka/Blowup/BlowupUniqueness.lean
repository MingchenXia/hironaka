/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The blowup along a smooth centre is unique up to a unique isomorphism over `X`

Source: the universal property recorded in `Hironaka.BlowupSequences.IsBlowupAlong`; this is the standard formal
consequence of it.

`IsBlowupAlong n C π` is stated by a universal property whose test manifolds range over all dimensions in the
universe of the target.
-/

open Set
open scoped Manifold ContDiff

universe u

namespace Hironaka.BlowupUniqueness

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y₁ : Type u} [TopologicalSpace Y₁] [ChartedSpace (ComplexModel n) Y₁]
  [IsComplexManifold n Y₁]
  {Y₂ : Type u} [TopologicalSpace Y₂] [ChartedSpace (ComplexModel n) Y₂]
  [IsComplexManifold n Y₂]

/-- The comparison map supplied by the universal property of the second blowup. -/
theorem existsUnique_comparison {C : Set X} {π₁ : Y₁ → X} {π₂ : Y₂ → X}
    (h₁ : IsBlowupAlong n C π₁) (h₂ : IsBlowupAlong n C π₂) :
    ∃! e : Y₁ → Y₂,
      ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e ∧ π₂ ∘ e = π₁ :=
  h₂.2.2.2.2 n Y₁ π₁ h₁.contMDiff h₁.2.2.2.1

/-- A holomorphic self-map of a blowup commuting with the projection is the identity. -/
theorem eq_id_of_comp_eq {C : Set X} {π : Y₁ → X} (h : IsBlowupAlong n C π) {k : Y₁ → Y₁}
    (hk : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ k) (hcomp : π ∘ k = π) :
    k = id := by
  obtain ⟨k₀, -, huniq⟩ := h.2.2.2.2 n Y₁ π h.contMDiff h.2.2.2.1
  exact (huniq k ⟨hk, hcomp⟩).trans (huniq id ⟨contMDiff_id, rfl⟩).symm

/-- **Two blowups of `X` along the same centre are biholomorphic over `X`.** -/
theorem exists_biholomorphism_over {C : Set X} {π₁ : Y₁ → X} {π₂ : Y₂ → X}
    (h₁ : IsBlowupAlong n C π₁) (h₂ : IsBlowupAlong n C π₂) :
    ∃ e : Y₁ → Y₂, ∃ f : Y₂ → Y₁,
      ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e ∧
      ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f ∧
      π₂ ∘ e = π₁ ∧ π₁ ∘ f = π₂ ∧ f ∘ e = id ∧ e ∘ f = id := by
  obtain ⟨e, ⟨he, hπe⟩, -⟩ := existsUnique_comparison h₁ h₂
  obtain ⟨f, ⟨hf, hπf⟩, -⟩ := existsUnique_comparison h₂ h₁
  refine ⟨e, f, he, hf, hπe, hπf, ?_, ?_⟩
  · refine eq_id_of_comp_eq h₁ (hf.comp he) ?_
    calc π₁ ∘ (f ∘ e) = (π₁ ∘ f) ∘ e := rfl
      _ = π₂ ∘ e := by rw [hπf]
      _ = π₁ := hπe
  · refine eq_id_of_comp_eq h₂ (he.comp hf) ?_
    calc π₂ ∘ (e ∘ f) = (π₂ ∘ e) ∘ f := rfl
      _ = π₁ ∘ f := by rw [hπe]
      _ = π₂ := hπf

end

end Hironaka.BlowupUniqueness
