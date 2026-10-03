/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Manifold.HolomorphicMaps
import Hironaka.Manifold.ComplexManifold
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Normed.Module.ContinuousInverse
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Hironaka.Resolution.StrictTransformComposition
import Hironaka.Blowup.BlowupSequences
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Non-vanishing under composition with a holomorphic map

A function that vanishes identically on no nonempty open subset of `U` vanishes identically on no nonempty open
subset of `g⁻¹ U` after composition with a holomorphic map `g` whose exceptional locus has empty interior.

Declarations:
* `exists_ne_zero_comp`
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.MeteredDivisorOperations

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences Hironaka.HolomorphicMaps

noncomputable section

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

variable {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z]

/-- A function vanishing on no nonempty open subset of `U` composes with a holomorphic map whose
exceptional locus has empty interior to one vanishing on no nonempty open subset of `g⁻¹ U`. -/
theorem exists_ne_zero_comp {g : Z → M}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    (hint : interior (exceptionalLocus n g) = ∅) {U : Set M} {f : M → ℂ}
    (hf : ∀ W : Set M, IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, f y ≠ 0)
    {W : Set Z} (hW : IsOpen W) (hWU : W ⊆ g ⁻¹' U) (hne : W.Nonempty) :
    ∃ z ∈ W, f (g z) ≠ 0 := by
  have hnot : ¬ W ⊆ exceptionalLocus n g := fun hsub => by
    obtain ⟨z, hz⟩ := hne
    have := interior_maximal hsub hW hz
    rw [hint] at this
    exact this
  obtain ⟨z₀, hz₀W, hz₀E⟩ := not_subset.mp hnot
  have himg : g '' W ∈ 𝓝 (g z₀) := by
    rw [← StrictTransformComposition.map_nhds_eq_of_not_mem_exceptionalLocus hg hz₀E]
    exact image_mem_map (hW.mem_nhds hz₀W)
  obtain ⟨y, hyi, hy⟩ := hf (interior (g '' W)) isOpen_interior
    (interior_subset.trans (image_subset_iff.mpr hWU)) ⟨_, mem_interior_iff_mem_nhds.mpr himg⟩
  obtain ⟨z, hzW, rfl⟩ := interior_subset hyi
  exact ⟨z, hzW, hy⟩

end

end Hironaka.MeteredDivisorOperations
