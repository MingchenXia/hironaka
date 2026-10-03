/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.HolomorphicAnalytic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.Analytic.Uniqueness
import Hironaka.Manifold.HolomorphicContDiff
set_option autoImplicit false

/-!
# The generic rank of a holomorphic map

Let `G` be holomorphic on a connected open set `U` of a finite-dimensional complex normed space and let the rank of
`dG` attain its maximum `r` at `z₁ ∈ U`.

* `eventually_finrank_range_le`: the rank of a continuous family of linear maps is lower
  semicontinuous (a linearly independent family of images stays independent nearby,
  `LinearIndependent.eventually`).
* `isOpen_maxRank`: `{z ∈ U | rank dG_z = r}` is open.
-/

open Set Filter Topology Module

noncomputable section

namespace Hironaka.HolomorphicGenericRank

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

omit [FiniteDimensional ℂ F] in
/-- **Lower semicontinuity of the rank** of a family of linear maps continuous at `x₀`. -/
theorem eventually_finrank_range_le {X : Type*} [TopologicalSpace X] {A : X → E →L[ℂ] F}
    {x₀ : X} (hA : ContinuousAt A x₀) :
    ∀ᶠ x in 𝓝 x₀, finrank ℂ (LinearMap.range ((A x₀ : E →L[ℂ] F) : E →ₗ[ℂ] F)) ≤
      finrank ℂ (LinearMap.range ((A x : E →L[ℂ] F) : E →ₗ[ℂ] F)) := by
  classical
  set R := LinearMap.range ((A x₀ : E →L[ℂ] F) : E →ₗ[ℂ] F)
  set b := Module.finBasis ℂ R
  have hpre : ∀ i, ∃ v : E, A x₀ v = (b i : F) := fun i => (b i).2
  choose v hv using hpre
  have hli : LinearIndependent ℂ (fun i => A x₀ (v i)) := by
    simp only [hv]
    exact b.linearIndependent.map' R.subtype (Submodule.ker_subtype R)
  have hcont : ContinuousAt (fun x => fun i => A x (v i)) x₀ :=
    continuousAt_pi.2 fun i =>
      ((ContinuousLinearMap.apply ℂ F (v i)).continuous.continuousAt).comp hA
  have hev := hcont.eventually (hli.eventually)
  filter_upwards [hev] with x hx
  have hx' : LinearIndependent ℂ (fun i => (⟨A x (v i), LinearMap.mem_range_self _ _⟩ :
      LinearMap.range ((A x : E →L[ℂ] F) : E →ₗ[ℂ] F))) :=
    LinearIndependent.of_comp (LinearMap.range ((A x : E →L[ℂ] F) : E →ₗ[ℂ] F)).subtype hx
  have := hx'.fintype_card_le_finrank
  simpa [b] using this

/-- **The maximal-rank set is open.** -/
theorem isOpen_maxRank {G : E → F} {U : Set E} (hU : IsOpen U) (hG : DifferentiableOn ℂ G U)
    {r : ℕ}
    (hmax : ∀ z ∈ U, finrank ℂ (LinearMap.range ((fderiv ℂ G z : E →L[ℂ] F) : E →ₗ[ℂ] F)) ≤ r) :
    IsOpen {z ∈ U | finrank ℂ (LinearMap.range ((fderiv ℂ G z : E →L[ℂ] F) : E →ₗ[ℂ] F)) = r} := by
  rw [isOpen_iff_mem_nhds]
  rintro z₀ ⟨hz₀, hr⟩
  have : CompleteSpace F := FiniteDimensional.complete ℂ F
  have hGs := Hironaka.contDiffOn_of_differentiableOn_complex hG hU
  have hfd : ContinuousAt (fderiv ℂ G) z₀ :=
    (hGs.continuousOn_fderiv_of_isOpen hU (by simp)).continuousAt (hU.mem_nhds hz₀)
  filter_upwards [eventually_finrank_range_le hfd, hU.mem_nhds hz₀] with z hz hzU
  exact ⟨hzU, le_antisymm (hmax z hzU) (hr ▸ hz)⟩

end Hironaka.HolomorphicGenericRank
