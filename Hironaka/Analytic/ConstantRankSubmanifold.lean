/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.HolomorphicConstantRank
import Hironaka.Analytic.RegularLocusDense
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Hironaka.Manifold.HolomorphicContDiff
set_option autoImplicit false

/-!
# Constant-rank images are submanifolds

* `image_mem_nhds_of_range_eq_top`: if `dG_p` is onto, `G` maps every neighbourhood of `p` onto a neighbourhood of
  `G p`.
-/

open Set Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace Hironaka.ConstantRankSubmanifold

open Hironaka.RegularLocusDense HolomorphicConstantRank

variable {N : ℕ} {R : Type*} [NormedAddCommGroup R] [NormedSpace ℂ R] [FiniteDimensional ℂ R]

/-! ### Images of constant-rank maps -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- **Submersions are open at a point** (the case `rank = dim F` of
`rem:constant-rank-submanifold`): if `dG_p` is onto, `G` maps every neighbourhood of `p` onto a
neighbourhood of `G p`. -/
theorem image_mem_nhds_of_range_eq_top {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [FiniteDimensional ℂ F] {G : E → F} {U : Set E} (hU : IsOpen U) (hG : DifferentiableOn ℂ G U)
    {p : E} (hp : p ∈ U) (hsurj : LinearMap.range ((fderiv ℂ G p : E →L[ℂ] F) : E →ₗ[ℂ] F) = ⊤)
    {O : Set E} (hO : O ∈ 𝓝 p) : G '' O ∈ 𝓝 (G p) := by
  have : CompleteSpace E := FiniteDimensional.complete ℂ E
  have : CompleteSpace F := FiniteDimensional.complete ℂ F
  have hGs : ContDiffOn ℂ ∞ G U := Hironaka.contDiffOn_of_differentiableOn_complex hG hU
  have hstrict : HasStrictFDerivAt G (fderiv ℂ G p) p :=
    (hGs.contDiffAt (hU.mem_nhds hp)).hasStrictFDerivAt (by simp)
  rw [← hstrict.map_nhds_eq_of_surj hsurj]
  exact image_mem_map hO

/-- The rank form of `image_mem_nhds_of_range_eq_top`: rank `dim F` at `p`. -/
theorem image_mem_nhds_of_finrank_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [FiniteDimensional ℂ F] {G : E → F} {U : Set E} (hU : IsOpen U) (hG : DifferentiableOn ℂ G U)
    {p : E} (hp : p ∈ U)
    (hrank : Module.finrank ℂ (LinearMap.range ((fderiv ℂ G p : E →L[ℂ] F) : E →ₗ[ℂ] F)) =
      Module.finrank ℂ F)
    {O : Set E} (hO : O ∈ 𝓝 p) : G '' O ∈ 𝓝 (G p) :=
  image_mem_nhds_of_range_eq_top hU hG hp (Submodule.eq_top_of_finrank_eq hrank) hO

end Hironaka.ConstantRankSubmanifold
