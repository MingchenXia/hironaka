/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.HolomorphicIdealSheaves
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Hironaka.Manifold.ComplexManifold
set_option autoImplicit false

/-!
# Holomorphy read in a chart

A function that is holomorphic on a set `U` of a complex manifold is complex differentiable, read in the preferred
chart at any point, on the part of the chart target lying over `U`.

Declarations:
* `differentiableOn_comp_chartSymm`
-/

open Set
open scoped Manifold ContDiff

namespace Hironaka

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Manifold holomorphy on `U`, read in the preferred chart at `x`, is ordinary
complex differentiability on the part of the chart target lying over `U`. -/
theorem differentiableOn_comp_chartSymm (x : M) {f : M → ℂ} {U : Set M}
    (hf : MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) f U) :
    DifferentiableOn ℂ (fun z => f ((complexChartAt (n := n) x).val.symm z))
      ((complexChartAt (n := n) x).val.target ∩
        (complexChartAt (n := n) x).val.symm ⁻¹' U) := by
  rw [← mdifferentiableOn_iff_differentiableOn]
  have hsymm : MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
      (chartAt (ComplexModel n) x).symm (chartAt (ComplexModel n) x).target :=
    (contMDiffOn_chart_symm (I := 𝓘(ℂ, ComplexModel n)) (n := ∞) (x := x)).mdifferentiableOn
      (by simp)
  exact hf.comp (hsymm.mono inter_subset_left) (fun z hz => hz.2)

end

end Hironaka
