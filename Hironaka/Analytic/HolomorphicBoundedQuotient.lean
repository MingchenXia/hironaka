/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.RiemannExtension
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Manifold.ComplexManifold
set_option autoImplicit false

/-!
# A bounded holomorphic quotient is holomorphic

Source: Demailly CADG II.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HolomorphicBoundedQuotient

noncomputable section

open Hironaka.HolomorphicIdealSheaves

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-! ### The preferred chart, recentred at the origin -/

theorem mdifferentiableAt_chartAt {x y : M} (hy : y ∈ (chartAt (ComplexModel n) x).source) :
    MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
      (chartAt (ComplexModel n) x) y :=
  ((contMDiffOn_chart (n := ∞)).contMDiffAt
    ((chartAt (ComplexModel n) x).open_source.mem_nhds hy)).mdifferentiableAt (by simp)

theorem mdifferentiableAt_chartAt_symm {x : M} {z : ComplexModel n}
    (hz : z ∈ (chartAt (ComplexModel n) x).target) :
    MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
      (chartAt (ComplexModel n) x).symm z :=
  ((contMDiffOn_chart_symm (n := ∞)).contMDiffAt
    ((chartAt (ComplexModel n) x).open_target.mem_nhds hz)).mdifferentiableAt (by simp)

end

end Hironaka.HolomorphicBoundedQuotient
