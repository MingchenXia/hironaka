/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.AnalyticSubsetOpens

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.AnalyticSubsetOpens
open Hironaka
noncomputable section
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {U : Opens M}

/-- A map holomorphic on the open set `U` is holomorphic on the manifold `U`. -/
theorem contMDiff_restrict {m : ℕ} {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel m) Y] {f : M → Y}
    (hf : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f U) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ (fun x : U => f x) := fun x =>
  contMDiffAt_subtype_iff.mpr ((hf x x.2).contMDiffAt (U.isOpen.mem_nhds x.2))


end
end Hironaka.AnalyticSubsetOpens
