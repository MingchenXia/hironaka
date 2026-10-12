/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.HomogenizedGlueing
import Hironaka.MarkedIdeal.DerivativeIdealCoherence

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology Manifold
namespace Hironaka.HomogenizedGlueing
open Hironaka Hironaka.HolomorphicIdealSheaves GermIdealOrder DerivativeIdeal IdealWeightPowers HomogenizedIdeal
noncomputable section
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] {𝔞 : GermIdeal n M}
/-- **The homogenized ideal of a coherent ideal is coherent.** -/
theorem isCoherent_homogenizedIdeal (h𝔞 : 𝔞.IsCoherent) (μ : ℕ) :
    (homogenizedIdeal 𝔞 μ).IsCoherent := by
  have h : homogenizedIdeal 𝔞 μ = finSumIdeal
      (fun i => (iterDerivIdeal 𝔞 i).mul (idealPow (tangentIdeal 𝔞 μ) i)) μ := rfl
  rw [h]
  exact isCoherent_finSumIdeal (fun i => isCoherent_mul (isCoherent_iterDerivIdeal h𝔞 i)
    (GermIdealPullbackCalculus.isCoherent_idealPow (isCoherent_iterDerivIdeal h𝔞 (μ - 1)) i)) μ

end
end Hironaka.HomogenizedGlueing
