/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.GermIdealTotalTransform
import Hironaka.Blowup.BlowupControlledTransform

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.FactorizationFromResolution
open Hironaka Hironaka.HolomorphicIdealSheaves MarkedIdeals BlowupTowers GermIdealTotalTransform BlowupControlledTransform
noncomputable section
variable {n : ℕ} {X : CMfd.{u} n}
/-- The marked ideal `(X, X, E, 𝔞, d)` with the data of `𝔪 = (X, N, E, 𝔞, d)` and `N` replaced by the whole manifold. -/
def ambient (𝔪 : MarkedIdeal n X) : MarkedIdeal n X := { 𝔪 with N := univ }

@[simp] theorem ambient_N (𝔪 : MarkedIdeal n X) : (ambient 𝔪).N = univ := rfl
@[simp] theorem ambient_E (𝔪 : MarkedIdeal n X) : (ambient 𝔪).E = 𝔪.E := rfl
@[simp] theorem ambient_ideal (𝔪 : MarkedIdeal n X) : (ambient 𝔪).ideal = 𝔪.ideal := rfl
@[simp] theorem ambient_d (𝔪 : MarkedIdeal n X) : (ambient 𝔪).d = 𝔪.d := rfl

/-- `𝔞^1 = 𝔞` for a coherent ideal. -/
theorem idealPow_one_of_isCoherent {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) : IdealWeightPowers.idealPow 𝔞 1 = 𝔞 := by
  rw [IdealWeightPowers.idealPow_succ, IdealWeightPowers.idealPow_zero, unitIdeal_mul h𝔞]

end
end Hironaka.FactorizationFromResolution
