/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.MarkedIdeal.CoefficientAmbientMarkedDataExact
import Hironaka.Invariant.CompanionMaximalOrder
import Hironaka.Support.ZeroCoordinateDerivativeUnivExact

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HomogenizedIdealAlong
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences Hironaka.GermIdealOrder Hironaka.DerivativeIdeal Hironaka.DerivativeIdealAlong Hironaka.GiraudAlong Hironaka.TangentDirectionAlong Hironaka.IdealWeightPowers Hironaka.MarkedIdeals Hironaka.DerivativeIdealTower Hironaka.CoefficientIdeal Hironaka.HomogenizedGlueing Hironaka.HomogenizedEquivalence Hironaka.HomogenizedEtale Hironaka.MarkedIdealBiholomorphism Hironaka.GermIdealPullbackCalculus Hironaka.HadamardBridge
noncomputable section
variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
variable {N : Set M} {𝔞 : GermIdeal n M}

theorem homogenizedIdealAlong_univ (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) (μ : ℕ) :
    homogenizedIdealAlong univ 𝔞 μ = HomogenizedIdeal.homogenizedIdeal 𝔞 μ := by
  rw [homogenizedIdeal_eq_homSum]
  exact homSum_congr (fun i _ => iterDerivIdealAlong_univ h𝔞 i) (iterDerivIdealAlong_univ h𝔞 (μ - 1))

theorem derivMarkedAlong_eq_derivMarked {𝔪 : MarkedIdeal n M} (hN : 𝔪.N = univ)
    (h𝔞 : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x) (j : ℕ) : derivMarkedAlong 𝔪 j = derivMarked 𝔪 j :=
  MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl
    (show iterDerivIdealAlong 𝔪.N 𝔪.ideal j = iterDerivIdeal 𝔪.ideal j by rw [hN, iterDerivIdealAlong_univ h𝔞]) rfl

theorem coeffMarkedAlong_eq_coeffMarked {𝔪 : MarkedIdeal n M} (hN : 𝔪.N = univ)
    (h𝔞 : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x) : coeffMarkedAlong 𝔪 = coeffMarked 𝔪 := by
  unfold coeffMarkedAlong coeffMarked
  congr 1
  funext i
  exact derivMarkedAlong_eq_derivMarked hN h𝔞 i

theorem isMaximalOrderAlong_univ_iff (h𝔞 : 𝔞.IsCoherent) {μ : ℕ} :
    IsMaximalOrderAlong univ 𝔞 μ ↔ MaximalContact.IsMaximalOrder 𝔞 μ := by
  refine ⟨CompanionReduction.isMaximalOrder_of_forall_notMem h𝔞, fun h x hx => ?_⟩
  have hx' : x ∈ cosupport n univ (iterDerivIdeal 𝔞 μ) 1 := by
    refine MaximalContact.cosupport_add_subset_cosupport_iterDerivIdeal 𝔞 1 μ ?_
    rwa [Nat.add_comm]
  have h1 := (vanishesToOrderOn_one_iff hx'.1 (holomorphicAt_const 1)).mp (hx'.2 _ (h x))
  exact one_ne_zero h1

end
end Hironaka.HomogenizedIdealAlong
