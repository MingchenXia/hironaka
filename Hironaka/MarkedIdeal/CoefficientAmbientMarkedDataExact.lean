/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.CoefficientIdeal
import Hironaka.MarkedIdeal.DerivativeIdealCoherence
import Hironaka.MarkedIdeal.DerivativeAmbientMarkedDataExact

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology Manifold
universe u
namespace Hironaka.CoefficientIdeal
open Hironaka Hironaka.HolomorphicIdealSheaves MarkedIdeals DerivativeIdeal DerivativeIdealTower HomogenizedGlueing
noncomputable section
variable {n : ℕ}

section Ambient
variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
structure IsAmbientFamily (𝔪 : ℕ → MarkedIdeal n M) (m : ℕ) : Prop where
  N : ∀ i < m, (𝔪 i).N = univ
  E : ∀ i < m, (𝔪 i).E = (𝔪 0).E
  coh : ∀ i < m, (𝔪 i).ideal.IsCoherent
  d : ∀ i < m, 1 ≤ (𝔪 i).d

variable {𝔪 : ℕ → MarkedIdeal n M} {m : ℕ}

theorem IsAmbientFamily.isCoherent_msum (h : IsAmbientFamily 𝔪 m) : (msum 𝔪 m).ideal.IsCoherent :=
  isCoherent_finSumIdeal_of_lt fun i hi => GermIdealPullbackCalculus.isCoherent_idealPow (h.coh i hi) _

end Ambient

def coeffMarked {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    (𝔪 : MarkedIdeal n M) : MarkedIdeal n M :=
  msum (fun i => derivMarked 𝔪 i) 𝔪.d

theorem isAmbientFamily_derivMarked {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] {𝔪 : MarkedIdeal n M}
    (hN : 𝔪.N = univ) (h𝔞 : 𝔪.ideal.IsCoherent) :
    IsAmbientFamily (fun i => derivMarked 𝔪 i) 𝔪.d where
  N _ _ := hN
  E _ _ := rfl
  coh i _ := isCoherent_iterDerivIdeal h𝔞 i
  d i hi := by simp only [derivMarked_d]; omega

end
end Hironaka.CoefficientIdeal
