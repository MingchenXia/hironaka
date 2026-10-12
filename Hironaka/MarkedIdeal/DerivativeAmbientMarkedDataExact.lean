/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.DerivativeIdealTower
import Hironaka.MarkedIdeal.DerivativeIdeal

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology Manifold
universe u
namespace Hironaka.DerivativeIdealTower
open Hironaka MarkedIdeals DerivativeIdeal
noncomputable section
variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

def derivMarked (𝔪 : MarkedIdeal n M) (j : ℕ) : MarkedIdeal n M where
  N := 𝔪.N
  E := 𝔪.E
  ideal := iterDerivIdeal 𝔪.ideal j
  d := 𝔪.d - j

@[simp] theorem derivMarked_N (𝔪 : MarkedIdeal n M) (j : ℕ) : (derivMarked 𝔪 j).N = 𝔪.N := rfl

@[simp] theorem derivMarked_E (𝔪 : MarkedIdeal n M) (j : ℕ) : (derivMarked 𝔪 j).E = 𝔪.E := rfl

@[simp] theorem derivMarked_ideal (𝔪 : MarkedIdeal n M) (j : ℕ) :
    (derivMarked 𝔪 j).ideal = iterDerivIdeal 𝔪.ideal j := rfl

@[simp] theorem derivMarked_d (𝔪 : MarkedIdeal n M) (j : ℕ) : (derivMarked 𝔪 j).d = 𝔪.d - j := rfl

end
end Hironaka.DerivativeIdealTower
