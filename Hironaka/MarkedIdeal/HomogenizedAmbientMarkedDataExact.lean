/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.HomogenizedEquivalence

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HomogenizedEquivalence
open Hironaka Hironaka.HolomorphicIdealSheaves MarkedIdeals HomogenizedIdeal
noncomputable section
variable {n : ℕ}
/-- **The homogenized marked ideal** `𝓗(𝔪) = (M, N, E, 𝓗(𝔞), μ)` of `𝔪 = (M, N, E, 𝔞, μ)`. -/
def homMarked {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] (𝔪 : MarkedIdeal n M) :
    MarkedIdeal n M where
  N := 𝔪.N
  E := 𝔪.E
  ideal := homogenizedIdeal 𝔪.ideal 𝔪.d
  d := 𝔪.d

end
end Hironaka.HomogenizedEquivalence
