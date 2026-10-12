/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.DivisorExponentAlongUnivExact
import Hironaka.Invariant.MonomialCaseAlong
import Hironaka.Invariant.MonomialAmbientDataExact

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.MonomialCaseAlong
open Hironaka Hironaka.HolomorphicIdealSheaves Hironaka.MonomialInvariant Hironaka.MonomialCase Hironaka.DivisorExponent Hironaka.DivisorExponentAlong
noncomputable section
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
variable {𝔞 : GermIdeal n M} {E : List (Set M)}

/-- For `N = univ` this is `MonomialCase.gamma`. -/
theorem gammaAlong_univ (d : ℕ) (x : M) : gammaAlong n univ 𝔞 E d x = gamma n 𝔞 E d x := by
  unfold gammaAlong gamma
  congr 1
  funext i
  simp only [expDataAlong, expData, divExpAlong_univ]


end
end Hironaka.MonomialCaseAlong
