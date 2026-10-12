/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.MonomialCase
import Hironaka.Invariant.AmbientDivisorExponent

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.MonomialCase
open Hironaka Hironaka.HolomorphicIdealSheaves Hironaka.DivisorExponent Hironaka.MonomialInvariant
noncomputable section
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
variable (n) in
/-- The exponents of `𝔞` along the members of `E` at `x` (`0` beyond the length of `E`). -/
def expData (𝔞 : GermIdeal n M) (E : List (Set M)) (x : M) (i : ℕ) : ℕ :=
  if h : i < E.length then divExp n 𝔞 (E.get ⟨i, h⟩) x else 0

variable (n) in
/-- **The invariant of a monomial marked ideal** at `x`. -/
def gamma (𝔞 : GermIdeal n M) (E : List (Set M)) (d : ℕ) (x : M) : WithBot Val :=
  inv n (memberIdx E x) (expData n 𝔞 E x) d

end
end Hironaka.MonomialCase
