/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.HadamardBridge
import Hironaka.Invariant.IdealOrderArithmetic
import Hironaka.Manifold.ComplexManifold
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Derivative ideals commute with pullback by biholomorphisms

Sources: Włodarczyk 2005 §2.4 (functoriality of the derivative ideals and of the invariants under étale maps, here
biholomorphisms), Bierstone--Milman 2008 §3.2 (`𝓓(𝓘)` is intrinsic: the image of `Der × 𝓘 → 𝒪`).
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.DerivativeIdealInvariance

open Hironaka.HolomorphicIdealSheaves
open Hironaka.DerivativeIdeal Hironaka.IdealOrderArithmetic Hironaka.HadamardBridge

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']

/-! ### The chain rule in charts -/

section ChainRule

variable {φ : M' → M} (e : ComplexChart n M) (e' : ComplexChart n M') {y : M'}

/-- The coefficient of the chain rule: the `j`-th coordinate of `D(e ∘ φ ∘ e'⁻¹)(e' p) v`. -/
def chainCoeff (φ : M' → M) (v : ComplexModel n) (j : Fin n) : M' → ℂ :=
  fun p => fderiv ℂ (e.val ∘ φ ∘ e'.val.symm) (e'.val p) v j

end ChainRule

end

end Hironaka.DerivativeIdealInvariance
