/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.IdealPresentation
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
set_option autoImplicit false

/-!
# Products of ideal sheaves

The family of pairwise products of two families of functions (`mulFamily`) and membership in a product of ideal
sheaves.

Declarations:
* `mulFamily`
* `mulFamily_apply`
* `mem_mul_iff`
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.IdealWeightProducts

noncomputable section

open Hironaka.HolomorphicIdealSheaves
open Hironaka.IdealWeightComparison

/-! ### The family of pairwise products -/

section Family

variable {X : Type*} {N P : ℕ}

/-- The `N·P` pairwise products of two finite families, indexed through
`finProdFinEquiv`. -/
def mulFamily (g : Fin N → X → ℂ) (h : Fin P → X → ℂ) : Fin (N * P) → X → ℂ :=
  fun k y => g (finProdFinEquiv.symm k).1 y * h (finProdFinEquiv.symm k).2 y

theorem mulFamily_apply (g : Fin N → X → ℂ) (h : Fin P → X → ℂ)
    (i : Fin N) (j : Fin P) (y : X) :
    mulFamily g h (finProdFinEquiv (i, j)) y = g i y * h j y := by
  simp [mulFamily]

end Family

/-! ### The weight of a product ideal -/

section Ideal

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- Unfolding the product ideal. -/
theorem mem_mul_iff {𝔞 𝔟 : GermIdeal n M} {x : M} {v : M → ℂ} :
    (𝔞.mul 𝔟).mem x v ↔
      IsInSpanAt (n := n) (fun s => ∃ a b, 𝔞.mem x a ∧ 𝔟.mem x b ∧ s = a * b) x v :=
  Iff.rfl

end Ideal

end

end Hironaka.IdealWeightProducts
