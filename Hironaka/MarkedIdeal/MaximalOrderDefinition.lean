/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.DerivativeIdealCoherence

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.MaximalContact
noncomputable section
open Hironaka HolomorphicIdealSheaves GermIdealOrder DerivativeIdeal
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- `𝓓^j(𝓓^i 𝔞) = 𝓓^{i+j} 𝔞`. -/
theorem iterDerivIdeal_iterDerivIdeal (𝔞 : GermIdeal n M) (i : ℕ) :
    ∀ j, iterDerivIdeal (iterDerivIdeal 𝔞 i) j = iterDerivIdeal 𝔞 (i + j)
  | 0 => rfl
  | j + 1 => by
    rw [iterDerivIdeal_succ, iterDerivIdeal_iterDerivIdeal 𝔞 i j, ← Nat.add_assoc,
      iterDerivIdeal_succ]

/-- **Maximal order** (Villamayor; Włodarczyk §2.7): `𝓓^μ(𝔞) = 𝒪_M`. -/
def IsMaximalOrder (𝔞 : GermIdeal n M) (μ : ℕ) : Prop :=
  ∀ x : M, (iterDerivIdeal 𝔞 μ).mem x (fun _ => 1)

/-- **Derivatives of a marked ideal of maximal order** are of maximal order:
`(𝓓^i 𝔞, μ - i)` for `i ≤ μ`. -/
theorem IsMaximalOrder.iterDerivIdeal {𝔞 : GermIdeal n M} {μ : ℕ} (h : IsMaximalOrder 𝔞 μ)
    {i : ℕ} (hi : i ≤ μ) : IsMaximalOrder (DerivativeIdeal.iterDerivIdeal 𝔞 i) (μ - i) := by
  intro x
  rw [iterDerivIdeal_iterDerivIdeal, Nat.add_sub_cancel' hi]
  exact h x

/-- **Giraud's inclusion, iterated** (`N = M`): `cosupp(𝔞, μ + j) ⊆ cosupp(𝓓^j 𝔞, μ)`. -/
theorem cosupport_add_subset_cosupport_iterDerivIdeal (𝔞 : GermIdeal n M) (μ : ℕ) :
    ∀ j, cosupport n univ 𝔞 (μ + j) ⊆ cosupport n univ (iterDerivIdeal 𝔞 j) μ
  | 0 => subset_rfl
  | j + 1 => by
    have h1 : cosupport n univ 𝔞 (μ + (j + 1)) ⊆ cosupport n univ (iterDerivIdeal 𝔞 j) (μ + 1) := by
      rw [show μ + (j + 1) = (μ + 1) + j by omega]
      exact cosupport_add_subset_cosupport_iterDerivIdeal 𝔞 (μ + 1) j
    exact h1.trans (cosupport_succ_subset_cosupport_derivIdeal μ)


end
end Hironaka.MaximalContact
