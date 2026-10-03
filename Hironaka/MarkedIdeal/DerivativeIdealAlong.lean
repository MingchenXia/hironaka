/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.DerivativeIdeal
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.HolomorphicGermAlgebra
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Derivative ideals along a submanifold

Sources: Bierstone--Milman 2008, §3.2 (`𝓓(𝓘)` is the image of `Der_N × 𝓘 → 𝒪_N`), Włodarczyk 2005, §2.6.

For a marked ideal `(M, N, E, 𝔞, d)` with `N ⊊ M` the derivative ideal of the algorithm is that of the ideal `𝔞|_N`
of `𝒪_N`, taken with the derivations of `N`. In the ambient encoding of the marked ideals it is represented by the
ambient ideal `derivIdealAlong N 𝔞`, generated at `x` by

* the germs of `𝔞_x` and of `𝓘_N` at `x`, and
* the derivatives `ξ(f) = ∑ₘ ξₘ ∂^e_{eₘ} f` (`f ∈ 𝔞_x`, `e` a chart at `x`) along holomorphic vector
  fields `ξ` **tangent to `N`** at `x`: `ξ(𝓘_N) ⊆ 𝓘_N` at `x` (`IsTangentField`).

Restricted to `N` this is the derivative ideal of `𝔞|_N` (derivations of `𝒪_N` are the ambient
derivations preserving `𝓘_N`, modulo `𝓘_N · Der`); it is NOT the restriction of the ambient
`𝓓(𝔞)`: for `N = {u = 0}` and `𝔞 = (u)`, `𝔞|_N = 0` but `1 = ∂ᵤ u ∈ 𝓓(𝔞)`, while
`derivIdealAlong N 𝔞 = (u)`.

* `le_derivIdealAlong`, `vanishingIdeal_le_derivIdealAlong`, `derivIdealAlong_mono`.
* `iterDerivIdealAlong N 𝔞 j`.
-/

open Set Filter
open scoped Topology Manifold

namespace Hironaka.DerivativeIdealAlong

open Hironaka.HolomorphicIdealSheaves DerivativeIdeal

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The derivative of `f` along the vector field `ξ = ∑ₘ ξₘ ∂/∂eₘ` written in the chart `e`. -/
def fieldDeriv (e : ComplexChart n M) (ξ : Fin n → M → ℂ) (f : M → ℂ) : M → ℂ :=
  fun p => ∑ m, ξ m p * chartDeriv e (EuclideanSpace.single m 1) f p

/-- **A holomorphic vector field tangent to `N` at `x`** (written in the chart `e`): holomorphic
coefficients, and the derivation `ξ` maps germs of `𝓘_N` at `x` to germs of `𝓘_N` at `x`. -/
structure IsTangentField (N : Set M) (e : ComplexChart n M) (ξ : Fin n → M → ℂ) (x : M) :
    Prop where
  mem_source : x ∈ e.val.source
  holomorphicAt : ∀ m, HolomorphicAt n (ξ m) x
  preserves : ∀ g, (vanishingIdeal (n := n) N).mem x g →
    (vanishingIdeal (n := n) N).mem x (fieldDeriv e ξ g)

/-- The generators of `𝓓_N(𝔞)` at `x`. -/
def DerivGenAlong (N : Set M) (𝔞 : GermIdeal n M) (x : M) (s : M → ℂ) : Prop :=
  𝔞.mem x s ∨ (vanishingIdeal (n := n) N).mem x s ∨
    ∃ (e : ComplexChart n M) (ξ : Fin n → M → ℂ) (f : M → ℂ),
      IsTangentField N e ξ x ∧ 𝔞.mem x f ∧ s = fieldDeriv e ξ f

/-- **The derivative ideal of `𝔞` along `N`** (ambient representative of `𝓓(𝔞|_N)`). -/
def derivIdealAlong (N : Set M) (𝔞 : GermIdeal n M) : GermIdeal n M where
  mem x := IsInSpanAt (n := n) (DerivGenAlong N 𝔞 x) x

/-- Iterated derivative ideals along `N`. -/
def iterDerivIdealAlong (N : Set M) (𝔞 : GermIdeal n M) : ℕ → GermIdeal n M
  | 0 => 𝔞
  | j + 1 => derivIdealAlong N (iterDerivIdealAlong N 𝔞 j)

variable {N : Set M} {𝔞 𝔟 : GermIdeal n M}

theorem holomorphicAt_fieldDeriv {e : ComplexChart n M} {ξ : Fin n → M → ℂ} {f : M → ℂ} {x : M}
    (hx : x ∈ e.val.source) (hξ : ∀ m, HolomorphicAt n (ξ m) x) (hf : HolomorphicAt n f x) :
    HolomorphicAt n (fieldDeriv e ξ f) x :=
  HolomorphicAt.sum _ fun m _ => (hξ m).mul (holomorphicAt_chartDeriv hx hf)

/-- `𝔞 ⊆ 𝓓_N(𝔞)`. -/
theorem le_derivIdealAlong (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) :
    𝔞.Le (derivIdealAlong N 𝔞) :=
  fun x g hg => isInSpanAt_of_eq_mul (Or.inl hg) (h𝔞 x g hg) (holomorphicAt_const 1)
    (Eventually.of_forall fun _ => (one_mul _).symm)

/-- `𝓘_N ⊆ 𝓓_N(𝔞)`. -/
theorem vanishingIdeal_le_derivIdealAlong : (vanishingIdeal (n := n) N).Le (derivIdealAlong N 𝔞) :=
  fun _ _ hg => isInSpanAt_of_eq_mul (Or.inr (Or.inl hg)) hg.1 (holomorphicAt_const 1)
    (Eventually.of_forall fun _ => (one_mul _).symm)

/-- `𝓓_N` is monotone. -/
theorem derivIdealAlong_mono (h : 𝔞.Le 𝔟) : (derivIdealAlong N 𝔞).Le (derivIdealAlong N 𝔟) := by
  intro x g hg
  refine hg.mono fun s hs => ?_
  rcases hs with hs | hs | ⟨e, ξ, f, hξ, hf, rfl⟩
  · exact Or.inl (h x s hs)
  · exact Or.inr (Or.inl hs)
  · exact Or.inr (Or.inr ⟨e, ξ, f, hξ, h x f hf, rfl⟩)

end

end Hironaka.DerivativeIdealAlong
