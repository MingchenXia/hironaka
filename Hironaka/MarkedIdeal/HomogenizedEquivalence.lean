/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.CoefficientIdealRestriction
import Hironaka.Invariant.CompanionReduction
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.MarkedIdeal.CoefficientIdeal
import Hironaka.MarkedIdeal.DerivativeIdeal
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.MarkedIdeal.HomogenizedGlueing
import Hironaka.MarkedIdeal.HomogenizedIdeal
import Hironaka.Invariant.IdealOrderArithmetic
import Hironaka.Analytic.IdealPowers
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The homogenized ideal is equivalent to the marked ideal

Source: Włodarczyk 2005, the lemma after `le:hom` (`(𝓗(𝓘), μ) ≃ (𝓘, μ)`, `hiron.tex` lines 822--840); the analytic
paper (GGT 2008) §5.5.

* `homSum A B μ = ∑_{i<μ} Aᵢ Bⁱ`, so `𝓗(𝔞) = homSum (𝓓^i 𝔞) T(𝔞) μ` (`homogenizedIdeal_eq_homSum`, by definition);
  `orderGE_homSum`: the order of `∑ᵢ Aᵢ Bⁱ` is `≥ μ` where `ord Aᵢ ≥ μ - i` and `ord B ≥ 1`.

Not here: `𝓗` and `𝓒` commute with restriction to open sets and with biholomorphisms between open sets
(`le:etale2` / `le:etale3`).
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HomogenizedEquivalence

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder DerivativeIdeal IdealWeightPowers BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal DerivativeIdealTower CoefficientIdeal HomogenizedIdeal HomogenizedGlueing MarkedIdealEquivalence MarkedIdealEquivalence.MarkedIdeal BlowupControlledTransform MarkedIdealOperationsTransform CoefficientIdealRestriction GermIdealPullbackCalculus

noncomputable section

/-! ### Sums `∑ᵢ Aᵢ Bⁱ` -/

section OneSpace

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- `∑_{i<μ} Aᵢ · Bⁱ`. -/
def homSum (A : ℕ → GermIdeal n M) (B : GermIdeal n M) (μ : ℕ) : GermIdeal n M :=
  finSumIdeal (fun i => (A i).mul (idealPow B i)) μ

/-- `𝓗(𝔞) = ∑_{i<μ} 𝓓^i(𝔞) · T(𝔞)^i` with `T(𝔞) = 𝓓^{μ-1}(𝔞)`. -/
theorem homogenizedIdeal_eq_homSum (𝔞 : GermIdeal n M) (μ : ℕ) :
    homogenizedIdeal 𝔞 μ = homSum (fun i => iterDerivIdeal 𝔞 i) (iterDerivIdeal 𝔞 (μ - 1)) μ := rfl

variable [IsComplexManifold n M]

theorem homSum_congr {A A' : ℕ → GermIdeal n M} {B B' : GermIdeal n M} {μ : ℕ} (hA : ∀ i < μ, A i = A' i)
    (hB : B = B') : homSum A B μ = homSum A' B' μ := by
  subst hB
  exact finSumIdeal_congr fun i hi => by rw [hA i hi]

/-- The order of a product: `ord(𝔞𝔟) ≥ p + q` where `ord 𝔞 ≥ p` and `ord 𝔟 ≥ q` (along any `N`). -/
theorem orderGE_mul {N : Set M} {𝔞 𝔟 : GermIdeal n M} {x : M} {p q : ℕ} (ha : OrderGE n N 𝔞 x p)
    (hb : OrderGE n N 𝔟 x q) : OrderGE n N (𝔞.mul 𝔟) x (p + q) := fun _ hg =>
  IdealOrderArithmetic.IsInSpanAt.vanishesToOrderOn (IdealOrderArithmetic.mem_mul_iff.mp hg) (by
    rintro s ⟨a, b, ha', hb', rfl⟩
    exact (ha a ha').mul (hb b hb'))

/-- The order of a power: `ord(𝔟^i) ≥ i` where `ord 𝔟 ≥ 1` (along any `N`). -/
theorem orderGE_idealPow {N : Set M} {𝔟 : GermIdeal n M} {x : M} (h1 : OrderGE n N 𝔟 x 1) :
    ∀ i : ℕ, OrderGE n N (idealPow 𝔟 i) x i
  | 0 => fun _ hg => vanishesToOrderOn_zero (holomorphicAt_of_mem_idealPow hg)
  | i + 1 => fun _ hg => by
      refine IdealOrderArithmetic.IsInSpanAt.vanishesToOrderOn (mem_idealPow_succ_iff.mp hg) ?_
      rintro s ⟨a, b, ha, hb, rfl⟩
      exact (orderGE_idealPow h1 i a ha).mul (h1 b hb)

/-- **The order of `∑ᵢ Aᵢ Bⁱ` is `≥ μ`** where `ord Aᵢ ≥ μ - i` (`i < μ`) and `ord B ≥ 1`. -/
theorem orderGE_homSum {N : Set M} {A : ℕ → GermIdeal n M} {B : GermIdeal n M} {μ : ℕ} {x : M}
    (hA : ∀ i < μ, OrderGE n N (A i) x (μ - i)) (hB : OrderGE n N B x 1) :
    OrderGE n N (homSum A B μ) x μ := fun _ hg =>
  IdealOrderArithmetic.IsInSpanAt.vanishesToOrderOn
    (show IsInSpanAt (n := n) (fun s => ∃ i, i < μ ∧ ((A i).mul (idealPow B i)).mem x s) x _ from hg) (by
    rintro s ⟨i, hi, hs⟩
    have := orderGE_mul (hA i hi) (orderGE_idealPow hB i) s hs
    rwa [Nat.sub_add_cancel hi.le] at this)

/-- `A₀ ⊆ ∑ᵢ Aᵢ Bⁱ` (`μ ≥ 1`). -/
theorem le_homSum {A : ℕ → GermIdeal n M} {B : GermIdeal n M} {μ : ℕ} (hμ : 1 ≤ μ)
    (hA : ∀ x g, (A 0).mem x g → HolomorphicAt n g x) : (A 0).Le (homSum A B μ) := by
  intro x g hg
  have hgh := hA x g hg
  show IsInSpanAt (n := n) (fun s => ∃ i, i < μ ∧ ((A i).mul (idealPow B i)).mem x s) x g
  refine isInSpanAt_of_eq_mul (s := fun p => g p * 1) ⟨0, hμ, ?_⟩ hgh (holomorphicAt_const 1)
    (Eventually.of_forall fun p => by simp)
  exact mul_mem_mul (b := fun _ => 1) hg (holomorphicAt_const (n := n) (x := x) 1) (by simpa using hgh)

theorem isCoherent_homSum {A : ℕ → GermIdeal n M} {B : GermIdeal n M} {μ : ℕ} (hA : ∀ i < μ, (A i).IsCoherent)
    (hB : B.IsCoherent) : (homSum A B μ).IsCoherent :=
  isCoherent_finSumIdeal_of_lt fun i hi => isCoherent_mul (hA i hi) (isCoherent_idealPow hB i)

end OneSpace

end

end Hironaka.HomogenizedEquivalence
