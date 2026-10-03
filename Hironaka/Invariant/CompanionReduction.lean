/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.GermOrderProduct
import Hironaka.MarkedIdeal.MarkedIdealOperationsTransform
import Hironaka.Blowup.BlowupDerivativeIdeal
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.GermIdealTotalTransform
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Analytic.IdealPowers
import Hironaka.MarkedIdeal.InvertibleIdealQuotient
import Hironaka.Invariant.OrderTaylor
import Hironaka.Analytic.IdealSpanCalculus
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Reduction to maximal order: the companion ideal along multiple test blow-ups

Sources: Włodarczyk 2005, Proposition `pr:resol`, Step 2a; Bierstone--Milman 2008 §5, Step II.B and Remark 5.2.

Let `𝔞 = 𝔟 𝔠` on `M` (`N = M`), with a common `E`, coherent `𝔟, 𝔠`, a mark `d ≥ 1` and `o ≥ 1` such that
`ord_x 𝔟 ≤ o` at every point of `cosupp(𝔞, d)`.  The **companion ideal** is `(𝔟, o) + (𝔠, d - o)` if `o < d` and
`(𝔟, o)` if `o ≥ d`.  The abstract factorization stands for the monomial / nonmonomial decomposition
`𝔞 = 𝓜(𝔞) 𝓝(𝔞)` (`𝔟 = 𝓝`, `𝔠 = 𝓜`), which is not needed here.

## Main results
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.CompanionReduction

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.GermIdealOrder Hironaka.IdealWeightPowers Hironaka.DerivativeIdeal Hironaka.OrderTaylor Hironaka.BlowupControlledTransform Hironaka.BlowupExceptionalDivisor Hironaka.InvertibleIdealQuotient Hironaka.BlowupTowers Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.MarkedIdealOperationsTransform Hironaka.MarkedIdealOperationsTransform.MarkedIdeal Hironaka.GermOrderProduct

noncomputable section

/-! ### Ideal-level facts for one blowup -/

section OneBlowup

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

/-- A germ of a coherent ideal times a holomorphic germ is a germ of the ideal. -/
theorem mul_mem_of_isCoherent {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
    [IsComplexManifold n Z] {J : GermIdeal n Z} (hJ : J.IsCoherent) {y : Z} {c g : Z → ℂ}
    (hc : HolomorphicAt n c y) (hg : J.mem y g) : J.mem y (fun p => c p * g p) :=
  GermIdealTotalTransform.mem_of_isInSpanAt_mem hJ
    (RelativePrincipalizationSpan.IsInSpanAt.mul_left hc
      (isInSpanAt_self hg (RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hJ hg)))

/-- `g ∘ π` is a germ of `π^*𝔟` at `z` for a germ `g` of the coherent `𝔟` at `π z`. -/
theorem comp_mem_pullback' (hπ : IsBlowupAlong n C π) {𝔟 : GermIdeal n X} (h𝔟 : 𝔟.IsCoherent) {z : Y}
    {g : X → ℂ} (hg : 𝔟.mem (π z) g) : (GermIdeal.pullback (m := n) π 𝔟).mem z (g ∘ π) := by
  have hgh : HolomorphicAt n g (π z) := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔟 hg
  have hcomp : HolomorphicAt n (g ∘ π) z :=
    hgh.comp_contMDiff (Eventually.of_forall fun q => hπ.contMDiff q)
  exact BlowupDerivativeIdeal.comp_mem_pullback (c := fun _ => 1) hg hcomp (holomorphicAt_const 1)
    (Eventually.of_forall fun p => by simp)

end OneBlowup

section Tower

variable {n : ℕ} {X : CMfd.{u} n}

end Tower

/-! ### The companion ideal is of maximal order -/

section MaximalOrder

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Powers of a holomorphic germ are holomorphic. -/
theorem holomorphicAt_pow_of {x : M} {g : M → ℂ} (hg : HolomorphicAt n g x) :
    ∀ k : ℕ, HolomorphicAt n (fun p => g p ^ k) x
  | 0 => by simpa using holomorphicAt_const (n := n) (x := x) (1 : ℂ)
  | k + 1 => by
    have h := (holomorphicAt_pow_of hg k).mul hg
    simpa [pow_succ] using h

/-- `g ∉ 𝔪_x^{o+1}` gives `g^k ∉ 𝔪_x^{k o + 1}` (orders add, `GermOrderProduct.mul_notMem_idealPow`). -/
theorem pow_notMem_idealPow {x : M} {g : M → ℂ} (hg : HolomorphicAt n g x) {o : ℕ}
    (hgo : ¬ (idealPow (pointIdeal n x) (o + 1)).mem x g) :
    ∀ k : ℕ, ¬ (idealPow (pointIdeal n x) (k * o + 1)).mem x (fun p => g p ^ k)
  | 0 => by
    intro h
    have h1 : (idealPow (pointIdeal n x) 1).mem x (fun _ => (1 : ℂ)) :=
      mem_idealPow_congr (by simpa using h) (Eventually.of_forall fun _ => rfl)
    have := apply_eq_zero_of_mem_idealPow_pointIdeal le_rfl h1
    simp at this
  | k + 1 => by
    intro h
    have hk := holomorphicAt_pow_of hg k
    have hne := GermOrderProduct.mul_notMem_idealPow (f := fun p => g p ^ k) hk hg
      (pow_notMem_idealPow hg hgo k) hgo
    refine hne (mem_idealPow_congr (by rwa [show k * o + o + 1 = (k + 1) * o + 1 by ring]) ?_)
    exact Eventually.of_forall fun p => pow_succ (g p) k

end MaximalOrder

end

end Hironaka.CompanionReduction
