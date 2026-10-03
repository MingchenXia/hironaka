/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.NormalDerivativeMonomial
import Hironaka.MarkedIdeal.CoefficientIdealRestriction
import Hironaka.Blowup.GlueingTrivialAction
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupFlatCoordinates
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.HadamardBridge
import Hironaka.Analytic.HolomorphicTaylorTail
import Hironaka.Invariant.IdealOrderArithmetic
import Hironaka.Analytic.IdealPowers
import Hironaka.MarkedIdeal.NormalDerivativeChart
import Hironaka.MarkedIdeal.NormalTaylorOrder
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The restricted coefficient ideal along multiple test blow-ups: the support

Source: Włodarczyk 2005, proof of Lemma `le:S`; GGT 2008 (`wlodarczyk09-analytic-resolution`), proof of Proposition
5.6.4 (2)-(3): the coefficients `c_{α f k}` of the transforms `f_k` in the normal coordinates of the strict
transforms `S_k` satisfy `c_{α f k}|_{S_k} ∈ (σ^k|_{S_k})^c(𝓓^{|α|}(𝓘)|_S)`.

**The invariant**: at a point `p` of `S_T` there are a flat chart for `S_T` and generators of the transformed ideal
`𝔪_T` at `p` whose normal derivatives `∂^L` (`|L| < μ`) restrict on `S_T` into the transformed derivative ideals
`[𝓓^{|L|} 𝔪]_T`.

* `GoodAt.mem_cosupp` (the conclusion): at a good point of `S_T` where every `[𝓓^i 𝔪]_T` has order `≥ μ - i` along
  `S_T`, the point lies in `cosupp 𝔪_T` (`NormalTaylorOrder`).
-/

open Set Filter Metric
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.CoefficientRestrictionTower

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder DerivativeIdeal IdealWeightPowers BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal DerivativeIdealTower CoefficientIdeal HomogenizedGlueingTower CoefficientIdealRestriction HolomorphicTaylorTail NormalTaylorOrder NormalDerivativeChart NormalDerivativeMonomial BlowupControlledTransform

noncomputable section

variable {n : ℕ} {X : CMfd.{u} n}

/-- Restricted spans of germs vanishing to order `μ` along `W` vanish to order `μ` along `W`. -/
theorem vanishesToOrderOn_of_isInSpanOnAt {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] {W : Set M} {S : (M → ℂ) → Prop} {z : M} {g : M → ℂ} {μ : ℕ}
    (hg : IsInSpanOnAt (n := n) W S z g) (hS : ∀ s, S s → VanishesToOrderOn n W z μ s) :
    VanishesToOrderOn n W z μ g := by
  obtain ⟨K, s, c, hs, hc, hsum⟩ := hg
  obtain ⟨h, hh, hgh⟩ := IdealOrderArithmetic.vanishesToOrderOn_sum_mul (N := W) hc fun k => hS _ (hs k)
  exact ⟨h, hh, by filter_upwards [hsum, hgh] with p hp hp' hpW; rw [hp hpW, hp' hpW]⟩

/-! ### Tools -/

section Tools

variable {Y Z : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

/-- Spans pull back along holomorphic maps. -/
theorem isInSpanAt_comp_map {S : (Y → ℂ) → Prop} {π : Z → Y} {z : Z}
    (hπ : ∀ᶠ w in 𝓝 z, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π w)
    {a : Y → ℂ} (ha : IsInSpanAt (n := n) S (π z) a) :
    IsInSpanAt (n := n) (fun t => ∃ s, S s ∧ t = s ∘ π) z (a ∘ π) := by
  obtain ⟨hah, K, t, c, ht, hc, hsum⟩ := ha
  refine ⟨HadamardBridge.holomorphicAt_comp_map hπ hah, K, fun k => t k ∘ π, fun k => c k ∘ π,
    fun k => ⟨t k, ht k, rfl⟩, fun k => HadamardBridge.holomorphicAt_comp_map hπ (hc k), ?_⟩
  filter_upwards [hπ.self_of_nhds.continuousAt.eventually hsum] with p hp
  simpa using hp

end Tools

/-! ### The step over the centre -/

section Centre

open BlowupFlatCoordinates BlowupMonomialCharts

variable {Y Z : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

/-- Normal derivatives of a holomorphic germ are holomorphic. -/
theorem FlatChart.holomorphicAt_nd {S : Set Y} {p : Y} {k : ℕ} (c : FlatChart n S p k) {f : Y → ℂ}
    (hf : HolomorphicAt n f p) (L : List (Fin n)) : HolomorphicAt n (c.nd L f) p := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp (c.eventually_differentiableAt_comp_inv hf)
  have hFU : DifferentiableOn ℂ (fun u => f (c.inv u)) (ball 0 r) := fun z hz =>
    (hball z hz).differentiableWithinAt
  have hd := differentiableOn_iterDeriv hFU isOpen_ball (L.map bv)
  refine holomorphicAt_comp_flat c.Φ c.mem_flatDomain ?_
  rw [show c.Φ.toFun (chartAt (ComplexModel n) p p) = 0 from c.zero]
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with w hw
  exact (hd w hw).differentiableAt (isOpen_ball.mem_nhds hw)

end Centre

end

end Hironaka.CoefficientRestrictionTower
