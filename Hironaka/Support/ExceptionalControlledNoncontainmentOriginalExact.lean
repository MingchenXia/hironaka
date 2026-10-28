/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.HadamardControlledCoherenceOriginalExact
import Hironaka.Blowup.ExceptionalIdealPushforward

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.ExceptionalIdealPushforward

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.GermIdealOrder Hironaka.OrderTaylor
open Hironaka.HolomorphicTaylorTail
open Hironaka.HadamardBridge
open Hironaka.OrderMultiplicativity
open Hironaka.HolomorphicAnalytic
open Hironaka.BlowupFlatCoordinates
open Hironaka.BlowupMonomialCharts
open Hironaka.BlowupLocalSurjectivity
open Hironaka.BlowupExceptionalDivisor
open Hironaka.BlowupStrictIdeal
open Hironaka.GlueingTrivialAction
open Hironaka.IdealWeightPowers
open Hironaka.BlowupFunctionTransform
open Hironaka.BlowupStrictSubmanifold

noncomputable section

variable {n : ℕ}

section Blowup

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

/-- **A controlled transform inside `𝒪(-D)` forces a higher order** (for Włodarczyk 2005, Step 2a
of `pr:resol`; the blowup half of TN-CLASSICAL's `hir:nonmonomial-transform`): if `C ⊆ cosupp(𝔞, μ)`
for a coherent `𝔞` and `σ^c(𝔞, μ) ⊆ 𝒪(-D)` at a point `z` over `C`, then `ord_{π z} 𝔞 ≥ μ + 1`.
Indeed `π^*𝔞 = 𝒪(-μD) σ^c(𝔞, μ) ⊆ 𝒪(-D)^{μ+1}` at `z`, so `𝔞 ⊆ 𝓘_C^{μ+1}` at `π z`. -/
theorem mem_cosupport_succ_of_controlledTransform_le (hπ : IsBlowupAlong n C π)
    {𝔞 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent) {μ : ℕ} (hsub : C ⊆ cosupport n univ 𝔞 μ) {z : Y}
    (hz : π z ∈ C)
    (hle : ∀ g, (BlowupControlledTransform.controlledTransform hπ 𝔞 μ).mem z g →
      (exceptionalDivisor hπ).ideal.mem z g) :
    π z ∈ cosupport n univ 𝔞 (μ + 1) := by
  refine ⟨mem_univ _, fun a ha => ?_⟩
  have hahol : HolomorphicAt n a (π z) :=
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 ha
  have hπd : ∀ᶠ w in 𝓝 z, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) π w :=
    Eventually.of_forall fun w => (hπ.contMDiff w).mdifferentiableAt (by simp)
  have haπ : HolomorphicAt n (a ∘ π) z := holomorphicAt_comp_map hπd hahol
  have h1 : (GermIdeal.pullback (m := n) π 𝔞).mem z (a ∘ π) :=
    BlowupDerivativeIdeal.comp_mem_pullback ha haπ (holomorphicAt_const 1)
      (Eventually.of_forall fun p => by simp)
  rw [pullback_eq_mul_controlledTransform_of_subset_cosupport hπ h𝔞 hsub] at h1
  have h2 : (idealPow (exceptionalDivisor hπ).ideal (μ + 1)).mem z (a ∘ π) :=
    mem_idealPow_succ_iff.mpr ((show IsInSpanAt (n := n) (fun s => ∃ p q,
      (idealPow (exceptionalDivisor hπ).ideal μ).mem z p ∧
        (BlowupControlledTransform.controlledTransform hπ 𝔞 μ).mem z q ∧ s = p * q) z (a ∘ π)
      from h1).mono fun _ ⟨p, q, hp, hq, hs⟩ => ⟨p, q, hp, hle q hq, hs⟩)
  have h3 := mem_idealPow_vanishingIdeal_of_pullback_mem hπ hz hahol h2
  have h4 : (idealPow (pointIdeal n (π z)) (μ + 1)).mem (π z) a :=
    mem_idealPow_of_mem_at (𝔞 := vanishingIdeal (n := n) C)
      (fun g (hg : (vanishingIdeal (n := n) C).mem (π z) g) =>
        mem_pointIdeal_of_apply_eq_zero hg.1 (hg.2.self_of_nhds hz)) (μ + 1) h3
  exact ⟨a, h4, Eventually.of_forall fun _ _ => rfl⟩

/-- **Where the order along the centre is exactly `μ`, the controlled transform is not in `𝒪(-D)`**:
if `C ⊆ cosupp(𝔞, μ)` and `ord_{π z} 𝔞 ≤ μ`, some germ of `σ^c(𝔞, μ)` at `z` is not in `𝒪(-D)`. -/
theorem exists_not_mem_exceptionalDivisor (hπ : IsBlowupAlong n C π) {𝔞 : GermIdeal n X}
    (h𝔞 : 𝔞.IsCoherent) {μ : ℕ} (hsub : C ⊆ cosupport n univ 𝔞 μ) {z : Y} (hz : π z ∈ C)
    (hord : π z ∉ cosupport n univ 𝔞 (μ + 1)) :
    ∃ g, (BlowupControlledTransform.controlledTransform hπ 𝔞 μ).mem z g ∧
      ¬ (exceptionalDivisor hπ).ideal.mem z g := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  exact hord (mem_cosupport_succ_of_controlledTransform_le hπ h𝔞 hsub hz h)

end Blowup

end

end Hironaka.ExceptionalIdealPushforward
