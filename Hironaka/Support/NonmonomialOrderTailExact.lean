/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Invariant.NonmonomialOrderTail

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.NonmonomialOrderTail

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.MarkedIdealBiholomorphism Hironaka.MonomialPartAlong
  Hironaka.CompanionReductionAlong Hironaka.CompanionRebase
  Hironaka.GermIdealOrder Hironaka.BlowupTowers
  Hironaka.DivisorExponentAlong
  Hironaka.BlowupTowerTransforms Hironaka.MarkedIdealRestrictOpen
  Hironaka.StepOneRegime Hironaka.NonmonomialOrderLocal
  Hironaka.NonmonomialOrderRegime Hironaka.NonmonomialOrderCanonical
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.ResolutionDriver (maxLocus)

noncomputable section

variable {n : ℕ}

section Start

variable {X : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ] {𝔪 : MarkedIdeal n X}
  {f : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

/-- **At the start of its run a point is in its regime**: if `y` is in the regime `P` at the last stage of `T`, then
the image of `y` at the stage where its run starts (the split of `T` at the run) is in the regime there. -/
theorem regime_start (P : Regime X) {Y : CMfd.{u} n} (T : BlowupTower X Y) {y : Y} (hy : P T y) :
    P (BlowupTowerSplit.head T (regimeRun P T y)) ((BlowupTowerSplit.tail T (regimeRun P T y)).proj y) := by
  rcases Nat.eq_zero_or_pos (regimeRun P T y) with h0 | hpos
  · rw [h0]
    cases T <;> exact hy
  · exact regime_head_of_le_regimeRun P T y _ hpos le_rfl

/-- **At the start of its run a point of order `o` is in the regime `o` and in the mask of `o`.** -/
theorem proj_tail_mem_ordMask (hn : 0 < n) {k : ℕ} (h : IsInvDomain k 𝔪) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower 𝔪 T) {y : Y} (hy : y ∈ (geoTransformAlong 𝔪 T).cosupp) {o : ℕ}
    (hyo : nmOrd (geoTransformAlong 𝔪 T) y = o) :
    OrdRegime 𝔪 o (BlowupTowerSplit.head T (regimeRun (OrdRegime 𝔪 o) T y))
        ((BlowupTowerSplit.tail T (regimeRun (OrdRegime 𝔪 o) T y)).proj y) ∧
      (BlowupTowerSplit.tail T (regimeRun (OrdRegime 𝔪 o) T y)).proj y ∈
        ordMask (geoTransformAlong 𝔪 (BlowupTowerSplit.head T (regimeRun (OrdRegime 𝔪 o) T y))) o := by
  have hreg := regime_start (OrdRegime 𝔪 o) T (y := y) ⟨hy, hyo⟩
  refine ⟨hreg, ?_⟩
  have hT₀ := ((BlowupTowerSplit.isGeoTestTower_iff_head_tail 𝔪 T (regimeRun (OrdRegime 𝔪 o) T y)).mp hT).1
  have hdom₀ := InvDomainTowerAlong.isInvDomain_geoTransformAlong h _ hT₀
  refine (mem_ordMask_iff hn hdom₀.isWellFormed hdom₀.isNonzeroAlongAt o _).mpr fun hge => ?_
  have h1 := (mem_ordGe_iff hdom₀.isWellFormed hdom₀.isNonzeroAlongAt
    ((geoTransformAlong 𝔪 _).cosupp_subset_N hreg.1) (o + 1)).mp hge
  rw [hreg.2] at h1
  omega

end Start
end
end Hironaka.NonmonomialOrderTail
