/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.MarkedTowerTransportEquationsExact
import Hironaka.Resolution.HironakaSharpActualCurveUniformInitialStage

/-! Genuine finite prefixes of the actual global successor blowups,
then original base transport using the internally proved initial biholomorphism. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveGlobalPrefixTowers
noncomputable section
open Hironaka.BlowupSequences BlowupTowers MarkedIdealTowerTransport
  HironakaSharpActualCurveUniformStageAtlas HironakaSharpActualCurveTopologicalGluing
  HironakaSharpActualCurveGluedProjection HironakaSharpActualCurveGlobalManifold
  HironakaSharpActualCurveOriginalRecipeAtlas HironakaSharpActualCurveGlobalSuccessorMap
  HironakaSharpActualCurveGlobalSuccessorCentre HironakaSharpActualCurveGlobalSuccessorBlowup
  HironakaSharpActualCurveUniformInitialStage
attribute [local instance] endpointChartedSpace
variable {n : ℕ} {X : CMfd.{u} n} {J : Type u}

/-- All k original global constructors are retained, including empty centres. -/
def uniformGlobalTower (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) : (k : ℕ) →
      BlowupTower (endpointManifold (uniformStageHistories A 0) hc)
        (endpointManifold (uniformStageHistories A k) hc)
  | 0 => .refl
  | k+1 => .step (uniformGlobalTower A hc k) (globalUniformCentre A k)
      (globalUniformSuccessor A k) (isBlowupAlong_globalUniformSuccessor A hc k)

theorem uniformGlobalTower_length (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ) :
    (uniformGlobalTower A hc k).length=k := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (·+1) ih

theorem uniformGlobalTower_projection (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ)
    (z : endpointManifold (uniformStageHistories A k) hc) :
    gluedProjection (uniformStageHistories A 0) ((uniformGlobalTower A hc k).proj z)=
      gluedProjection (uniformStageHistories A k) z := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact (ih (globalUniformSuccessor A k z)).trans (globalUniformSuccessor_projection A k z)

/-- The original transport is applied to an internally constructed actual base inverse. -/
def uniformOriginalTransport (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ) :
    TowerTransport X (endpointManifold (uniformStageHistories A k) hc) :=
  transport (initialProjectionBiholomorphism A hc).symm (uniformGlobalTower A hc k)

theorem uniformOriginalTransport_zero (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) :
    (uniformOriginalTransport A hc 0).tower=(BlowupTower.refl : BlowupTower X X) := rfl

/-- Every positive transported endpoint is the SAME actual global stage. -/
def uniformOriginalPositiveTower (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ) :
    BlowupTower X (endpointManifold (uniformStageHistories A (k+1)) hc) :=
  (uniformOriginalTransport A hc (k+1)).tower

theorem uniformOriginalPositiveTower_length (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ) :
    (uniformOriginalPositiveTower A hc k).length=k+1 :=
  (length_transport (initialProjectionBiholomorphism A hc).symm
    (uniformGlobalTower A hc (k+1))).trans (uniformGlobalTower_length A hc (k+1))

theorem uniformOriginalPositiveTower_projection (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ)
    (z : endpointManifold (uniformStageHistories A (k+1)) hc) :
    (uniformOriginalPositiveTower A hc k).proj z=gluedProjection (uniformStageHistories A (k+1)) z := by
  let e := initialProjectionBiholomorphism A hc
  have hp := proj_transport e.symm (uniformGlobalTower A hc (k+1)) z
  change e.symm ((uniformOriginalPositiveTower A hc k).proj z)=(uniformGlobalTower A hc (k+1)).proj z at hp
  have hh := congrArg e hp
  rw [Diffeomorph.apply_symm_apply] at hh
  exact hh.trans (uniformGlobalTower_projection A hc (k+1) z)

theorem uniformOriginalPositiveTower_successor (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ) :
    uniformOriginalPositiveTower A hc (k+1)=BlowupTower.step
      (uniformOriginalPositiveTower A hc k) (globalUniformCentre A (k+1))
      (globalUniformSuccessor A (k+1)) (isBlowupAlong_globalUniformSuccessor A hc (k+1)) := rfl

section OriginalInput
variable (hn : 0<n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : NormalCrossings.IsSNCDivisor n E)
  (hdense : W⊆closure (W \ ⋃ H∈E,H)) (hr : ∀ x∈W,RegularAtDim (n := n) W x 1)

/-- ONLY original data produce each genuine original-base global blowup prefix. -/
def originalUniformPositiveTower (k : ℕ) :
    BlowupTower X (originalUniformStageManifold hn hW hE hdense hr (k+1)) :=
  uniformOriginalPositiveTower (originalEndpointHistories hn hW hE hdense hr)
    (originalEndpointHistories_cover hn hW hE hdense hr) k

theorem originalUniformPositiveTower_length (k : ℕ) :
    (originalUniformPositiveTower hn hW hE hdense hr k).length=k+1 :=
  uniformOriginalPositiveTower_length (originalEndpointHistories hn hW hE hdense hr)
    (originalEndpointHistories_cover hn hW hE hdense hr) k

theorem originalUniformPositiveTower_projection (k : ℕ)
    (z : originalUniformStageManifold hn hW hE hdense hr (k+1)) :
    (originalUniformPositiveTower hn hW hE hdense hr k).proj z=
      originalUniformStageProjection hn hW hE hdense hr (k+1) z :=
  uniformOriginalPositiveTower_projection (originalEndpointHistories hn hW hE hdense hr)
    (originalEndpointHistories_cover hn hW hE hdense hr) k z

end OriginalInput
end
end Hironaka.HironakaSharpActualCurveGlobalPrefixTowers
