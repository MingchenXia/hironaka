/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveStoppedOpenGluing

/-! Genuine full-history predecessor uniqueness gives the actual terminal
square for SAME local and global successors, retaining all empty steps. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveStoppedSuccessorNaturality
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerIsomorphism
  HironakaSharpActualCurveUniformPrefixes HironakaSharpActualCurveUniformSuccessorComparison
  HironakaSharpActualCurveUniformStageAtlas HironakaSharpActualCurveEmptyPadding
  HironakaSharpActualCurveStoppedStageTerminalRanges HironakaSharpActualCurveFiniteRecipeComparison
  HironakaSharpActualCurveTopologicalGluing HironakaSharpActualCurveGluedProjection
  HironakaSharpActualCurveGlobalManifold HironakaSharpActualCurveGlobalSuccessorMap
  HironakaSharpActualCurveStoppedOpenGluing HironakaSharpActualCurveOriginalRecipeAtlas
attribute [local instance] endpointChartedSpace
variable {n : ℕ} {X Y : CMfd.{u} n} {J : Type u}

theorem stoppedPrefix_successor_square (T : BlowupTower X Y) (k : ℕ) (hk : T.length≤k)
    (z : (uniformPrefix T (k+1)).1) :
    stoppedPrefixBiholomorphism T k hk ((actualUniformSuccessor T k).map z)=
      stoppedPrefixBiholomorphism T (k+1) (by omega) z := by
  have hTop := stoppedPrefixBiholomorphism_stagewise T (k+1) (by omega)
  rw [(actualUniformSuccessor T k).step_eq] at hTop
  have hCount : k+1-T.length=(k-T.length)+1 := by omega
  rw [hCount] at hTop
  obtain ⟨χ,hPrev,hSquare,_hCentre⟩ := hTop.step_inv
  have hSame := actual_tower_comparison_unique hPrev (stoppedPrefixBiholomorphism_stagewise T k hk)
  have hPoint := hSquare z
  change stoppedPrefixBiholomorphism T (k+1) (by omega) z=χ ((actualUniformSuccessor T k).map z) at hPoint
  rw [hSame] at hPoint
  exact hPoint.symm

/-- Genuine original projection membership constructs BOTH stopped-map domains internally. -/
theorem stoppedOpen_successor_square (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ)
    (q : endpointManifold (uniformStageHistories A (k+1)) hc)
    (hq : gluedProjection (uniformStageHistories A (k+1)) q∈stoppedBaseOpen A k) :
    (stoppedOpenBiholomorphism A hc k ⟨globalUniformSuccessor A k q,by
      change gluedProjection (uniformStageHistories A k) (globalUniformSuccessor A k q)∈stoppedBaseOpen A k
      exact (globalUniformSuccessor_projection A k q).symm ▸ hq⟩).val=
      (stoppedOpenBiholomorphism A hc (k+1)
        ⟨q,stoppedBaseOpen_mono A (Nat.le_succ k) hq⟩).val := by
  let q₀ : stoppedStageOpen A hc k := ⟨globalUniformSuccessor A k q,by
    change gluedProjection (uniformStageHistories A k) (globalUniformSuccessor A k q)∈stoppedBaseOpen A k
    exact (globalUniformSuccessor_projection A k q).symm ▸ hq⟩
  let q₁ : stoppedStageOpen A hc (k+1) := ⟨q,stoppedBaseOpen_mono A (Nat.le_succ k) hq⟩
  change stoppedPointMap A hc k q₀=stoppedPointMap A hc (k+1) q₁
  obtain ⟨i,hi,hqi⟩ := (mem_stoppedBaseOpen A k _).mp hq
  have hRange : q∈range (endpointLocalInclusion (uniformStageHistories A (k+1)) i) := by
    rw [localInclusion_range]
    exact hqi
  obtain ⟨y,hy⟩ := hRange
  have hRep₀ : endpointLocalInclusion (uniformStageHistories A k) i (localUniformSuccessor A k i y)=
      globalUniformSuccessor A k q :=
    (globalUniformSuccessor_local A k i y).symm.trans (congrArg (globalUniformSuccessor A k) hy)
  have hLeft := stoppedPointMap_local A hc k q₀ i hi (localUniformSuccessor A k i y) hRep₀
  have hRight := stoppedPointMap_local A hc (k+1) q₁ i (hi.trans (Nat.le_succ k)) y hy
  exact hLeft.trans ((congrArg (endpointLocalInclusion A i)
    (stoppedPrefix_successor_square ((A.prefixTower i).append (A.tail i)) k hi y)).trans hRight.symm)

section OriginalInput
variable (hn : 0<n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : NormalCrossings.IsSNCDivisor n E)
  (hdense : W⊆closure (W \ ⋃ H∈E,H)) (hr : ∀ x∈W,RegularAtDim (n := n) W x 1)

/-- ONLY original inputs, actual point-chart membership and a genuine stage supply the square. -/
theorem originalStopped_successor_square (x : X) (r : ℕ) :
    let A := originalEndpointHistories hn hW hE hdense hr
    let hc := originalEndpointHistories_cover hn hW hE hdense hr
    let k := ((A.prefixTower x).append (A.tail x)).length+r
    ∀ (q : endpointManifold (uniformStageHistories A (k+1)) hc)
      (hq : gluedProjection (uniformStageHistories A (k+1)) q∈A.openSet x),
      let hqU := (mem_stoppedBaseOpen A k _).mpr ⟨x,by omega,hq⟩
      (stoppedOpenBiholomorphism A hc k ⟨globalUniformSuccessor A k q,by
        change gluedProjection (uniformStageHistories A k) (globalUniformSuccessor A k q)∈stoppedBaseOpen A k
        exact (globalUniformSuccessor_projection A k q).symm ▸ hqU⟩).val=
        (stoppedOpenBiholomorphism A hc (k+1)
          ⟨q,stoppedBaseOpen_mono A (Nat.le_succ k) hqU⟩).val := by
  dsimp only
  intro q hq
  exact stoppedOpen_successor_square (originalEndpointHistories hn hW hE hdense hr)
    (originalEndpointHistories_cover hn hW hE hdense hr) _ q
    ((mem_stoppedBaseOpen (originalEndpointHistories hn hW hE hdense hr) _ _).mpr ⟨x,by omega,hq⟩)

end OriginalInput

end
end Hironaka.HironakaSharpActualCurveStoppedSuccessorNaturality
