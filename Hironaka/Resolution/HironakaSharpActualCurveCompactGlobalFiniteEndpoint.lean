/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveCompactSubsetStopping
import Hironaka.Resolution.HironakaSharpActualCurveGlobalSharpEndpointData

/-! Ordinary ambient compactness supplies an actual finite global prefix
coupled by a genuine whole biholomorphism to the SAME full sharp endpoint. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveCompactGlobalFiniteEndpoint
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupRestrictOpen
  HironakaSharpActualCurveCompactSubsetStopping HironakaSharpActualCurveStoppedOpenGluing
  HironakaSharpActualCurveUniformStageAtlas HironakaSharpActualCurveTopologicalGluing
  HironakaSharpActualCurveGlobalManifold HironakaSharpActualCurveGluedProjection
  HironakaSharpActualCurveGlobalPrefixTowers HironakaSharpActualCurveOriginalRecipeAtlas
  HironakaSharpActualCurveGlobalSuccessorCentre HironakaSharpActualCurveGlobalSharpEndpointData
attribute [local instance] endpointChartedSpace
variable {n : ℕ} {X : CMfd.{u} n} {J : Type u}

private def wholeOpenBiholomorphism (M : CMfd.{u} n) (U : Opens M) (hU : ∀ x : M,x∈U) :
    M ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U where
  toEquiv := {
    toFun := fun x => ⟨x,hU x⟩
    invFun := Subtype.val
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  contMDiff_toFun := contMDiff_opens_mk contMDiff_id hU
  contMDiff_invFun := contMDiff_subtype_val

/-- Both genuine whole-open identifications have literal underlying point maps. -/
def wholePositivePrefixTerminalBiholomorphism (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (N : ℕ)
    (hAll : ∀ x : X,x∈stoppedBaseOpen A (N+1)) :
    endpointManifold (uniformStageHistories A (N+1)) hc
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ endpointManifold A hc :=
  (wholeOpenBiholomorphism (endpointManifold (uniformStageHistories A (N+1)) hc)
    (openPreimage (uniformOriginalPositiveTower A hc N) (stoppedBaseOpen A (N+1)))
    (fun z => hAll ((uniformOriginalPositiveTower A hc N).proj z))).trans
      ((positivePrefixTerminalBiholomorphism A hc N).trans
        (wholeOpenBiholomorphism (endpointManifold A hc) (stoppedTerminalOpen A hc (N+1))
          (fun z => hAll (gluedProjection A z))).symm)

theorem wholePositivePrefixTerminalBiholomorphism_projection (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (N : ℕ)
    (hAll : ∀ x : X,x∈stoppedBaseOpen A (N+1))
    (z : endpointManifold (uniformStageHistories A (N+1)) hc) :
    gluedProjection A (wholePositivePrefixTerminalBiholomorphism A hc N hAll z)=
      (uniformOriginalPositiveTower A hc N).proj z :=
  positivePrefixTerminalBiholomorphism_projection A hc N ⟨z,hAll _⟩

section OriginalInput
variable (hn : 0<n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : NormalCrossings.IsSNCDivisor n E)
  (hdense : W⊆closure (W \ ⋃ H∈E,H)) (hr : ∀ x∈W,RegularAtDim (n := n) W x 1)

/-- The full sharp endpoint is an internally constructed OUTPUT, genuinely
coupled to the SAME finite original-base blowup tower, never a supplied certificate. -/
theorem exists_original_compact_finite_sharp_endpoint [CompactSpace X] :
    ∃ (N : ℕ) (Y : CMfd.{u} n) (T : BlowupTower X Y) (G : GlobalSharpCurveEndpoint W E)
      (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ G.ambient),
      T.length=N+1 ∧ (∀ z : Y,G.projection (e z)=T.proj z) ∧
        ∀ k,N+1≤k → originalUniformCentre hn hW hE hdense hr k=∅ := by
  let A := originalEndpointHistories hn hW hE hdense hr
  let hc := originalEndpointHistories_cover hn hW hE hdense hr
  obtain ⟨N,hN⟩ := exists_compact_stopped_open_bound A hc (univ : Set X) isCompact_univ
  have hAll : ∀ x : X,x∈stoppedBaseOpen A (N+1) := fun x => hN (mem_univ x)
  let Y := endpointManifold (uniformStageHistories A (N+1)) hc
  let G := originalGlobalSharpCurveEndpoint hn hW hE hdense hr
  refine ⟨N,Y,uniformOriginalPositiveTower A hc N,G,
    wholePositivePrefixTerminalBiholomorphism A hc N hAll,
    uniformOriginalPositiveTower_length A hc N,?_,?_⟩
  · intro z
    exact wholePositivePrefixTerminalBiholomorphism_projection A hc N hAll z
  · intro k hk
    have hh := globalCentres_avoid_subset_of_stopped_open A (univ : Set X) (N+1) hN k hk
    apply Subset.antisymm ?_ (empty_subset _)
    intro z hz
    exact disjoint_left.mp hh hz (mem_univ _)

end OriginalInput
end
end Hironaka.HironakaSharpActualCurveCompactGlobalFiniteEndpoint
