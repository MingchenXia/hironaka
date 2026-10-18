/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveStoppedOpenGluing
import Hironaka.Resolution.HironakaSharpActualCurveGlobalPrefixTowers

/-! Finite chosen covers of ordinary compact subsets supply real stopping
bounds and SAME original-base finite-prefix terminal maps. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveCompactSubsetStopping
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  HironakaSharpActualCurveStoppedOpenGluing HironakaSharpActualCurveUniformStageAtlas
  HironakaSharpActualCurveTopologicalGluing HironakaSharpActualCurveGlobalManifold
  HironakaSharpActualCurveGluedProjection HironakaSharpActualCurveGlobalPrefixTowers
  HironakaSharpActualCurveGlobalSuccessorCentre HironakaSharpActualCurveLocalStationaryCentres
  HironakaSharpActualCurveOriginalRecipeAtlas BlowupTowerIsoTail
attribute [local instance] endpointChartedSpace
variable {n : ℕ} {X : CMfd.{u} n} {J : Type u}

/-- The maximum is taken ONLY over an actual finite subcover, never the original infinite atlas. -/
theorem exists_compact_stopped_open_bound (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (K : Set X) (hK : IsCompact K) :
    ∃ N : ℕ,K⊆stoppedBaseOpen A (N+1) := by
  have hCover : K⊆⋃ k : ℕ,(stoppedBaseOpen A k : Set X) := by
    intro x _hx
    obtain ⟨k,hk⟩ := stoppedBaseOpen_cover A hc x
    exact mem_iUnion.mpr ⟨k,hk⟩
  obtain ⟨t,ht⟩ := hK.elim_finite_subcover (fun k : ℕ => (stoppedBaseOpen A k : Set X))
    (fun k => (stoppedBaseOpen A k).isOpen) hCover
  refine ⟨t.sup id,?_⟩
  intro x hx
  obtain ⟨k,hk⟩ := mem_iUnion.mp (ht hx)
  obtain ⟨hkt,hxk⟩ := mem_iUnion.mp hk
  exact stoppedBaseOpen_mono A ((Finset.le_sup (f := id) hkt).trans (Nat.le_succ _)) hxk

/-- EVERY later actual centre avoids the ENTIRE preimage of the ordinary compact subset. -/
theorem globalCentres_avoid_subset_of_stopped_open (A : ActualEndpointHistories X J)
    (K : Set X) (N : ℕ) (hKN : K⊆stoppedBaseOpen A N) (k : ℕ) (hNk : N≤k) :
    Disjoint (globalUniformCentre A k) ((gluedProjection (uniformStageHistories A k)) ⁻¹' K) := by
  apply disjoint_left.mpr
  intro q hC hqK
  obtain ⟨i,hi,hqi⟩ := (mem_stoppedBaseOpen A N _).mp (hKN hqK)
  exact disjoint_left.mp (globalUniformCentre_disjoint_preimage_open A k i (hi.trans hNk)) hC hqi

private theorem positive_prefix_stopped_open_eq (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (N : ℕ) :
    openPreimage (uniformOriginalPositiveTower A hc N) (stoppedBaseOpen A (N+1))=
      stoppedStageOpen A hc (N+1) := by
  apply Opens.ext
  ext z
  change (uniformOriginalPositiveTower A hc N).proj z∈stoppedBaseOpen A (N+1) ↔
    gluedProjection (uniformStageHistories A (N+1)) z∈stoppedBaseOpen A (N+1)
  rw [uniformOriginalPositiveTower_projection]

/-- SAME actual positive prefix and SAME retained terminal endpoint, over a genuine original open. -/
def positivePrefixTerminalBiholomorphism (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (N : ℕ) :
    CMfd.of (n := n) (openPreimage (uniformOriginalPositiveTower A hc N) (stoppedBaseOpen A (N+1)))
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (stoppedTerminalOpen A hc (N+1)) :=
  (opensCongr (positive_prefix_stopped_open_eq A hc N)).trans (stoppedOpenBiholomorphism A hc (N+1))

theorem positivePrefixTerminalBiholomorphism_projection (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (N : ℕ)
    (z : openPreimage (uniformOriginalPositiveTower A hc N) (stoppedBaseOpen A (N+1))) :
    gluedProjection A (positivePrefixTerminalBiholomorphism A hc N z).val=
      (uniformOriginalPositiveTower A hc N).proj z.val := by
  exact (stoppedOpenBiholomorphism_projection A hc (N+1)
    (opensCongr (positive_prefix_stopped_open_eq A hc N) z)).trans
      (uniformOriginalPositiveTower_projection A hc N z.val).symm

theorem positivePrefixTerminalBiholomorphism_symm_projection (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (N : ℕ)
    (w : stoppedTerminalOpen A hc (N+1)) :
    (uniformOriginalPositiveTower A hc N).proj (positivePrefixTerminalBiholomorphism A hc N |>.symm w).val=
      gluedProjection A w.val := by
  let e := positivePrefixTerminalBiholomorphism A hc N
  have hh := (positivePrefixTerminalBiholomorphism_projection A hc N (e.symm w)).symm
  exact hh.trans (congrArg (fun q => gluedProjection A q.val) (e.apply_symm_apply w))

/-- ENTIRE subset preimages, without inventing a manifold on a nonopen compact subset. -/
theorem positivePrefixTerminalBiholomorphism_preimage (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (N : ℕ) (K : Set X) :
    (positivePrefixTerminalBiholomorphism A hc N) ⁻¹'
      {w : stoppedTerminalOpen A hc (N+1) | gluedProjection A w.val∈K}=
      {z : openPreimage (uniformOriginalPositiveTower A hc N) (stoppedBaseOpen A (N+1)) |
        (uniformOriginalPositiveTower A hc N).proj z.val∈K} := by
  ext z
  change gluedProjection A (positivePrefixTerminalBiholomorphism A hc N z).val∈K ↔
    (uniformOriginalPositiveTower A hc N).proj z.val∈K
  rw [positivePrefixTerminalBiholomorphism_projection]

section OriginalInput
variable (hn : 0<n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : NormalCrossings.IsSNCDivisor n E)
  (hdense : W⊆closure (W \ ⋃ H∈E,H)) (hr : ∀ x∈W,RegularAtDim (n := n) W x 1)

def originalPositivePrefixTerminalBiholomorphism (N : ℕ) :
    let A := originalEndpointHistories hn hW hE hdense hr
    let hc := originalEndpointHistories_cover hn hW hE hdense hr
    CMfd.of (n := n) (openPreimage (originalUniformPositiveTower hn hW hE hdense hr N)
      (stoppedBaseOpen A (N+1))) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (stoppedTerminalOpen A hc (N+1)) :=
  positivePrefixTerminalBiholomorphism (originalEndpointHistories hn hW hE hdense hr)
    (originalEndpointHistories_cover hn hW hE hdense hr) N

/-- The actual finite bound and ENTIRE later centre avoidance are proved, not supplied. -/
theorem original_compact_subset_finite_stopping (K : Set X) (hK : IsCompact K) :
    let A := originalEndpointHistories hn hW hE hdense hr
    ∃ N : ℕ,K⊆stoppedBaseOpen A (N+1) ∧
      (originalUniformPositiveTower hn hW hE hdense hr N).length=N+1 ∧
      (∀ k,N+1≤k → Disjoint (originalUniformCentre hn hW hE hdense hr k)
        ((originalUniformStageProjection hn hW hE hdense hr k) ⁻¹' K)) ∧
      ∀ z : openPreimage (originalUniformPositiveTower hn hW hE hdense hr N)
          (stoppedBaseOpen A (N+1)),
        originalEndpointProjection hn hW hE hdense hr
            (originalPositivePrefixTerminalBiholomorphism hn hW hE hdense hr N z).val=
          (originalUniformPositiveTower hn hW hE hdense hr N).proj z.val := by
  let A := originalEndpointHistories hn hW hE hdense hr
  let hc := originalEndpointHistories_cover hn hW hE hdense hr
  obtain ⟨N,hN⟩ := exists_compact_stopped_open_bound A hc K hK
  refine ⟨N,hN,originalUniformPositiveTower_length hn hW hE hdense hr N,?_,?_⟩
  · intro k hk
    exact globalCentres_avoid_subset_of_stopped_open A K (N+1) hN k hk
  · intro z
    exact positivePrefixTerminalBiholomorphism_projection A hc N z

end OriginalInput

end
end Hironaka.HironakaSharpActualCurveCompactSubsetStopping
