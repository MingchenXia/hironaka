/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveGrowingOpenTerminal

/-! ONLY original curve geometry constructs the whole genuine locally finite
sharp history and SAME full endpoint, retaining every actual position/readout. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveLocallyFiniteSharpHistory
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  ResolutionInvariantSeq HironakaLocallyFiniteResolutionSequence HironakaSharpOriginalMemberProductDomain
  HironakaSharpActualCurveOriginalGrowingHistory HironakaSharpActualCurveGrowingOpenTerminal
  HironakaSharpActualCurveGlobalSharpEndpointData HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpActualCurveOriginalRecipeAtlas HironakaSharpActualCurveGlobalPrefixTowers
  HironakaSharpActualCurveCompactSubsetStopping HironakaSharpActualCurveStoppedOpenGluing
  HironakaSharpActualCurveBirthBoundaryOverlaps
variable {n : ℕ} {X : CMfd.{u} n}

/-- The actual entire projection preimage, with openness from actual holomorphicity. -/
def endpointPreimageOpen {W : Set X} {E : List (Set X)}
    (G : GlobalSharpCurveEndpoint W E) (U : Opens X) : Opens G.ambient :=
  ⟨G.projection ⁻¹' (U : Set X),U.isOpen.preimage G.holomorphic.continuous⟩

/-- WHOLE sharp locally finite history existence from ONLY original geometry.
Explicit constructor equalities retain the actual producer recipe. -/
theorem exists_original_locallyFinite_sharp_history (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W⊆closure (W \ ⋃ H∈E,H)) (hr : ∀ x∈W,RegularAtDim (n := n) W x 1) :
    ∃ (s : GrowingSeq X) (G : GlobalSharpCurveEndpoint W E),
      s=originalGrowingSeq hn hW hE hdense hr ∧
      G=originalGlobalSharpCurveEndpoint hn hW hE hdense hr ∧
      (∀ k : ℕ,(s.stage k).2.length=k ∧
        IsGeoTestTower (originalMemberProductMarked W E 1) (s.stage k).2 ∧
        IsGeoTestTower (geometricTemplate (univ : Set X) E) (s.stage k).2 ∧
        IsSNCDivisor n (geoTransformAlong (geometricTemplate (univ : Set X) E) (s.stage k).2).E) ∧
      LocallyFinite (centreImage s) ∧ IsClosed (⋃ k,centreImage s k) ∧
      ∀ K : Set X,IsCompact K → ∃ (N : ℕ) (U : Opens X),K⊆U ∧
        ∃ e : CMfd.of (n := n) (openPreimage (s.stage (N+1)).2 U)
          ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
            CMfd.of (n := n) (endpointPreimageOpen G U),
          (∀ q,G.projection (e q).val=(s.stage (N+1)).2.proj q.val) ∧
          (∀ q,q.val∈strictTransform n (s.stage (N+1)).2.proj W ↔
            (e q).val∈strictTransform n G.projection W) ∧
          (∀ (j : ℕ) q,q.val∈boundaryReadout (geoTransformAlong
              (geometricTemplate (univ : Set X) E) (s.stage (N+1)).2).E j ↔
            (e q).val∈G.boundary j) ∧
          ∀ r : ℕ,ResolutionInvariantExt.IsEmptyTower
            (restrict (openPreimage (s.stage (N+1)).2 U)
              (HironakaLocallyFiniteResolutionSequence.tailTower s (N+1) r)) := by
  let A := originalEndpointHistories hn hW hE hdense hr
  let hc := originalEndpointHistories_cover hn hW hE hdense hr
  let s := originalGrowingSeq hn hW hE hdense hr
  let G := originalGlobalSharpCurveEndpoint hn hW hE hdense hr
  refine ⟨s,G,rfl,rfl,?_,locallyFinite_originalGrowingSeq_centreImage hn hW hE hdense hr,
    isClosed_originalGrowingSeq_centreImage_union hn hW hE hdense hr,?_⟩
  · intro k
    exact ⟨uniformGrowingSeq_length A hc k,originalGrowingSeq_test hn hW hE hdense hr k,
      originalGrowingSeq_ambient_test hn hW hE hdense hr k⟩
  · intro K hK
    obtain ⟨N,hN,hTails⟩ := originalGrowingSeq_compact_open_empty_tails hn hW hE hdense hr K hK
    let U := stoppedBaseOpen A (N+1)
    let e : CMfd.of (n := n) (openPreimage (s.stage (N+1)).2 U)
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
          CMfd.of (n := n) (endpointPreimageOpen G U) :=
      positivePrefixTerminalBiholomorphism A hc N
    refine ⟨N,U,hN,e,?_,?_,?_,hTails⟩
    · exact positivePrefixTerminalBiholomorphism_projection A hc N
    · exact original_stopped_strict_curve hn hW hE hdense hr N
    · exact fun j => original_stopped_boundary hn hW hE hdense hr N j

end
end Hironaka.HironakaSharpActualCurveLocallyFiniteSharpHistory
