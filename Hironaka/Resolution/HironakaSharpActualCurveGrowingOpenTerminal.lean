/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveOriginalGrowingHistory

/-! Genuine stopped-open curve/boundary dictionaries for the SAME growing
history and actual endpoint, before all actual compact-neighbourhood empty tails. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveGrowingOpenTerminal
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdeals MarkedIdeals.MarkedIdeal
  HomogenizedGlueingTower MemberInterLocusAlong MemberInterTowerAlong NormalCrossings IdealWeightPowers
  HironakaSharpOriginalMemberProductDomain HironakaSharpOriginalMemberProduct
  HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpActualCurveOriginalGrowingHistory HironakaLocallyFiniteResolutionSequence
  HironakaSharpActualCurveCompactBoundaryReadouts HironakaSharpActualCurveGlobalPrefixTests
  HironakaSharpActualCurveGlobalPrefixTowers HironakaSharpActualCurveOriginalRecipeAtlas
  HironakaSharpActualCurveUniformStageAtlas HironakaSharpActualCurveTopologicalGluing
  HironakaSharpActualCurveGlobalManifold HironakaSharpActualCurveGluedProjection
  HironakaSharpActualCurveCompactSubsetStopping HironakaSharpActualCurveStoppedOpenGluing
  HironakaSharpActualCurveStoppedStageTerminalRanges HironakaSharpActualCurveStrictSetOverlaps
  HironakaSharpActualCurveBirthBoundaryOverlaps HironakaSharpActualCurveLocallyFiniteBoundary
  HironakaSharpActualCurveGlobalStrictClosure HironakaSharpActualCurveLocalStationaryCentres
  HironakaSharpActualCurveGlobalSuccessorCentre HironakaSharpActualCurveUniformPrefixes
attribute [local instance] endpointChartedSpace
variable {n : ℕ} {X Y : CMfd.{u} n} {J : Type u}

/-- Closed strict sets are normalized by TRUE full-history empty suffixes. -/
theorem stoppedPrefix_strictAlong (T : BlowupTower X Y) (S : Set X) (hS : IsClosed S)
    (k : ℕ) (hk : T.length≤k) :
    strictAlong (uniformPrefix T k).2 S=
      stoppedPrefixBiholomorphism T k hk ⁻¹' strictAlong T S := by
  have h := (stoppedPrefixBiholomorphism_stagewise T k hk).strictAlong_eq S
  change strictAlong (uniformPrefix T k).2 S=_ at h
  rw [strictAlong_append,strictAlong_identityEmptyTail (isClosed_strictAlong T hS)] at h
  exact h

private theorem positiveStopped_local (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (N : ℕ)
    (q : openPreimage (uniformOriginalPositiveTower A hc N) (stoppedBaseOpen A (N+1)))
    (i : J) (hi : ((A.prefixTower i).append (A.tail i)).length≤N+1)
    (y : (uniformStageHistories A (N+1)).finalSpace i)
    (hy : endpointLocalInclusion (uniformStageHistories A (N+1)) i y=q.val) :
    (positivePrefixTerminalBiholomorphism A hc N q).val=
      endpointLocalInclusion A i
        (stoppedPrefixBiholomorphism ((A.prefixTower i).append (A.tail i)) (N+1) hi y) := by
  exact stoppedPointMap_local A hc (N+1)
    ⟨q.val,Eq.mp (congrArg (fun x => x∈stoppedBaseOpen A (N+1))
      (uniformOriginalPositiveTower_projection A hc N q.val)) q.property⟩ i hi y hy

section OriginalInput
variable (hn : 0<n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
  (hdense : W⊆closure (W \ ⋃ H∈E,H)) (hr : ∀ x∈W,RegularAtDim (n := n) W x 1)

/-- ENTIRE conventional strict curves agree on the actual stopped open. -/
theorem original_stopped_strict_curve (N : ℕ) :
    let A := originalEndpointHistories hn hW hE hdense hr
    let hc := originalEndpointHistories_cover hn hW hE hdense hr
    ∀ q : openPreimage (uniformOriginalPositiveTower A hc N) (stoppedBaseOpen A (N+1)),
      q.val∈strictTransform n (uniformOriginalPositiveTower A hc N).proj W ↔
        (positivePrefixTerminalBiholomorphism A hc N q).val∈
          strictTransform n (originalEndpointProjection hn hW hE hdense hr) W := by
  let A := originalEndpointHistories hn hW hE hdense hr
  let hc := originalEndpointHistories_cover hn hW hE hdense hr
  let T := uniformOriginalPositiveTower A hc N
  have hTest := originalUniformPositiveTower_test hn hW hE hdense hr N
  have hDom : ResolutionInvariantSpec.IsInvDomain 1 (originalMemberProductMarked W E 1) :=
    ⟨⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩,
      fun x hx => ⟨1,le_rfl,hr x hx⟩,le_rfl,
      fun _ hx => originalMemberProduct_isNonzeroAlongAt hn hE hdense hx⟩
  have hCon : strictAlong T W=strictTransform n T.proj W :=
    (N_geoTransformAlong (originalMemberProductMarked W E 1) T).symm.trans
      (carrier_eq_strictTransform _ hDom rfl T hTest)
  dsimp only
  intro q
  have hq := Eq.mp (congrArg (fun x => x∈stoppedBaseOpen A (N+1))
    (uniformOriginalPositiveTower_projection A hc N q.val)) q.property
  obtain ⟨i,hi,hxi⟩ := (mem_stoppedBaseOpen A (N+1) _).mp hq
  have hRange : q.val∈range (endpointLocalInclusion (uniformStageHistories A (N+1)) i) :=
    Eq.mpr (congrArg (fun B : Set (endpointGluedSpace (uniformStageHistories A (N+1))) => q.val∈B)
      (localInclusion_range (uniformStageHistories A (N+1)) i)) hxi
  obtain ⟨y,hy⟩ := hRange
  have hFinite := congrArg (fun B : Set ((uniformStageHistories A (N+1)).finalSpace i) => y∈B)
    (originalUniformPositiveTower_local_strict hn hW hE hdense hr N i W).symm
  have hStop := congrArg (fun B : Set ((uniformStageHistories A (N+1)).finalSpace i) => y∈B)
    (stoppedPrefix_strictAlong ((A.prefixTower i).append (A.tail i))
      ((Subtype.val : A.openSet i → X) ⁻¹' W) (hW.1.preimage continuous_subtype_val) (N+1) hi)
  let yOld := stoppedPrefixBiholomorphism ((A.prefixTower i).append (A.tail i)) (N+1) hi y
  have hOld := congrArg (fun B : Set (A.finalSpace i) => yOld∈B)
    ((preimage_strictTransform_gluedProjection A hc i W).trans
      (original_localStrictSet_eq_strictTransform hn hW hE hdense hr i).symm)
  have hMap := positiveStopped_local A hc N q i hi y hy
  exact (Eq.to_iff (congrArg (fun B => q.val∈B) hCon)).symm.trans
    (((Eq.to_iff (congrArg (fun z => z∈strictAlong T W) hy)).symm.trans
      (Eq.to_iff hFinite)).trans ((Eq.to_iff hStop).trans
        ((Eq.to_iff hOld).symm.trans (Eq.to_iff (congrArg (fun z =>
          z∈strictTransform n (originalEndpointProjection hn hW hE hdense hr) W) hMap)).symm)))

/-- EVERY original/born/defaulted boundary position on the SAME stopped open. -/
theorem original_stopped_boundary (N j : ℕ) :
    let A := originalEndpointHistories hn hW hE hdense hr
    let hc := originalEndpointHistories_cover hn hW hE hdense hr
    ∀ q : openPreimage (uniformOriginalPositiveTower A hc N) (stoppedBaseOpen A (N+1)),
      q.val∈boundaryReadout (geoTransformAlong (geometricTemplate (univ : Set X) E)
        (uniformOriginalPositiveTower A hc N)).E j ↔
      (positivePrefixTerminalBiholomorphism A hc N q).val∈
        originalGluedBoundaryReadout hn hW hE hdense hr j := by
  let A := originalEndpointHistories hn hW hE hdense hr
  let hc := originalEndpointHistories_cover hn hW hE hdense hr
  dsimp only
  intro q
  have hq := Eq.mp (congrArg (fun x => x∈stoppedBaseOpen A (N+1))
    (uniformOriginalPositiveTower_projection A hc N q.val)) q.property
  obtain ⟨i,hi,hxi⟩ := (mem_stoppedBaseOpen A (N+1) _).mp hq
  have hRange : q.val∈range (endpointLocalInclusion (uniformStageHistories A (N+1)) i) :=
    Eq.mpr (congrArg (fun B : Set (endpointGluedSpace (uniformStageHistories A (N+1))) => q.val∈B)
      (localInclusion_range (uniformStageHistories A (N+1)) i)) hxi
  obtain ⟨y,hy⟩ := hRange
  let F := boundaryReadout (geoTransformAlong (geometricTemplate (univ : Set X) E)
    (uniformOriginalPositiveTower A hc N)).E j
  have hFinite := congrArg (fun B : Set ((uniformStageHistories A (N+1)).finalSpace i) => y∈B)
    (original_global_prefix_boundary_local hn hW hE hdense hr N i j)
  let M := geometricTemplate (X := CMfd.of (n := n) (A.openSet i)) (univ : Set (A.openSet i))
    (E.map ((Subtype.val : A.openSet i → X) ⁻¹' ·))
  have hAmbient := original_localBoundary_ambient_geometry hn hW hE hdense hr i
  have hClosed : ∀ H∈(geoTransformAlong M ((A.prefixTower i).append (A.tail i))).E,IsClosed H :=
    fun H hH => hAmbient.2.1 H hH
  have hStop := congrArg (fun B : Set ((uniformStageHistories A (N+1)).finalSpace i) => y∈B)
    (stoppedPrefix_boundary_readout M isCoherent_unitIdeal
      ((A.prefixTower i).append (A.tail i)) hClosed (N+1) hi j)
  have hOld := mem_originalGluedBoundaryReadout_iff hn hW hE hdense hr i j
    (stoppedPrefixBiholomorphism ((A.prefixTower i).append (A.tail i)) (N+1) hi y)
  have hMap := positiveStopped_local A hc N q i hi y hy
  exact ((Eq.to_iff (congrArg (fun z => z∈F) hy)).symm.trans (Eq.to_iff hFinite)).trans
    ((Eq.to_iff hStop).trans (hOld.symm.trans (Eq.to_iff (congrArg (fun z =>
      z∈originalGluedBoundaryReadout hn hW hE hdense hr j) hMap)).symm))

/-- Ordinary compactness constructs one actual stopped neighbourhood on
which EVERY genuine finite later tail has only empty centres. -/
theorem originalGrowingSeq_compact_open_empty_tails (K : Set X) (hK : IsCompact K) :
    let A := originalEndpointHistories hn hW hE hdense hr
    let s := originalGrowingSeq hn hW hE hdense hr
    ∃ N : ℕ,K⊆stoppedBaseOpen A (N+1) ∧ ∀ r : ℕ,
      ResolutionInvariantExt.IsEmptyTower
        (restrict (openPreimage (s.stage (N+1)).2 (stoppedBaseOpen A (N+1)))
          (HironakaLocallyFiniteResolutionSequence.tailTower s (N+1) r)) := by
  let A := originalEndpointHistories hn hW hE hdense hr
  let hc := originalEndpointHistories_cover hn hW hE hdense hr
  let s := originalGrowingSeq hn hW hE hdense hr
  obtain ⟨N,hN⟩ := exists_compact_stopped_open_bound A hc K hK
  have hAvoid (k : ℕ) (hk : N+1≤k) :
      Disjoint (stepCentre s k) ((s.stage k).2.proj ⁻¹' (stoppedBaseOpen A (N+1) : Set X)) := by
    apply disjoint_left.mpr
    intro y hy hyU
    have hImg := centreImage_uniformGrowingSeq A hc k
    have hMem : (s.stage k).2.proj y∈centreImage s k := ⟨y,hy,rfl⟩
    obtain ⟨z,hz,hp⟩ := Eq.mp (congrArg (fun B => (s.stage k).2.proj y∈B) hImg) hMem
    exact disjoint_left.mp
      (globalCentres_avoid_subset_of_stopped_open A (stoppedBaseOpen A (N+1)) (N+1)
        Subset.rfl k hk) hz (Eq.mpr (congrArg (fun x => x∈stoppedBaseOpen A (N+1)) hp) hyU)
  refine ⟨N,hN,fun r => ?_⟩
  exact (RestrictEmptyTower.isEmptyTower_restrict_iff _ _).mpr
    (centresAvoid_tailTower s (N+1) (stoppedBaseOpen A (N+1)) hAvoid r)

end OriginalInput
end
end Hironaka.HironakaSharpActualCurveGrowingOpenTerminal
