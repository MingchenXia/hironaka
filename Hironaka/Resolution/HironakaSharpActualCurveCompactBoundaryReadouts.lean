/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveCompactAdmissibleHistory

/-! Genuine full-history boundary transport retains original positions,
born empty entries and every defaulted natural index before global stopping. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveCompactBoundaryReadouts
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen NormalCrossings IdealWeightPowers
  HironakaSharpActualCurveCompactAdmissibleHistory HironakaSharpActualCurveGlobalPrefixTests
  HironakaSharpActualCurveGlobalPrefixLocalHistories HironakaSharpActualCurveGlobalPrefixTowers
  HironakaSharpActualCurveStoppedStageTerminalRanges HironakaSharpActualCurveUniformPrefixes
  HironakaSharpActualCurveEmptyPadding HironakaSharpActualCurveBirthBoundaryOverlaps
  HironakaSharpActualCurveOriginalRecipeAtlas HironakaSharpActualCurveUniformStageAtlas
  HironakaSharpActualCurveTopologicalGluing HironakaSharpActualCurveGlobalManifold
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualCurveFullAmbientBoundary
  HironakaSharpActualCurveCompactGlobalFiniteEndpoint HironakaSharpActualCurveStoppedOpenGluing
  HironakaSharpActualCurveGluedProjection HironakaSharpActualCurveLocallyFiniteBoundary
  HironakaSharpActualCurveGlobalSharpEndpointData HironakaSharpActualCurveCompactSubsetStopping
attribute [local instance] endpointChartedSpace
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- The SAME genuine stopped full-history map transports ALL actual positions. -/
theorem stoppedPrefix_boundary_readout (M : MarkedIdeal n X) (hcoh : M.ideal.IsCoherent)
    (T : BlowupTower X Y) (hClosed : ∀ H∈(geoTransformAlong M T).E,IsClosed H)
    (k : ℕ) (hk : T.length≤k) (j : ℕ) :
    boundaryReadout (geoTransformAlong M (uniformPrefix T k).2).E j=
      (stoppedPrefixBiholomorphism T k hk) ⁻¹' boundaryReadout (geoTransformAlong M T).E j := by
  have hRead := boundaryReadout_isTowerIso M (stoppedPrefixBiholomorphism_stagewise T k hk) j
  have hId : MarkedIdeal.pullback (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) M=M :=
    ContactCanonicalAlong.pullback_id M hcoh
  rw [hId,boundaryReadout_append_identityEmptyTail M T hClosed] at hRead
  exact hRead

private theorem template_pullback_val (U : Opens X) (E : List (Set X)) :
    MarkedIdeal.pullback (Subtype.val : U → X) (geometricTemplate (univ : Set X) E)=
      geometricTemplate (X := CMfd.of (n := n) U) (univ : Set U) (E.map ((Subtype.val : U → X) ⁻¹' ·)) := by
  exact MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl
    BlowupExceptionalDivisor.pullback_unitIdeal rfl

private theorem wholeStopped_local {J : Type u} (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (N : ℕ)
    (hAll : ∀ x : X,x∈stoppedBaseOpen A (N+1)) (i : J)
    (hi : ((A.prefixTower i).append (A.tail i)).length≤N+1)
    (y : (uniformStageHistories A (N+1)).finalSpace i) :
    wholePositivePrefixTerminalBiholomorphism A hc N hAll
      (endpointLocalInclusion (uniformStageHistories A (N+1)) i y)=
        endpointLocalInclusion A i
          (stoppedPrefixBiholomorphism ((A.prefixTower i).append (A.tail i)) (N+1) hi y) := by
  exact stoppedPointMap_local A hc (N+1)
    ⟨endpointLocalInclusion (uniformStageHistories A (N+1)) i y,hAll _⟩ i hi y rfl

section OriginalInput
variable (hn : 0<n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
  (hdense : W⊆closure (W \ ⋃ H∈E,H)) (hr : ∀ x∈W,RegularAtDim (n := n) W x 1)

/-- Actual original ambient-template TEST precedes WHOLE local/global readouts. -/
theorem original_global_prefix_boundary_local (N : ℕ) (x : X) (j : ℕ) :
    let A := originalEndpointHistories hn hW hE hdense hr
    let U := A.openSet x
    endpointLocalInclusion (uniformStageHistories A (N+1)) x ⁻¹'
      boundaryReadout (geoTransformAlong (geometricTemplate (univ : Set X) E)
        (originalUniformPositiveTower hn hW hE hdense hr N)).E j=
      boundaryReadout (geoTransformAlong
        (geometricTemplate (X := CMfd.of (n := n) U) (univ : Set U) (E.map ((Subtype.val : U → X) ⁻¹' ·)))
        (uniformPrefix ((A.prefixTower x).append (A.tail x)) (N+1)).2).E j := by
  let A := originalEndpointHistories hn hW hE hdense hr
  let hc := originalEndpointHistories_cover hn hW hE hdense hr
  let U := A.openSet x
  let M := geometricTemplate (X := CMfd.of (n := n) U) (univ : Set U) (E.map ((Subtype.val : U → X) ⁻¹' ·))
  have hIso := localOriginalPrefix_isTowerIso A hc N x
  have hRead := boundaryReadout_isTowerIso M hIso j
  have hId : MarkedIdeal.pullback
      (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞) M=M :=
    ContactCanonicalAlong.pullback_id M isCoherent_unitIdeal
  rw [hId] at hRead
  have hTest := (original_curve_history_full_ambient_boundary hn hW hE hdense hr
    (originalUniformPositiveTower hn hW hE hdense hr N)
    (originalUniformPositiveTower_test hn hW hE hdense hr N)).2.1
  have hN : IsClosedSubmanifold n (univ : Set X) :=
    ⟨isClosed_univ,fun y _ => ⟨n,AnalyticIrreducibleComponents.regularAtDim_univ y⟩⟩
  have hRestrict := boundaryReadout_restrict (geometricTemplate (univ : Set X) E)
    hN isCoherent_unitIdeal U (originalUniformPositiveTower hn hW hE hdense hr N) hTest j
  rw [template_pullback_val] at hRestrict
  exact (hRead.trans (congrArg (fun B => (localOriginalPrefixBiholomorphism A hc N x) ⁻¹' B)
    hRestrict)).symm

/-- The actual entire endpoint map, not a supplied boundary comparison. -/
theorem original_whole_stopped_boundary (N : ℕ)
    (hAll : ∀ x : X,x∈stoppedBaseOpen (originalEndpointHistories hn hW hE hdense hr) (N+1))
    (j : ℕ) :
    let A := originalEndpointHistories hn hW hE hdense hr
    let hc := originalEndpointHistories_cover hn hW hE hdense hr
    boundaryReadout (geoTransformAlong (geometricTemplate (univ : Set X) E)
      (originalUniformPositiveTower hn hW hE hdense hr N)).E j=
        (wholePositivePrefixTerminalBiholomorphism A hc N hAll) ⁻¹'
          originalGluedBoundaryReadout hn hW hE hdense hr j := by
  let A := originalEndpointHistories hn hW hE hdense hr
  let hc := originalEndpointHistories_cover hn hW hE hdense hr
  ext q
  obtain ⟨i,hi,hxi⟩ := (mem_stoppedBaseOpen A (N+1)
    (gluedProjection (uniformStageHistories A (N+1)) q)).mp (hAll _)
  have hRange : q∈range (endpointLocalInclusion (uniformStageHistories A (N+1)) i) := by
    exact Eq.mpr (congrArg (fun B : Set (endpointGluedSpace (uniformStageHistories A (N+1))) => q∈B)
      (localInclusion_range (uniformStageHistories A (N+1)) i)) hxi
  obtain ⟨y,rfl⟩ := hRange
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
  have hMap := wholeStopped_local A hc N hAll i hi y
  exact (Eq.to_iff hFinite).trans ((Eq.to_iff hStop).trans
    (hOld.symm.trans (Eq.to_iff (congrArg (fun z => z∈originalGluedBoundaryReadout hn hW hE hdense hr j)
      hMap)).symm))

/-- ONLY original compact geometry gives the finite genuine ambient list,
SAME complete endpoint and EVERY exact indexed readout, including its cutoff. -/
theorem exists_original_compact_all_boundary_readouts [CompactSpace X] :
    ∃ N : ℕ,
      let G := originalGlobalSharpCurveEndpoint hn hW hE hdense hr
      let T := originalUniformPositiveTower hn hW hE hdense hr N
      ∃ e : originalUniformStageManifold hn hW hE hdense hr (N+1)
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ G.ambient,
        T.length=N+1 ∧ (∀ z,G.projection (e z)=T.proj z) ∧
        IsGeoTestTower (HironakaSharpOriginalMemberProductDomain.originalMemberProductMarked W E 1) T ∧
        IsGeoTestTower (geometricTemplate (univ : Set X) E) T ∧
        IsSNCDivisor n (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E ∧
        (∀ j,boundaryReadout (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E j=
          e ⁻¹' G.boundary j) ∧
        ∀ j,E.length+(N+1)≤j → G.boundary j=∅ := by
  let A := originalEndpointHistories hn hW hE hdense hr
  let hc := originalEndpointHistories_cover hn hW hE hdense hr
  obtain ⟨N,hN⟩ := exists_compact_stopped_open_bound A hc (univ : Set X) isCompact_univ
  have hAll : ∀ x : X,x∈stoppedBaseOpen A (N+1) := fun x => hN (mem_univ x)
  let G := originalGlobalSharpCurveEndpoint hn hW hE hdense hr
  let T := originalUniformPositiveTower hn hW hE hdense hr N
  let e : originalUniformStageManifold hn hW hE hdense hr (N+1)
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ G.ambient :=
    wholePositivePrefixTerminalBiholomorphism A hc N hAll
  have hTest := originalUniformPositiveTower_test hn hW hE hdense hr N
  have hAmbient := (original_curve_history_full_ambient_boundary hn hW hE hdense hr T hTest).2
  have hBoundary (j : ℕ) : boundaryReadout (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E j=
      e ⁻¹' G.boundary j := original_whole_stopped_boundary hn hW hE hdense hr N hAll j
  refine ⟨N,e,originalUniformPositiveTower_length hn hW hE hdense hr N,
    wholePositivePrefixTerminalBiholomorphism_projection A hc N hAll,hTest,
    hAmbient.1,hAmbient.2,hBoundary,?_⟩
  intro j hj
  have hLength : (geometricTemplate (univ : Set X) E).E.length+T.length≤j := by
    change E.length+(originalUniformPositiveTower hn hW hE hdense hr N).length≤j
    rw [originalUniformPositiveTower_length]
    exact hj
  have hPre : e ⁻¹' G.boundary j=∅ := (hBoundary j).symm.trans
    (boundaryReadout_geoTransformAlong_eq_empty (geometricTemplate (univ : Set X) E) T j hLength)
  apply Set.preimage_injective.mpr e.surjective
  change e ⁻¹' G.boundary j=e ⁻¹' (∅ : Set G.ambient)
  exact hPre

end OriginalInput
end
end Hironaka.HironakaSharpActualCurveCompactBoundaryReadouts
