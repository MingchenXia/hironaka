/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveGrowingGoodPreservation

/-! Genuine adapted coordinates and finite SNC/transverse predicates on the
SAME actual stopped-prefix chart, not just full endpoint readout equalities. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveStoppedPrefixSharpGeometry
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings NormalCrossingsInvariance HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpActualCurveGlobalPrefixTowers HironakaSharpActualCurveOriginalRecipeAtlas
  HironakaSharpActualCurveUniformStageAtlas HironakaSharpActualCurveTopologicalGluing
  HironakaSharpActualCurveGlobalManifold HironakaSharpActualCurveCompactSubsetStopping
  HironakaSharpActualCurveStoppedOpenGluing HironakaSharpActualCurveGrowingOpenTerminal
  HironakaSharpActualCurveBirthBoundaryOverlaps HironakaSharpActualCurveGlobalBoundaryCoordinates
  HironakaSharpActualCurveOriginalGrowingHistory HironakaSharpActualCurveGrowingGoodPreservation
  HironakaSharpActualCurveGlobalSharpEndpointData HironakaSharpActualCurveLocallyFiniteSharpHistory
attribute [local instance] endpointChartedSpace
variable {n : ℕ} {X : CMfd.{u} n}
section OriginalInput
variable (hn : 0<n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
  (hdense : W⊆closure (W \ ⋃ H∈E,H)) (hr : ∀ x∈W,RegularAtDim (n := n) W x 1)

/-- The ENTIRE actual prefix projection preimage of the true stopped base open. -/
def originalStoppedPrefixOpen (N : ℕ) : Opens (originalUniformStageManifold hn hW hE hdense hr (N+1)) :=
  openPreimage (originalUniformPositiveTower hn hW hE hdense hr N)
    (stoppedBaseOpen (originalEndpointHistories hn hW hE hdense hr) (N+1))

/-- The actual conventional strict curve on the same actual open manifold. -/
def originalStoppedPrefixCurve (N : ℕ) : Set (originalStoppedPrefixOpen hn hW hE hdense hr N) :=
  (Subtype.val : originalStoppedPrefixOpen hn hW hE hdense hr N →
    originalUniformStageManifold hn hW hE hdense hr (N+1)) ⁻¹'
      strictTransform n (originalUniformPositiveTower hn hW hE hdense hr N).proj W

/-- The ENTIRE literal original/born finite ordered list, including empty members. -/
def originalStoppedPrefixBoundary (N : ℕ) : List (Set (originalStoppedPrefixOpen hn hW hE hdense hr N)) :=
  (geoTransformAlong (geometricTemplate (univ : Set X) E)
    (originalUniformPositiveTower hn hW hE hdense hr N)).E.map
      ((Subtype.val : originalStoppedPrefixOpen hn hW hE hdense hr N →
        originalUniformStageManifold hn hW hE hdense hr (N+1)) ⁻¹' ·)

private theorem stoppedPrefix_readout (N j : ℕ) :
    boundaryReadout (originalStoppedPrefixBoundary hn hW hE hdense hr N) j=
      (Subtype.val : originalStoppedPrefixOpen hn hW hE hdense hr N →
        originalUniformStageManifold hn hW hE hdense hr (N+1)) ⁻¹'
        boundaryReadout (geoTransformAlong (geometricTemplate (univ : Set X) E)
          (originalUniformPositiveTower hn hW hE hdense hr N)).E j :=
  boundaryReadout_map_preimage _ _ _

/-- True e and both entire readout dictionaries supply an actual chart frame. -/
theorem original_stopped_prefix_coordinates (N : ℕ)
    (q : originalStoppedPrefixOpen hn hW hE hdense hr N)
    (hq : q∈originalStoppedPrefixCurve hn hW hE hdense hr N) :
    ∃ (S₀ : Finset (Fin n)) (S : ℕ → Finset (Fin n)),
      IsCoordinateFamilyAt n (fun o : Option ℕ => o.elim
        (originalStoppedPrefixCurve hn hW hE hdense hr N)
        (fun j => boundaryReadout (originalStoppedPrefixBoundary hn hW hE hdense hr N) j))
        (fun o => o.elim S₀ S) q ∧
      ∀ j,q∈boundaryReadout (originalStoppedPrefixBoundary hn hW hE hdense hr N) j →
        (S j).card=1 ∧ Disjoint (S j) S₀ := by
  let A := originalEndpointHistories hn hW hE hdense hr
  let hc := originalEndpointHistories_cover hn hW hE hdense hr
  let G := originalGlobalSharpCurveEndpoint hn hW hE hdense hr
  let U := stoppedBaseOpen A (N+1)
  let e : CMfd.of (n := n) (originalStoppedPrefixOpen hn hW hE hdense hr N)
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (endpointPreimageOpen G U) := positivePrefixTerminalBiholomorphism A hc N
  have hCurve (p : originalStoppedPrefixOpen hn hW hE hdense hr N) :
      p∈originalStoppedPrefixCurve hn hW hE hdense hr N ↔
        (e p).val∈strictTransform n G.projection W :=
    original_stopped_strict_curve hn hW hE hdense hr N p
  have hBoundary (j : ℕ) (p : originalStoppedPrefixOpen hn hW hE hdense hr N) :
      p∈boundaryReadout (originalStoppedPrefixBoundary hn hW hE hdense hr N) j ↔
        (e p).val∈G.boundary j :=
    (Eq.to_iff (congrArg (fun B => p∈B) (stoppedPrefix_readout hn hW hE hdense hr N j))).trans
      (original_stopped_boundary hn hW hE hdense hr N j p)
  obtain ⟨S₀,S,hFrame,hSets⟩ := G.transverse_coordinates (e q).val ((hCurve q).mp hq)
  have hOpen := pullsBackCoordinates_val (endpointPreimageOpen G U)
    (fun o : Option ℕ => o.elim (strictTransform n G.projection W) G.boundary)
    (fun o => o.elim S₀ S) (e q) hFrame
  have hPulled := MarkedIdealTowerTransport.pullsBackCoordinates e _ _ q hOpen
  refine ⟨S₀,S,?_,fun j hj => hSets j ((hBoundary j q).mp hj)⟩
  apply NormalCrossingsInvariance.IsCoordinateFamilyAt.reindex hPulled id
  · intro o
    ext p
    cases o with
    | none => exact hCurve p
    | some j => exact hBoundary j p
  · intro o
    rfl

/-- Actual finite-list SNC and transversality on the actual prefix chart. -/
theorem original_stopped_prefix_sharp (N : ℕ) :
    IsClosedSubmanifold n (originalStoppedPrefixCurve hn hW hE hdense hr N) ∧
    IsSNCDivisor n (originalStoppedPrefixBoundary hn hW hE hdense hr N) ∧
    IsTransverse n (originalStoppedPrefixCurve hn hW hE hdense hr N)
      (originalStoppedPrefixBoundary hn hW hE hdense hr N) := by
  let A := originalEndpointHistories hn hW hE hdense hr
  let hc := originalEndpointHistories_cover hn hW hE hdense hr
  let G := originalGlobalSharpCurveEndpoint hn hW hE hdense hr
  let U := stoppedBaseOpen A (N+1)
  let e : CMfd.of (n := n) (originalStoppedPrefixOpen hn hW hE hdense hr N)
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (endpointPreimageOpen G U) := positivePrefixTerminalBiholomorphism A hc N
  have hCurve : originalStoppedPrefixCurve hn hW hE hdense hr N=
      e ⁻¹' ((Subtype.val : endpointPreimageOpen G U → G.ambient) ⁻¹'
        strictTransform n G.projection W) := by
    ext p
    exact original_stopped_strict_curve hn hW hE hdense hr N p
  have hTarget := BlowupRestrictOpen.isClosedSubmanifold_preimage_val G.strict_smooth (endpointPreimageOpen G U)
  have hSource := (MarkedIdealTowerTransport.isClosedSubmanifold_preimage_iff e).mpr hTarget
  refine ⟨Eq.mpr (congrArg (fun B => IsClosedSubmanifold n B) hCurve) hSource,?_,?_⟩
  · exact isSNCDivisor_map_preimage (pullsBackCoordinates_val
      (originalStoppedPrefixOpen hn hW hE hdense hr N)) continuous_subtype_val
        (originalGrowingSeq_ambient_test hn hW hE hdense hr (N+1)).2
  · intro q hq
    obtain ⟨S₀,S,hCoord,hSets⟩ := original_stopped_prefix_coordinates hn hW hE hdense hr N q hq
    let F := originalStoppedPrefixBoundary hn hW hE hdense hr N
    refine ⟨S₀,fun i => S i.val,?_,?_⟩
    · apply NormalCrossingsInvariance.IsCoordinateFamilyAt.reindex hCoord (Option.map Fin.val)
      · intro o
        cases o with
        | none => rfl
        | some i => exact (List.getD_eq_get F ∅ i).symm
      · intro o
        cases o <;> rfl
    · intro i hi
      exact hSets i.val (Eq.mpr (congrArg (fun B => q∈B) (List.getD_eq_get F ∅ i)) hi)

/-- Genuine finite sharp-prefix geometry near EVERY compact, together with
EVERY prefix's actual original-good isomorphism and the same whole π-square. -/
theorem original_compact_sharp_prefix_and_good :
    (∀ k,IsIsomorphismOver n ((originalGrowingSeq hn hW hE hdense hr).stage k).2.proj
      (HironakaSharpOriginalMultiBoundaryBadLocus.originalGoodLocus (n := n) W E)) ∧
    ∀ K : Set X,IsCompact K → ∃ N : ℕ,
      K⊆stoppedBaseOpen (originalEndpointHistories hn hW hE hdense hr) (N+1) ∧
      IsClosedSubmanifold n (originalStoppedPrefixCurve hn hW hE hdense hr N) ∧
      IsSNCDivisor n (originalStoppedPrefixBoundary hn hW hE hdense hr N) ∧
      IsTransverse n (originalStoppedPrefixCurve hn hW hE hdense hr N)
        (originalStoppedPrefixBoundary hn hW hE hdense hr N) ∧
      ∃ e : CMfd.of (n := n) (originalStoppedPrefixOpen hn hW hE hdense hr N)
          ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
            CMfd.of (n := n) (endpointPreimageOpen (originalGlobalSharpCurveEndpoint hn hW hE hdense hr)
              (stoppedBaseOpen (originalEndpointHistories hn hW hE hdense hr) (N+1))),
        ∀ q,(originalGlobalSharpCurveEndpoint hn hW hE hdense hr).projection (e q).val=
          (originalUniformPositiveTower hn hW hE hdense hr N).proj q.val := by
  refine ⟨originalGrowingSeq_good_isomorphism hn hW hE hdense hr,?_⟩
  intro K hK
  let A := originalEndpointHistories hn hW hE hdense hr
  let hc := originalEndpointHistories_cover hn hW hE hdense hr
  obtain ⟨N,hN⟩ := exists_compact_stopped_open_bound A hc K hK
  have hSharp := original_stopped_prefix_sharp hn hW hE hdense hr N
  exact ⟨N,hN,hSharp.1,hSharp.2.1,hSharp.2.2,positivePrefixTerminalBiholomorphism A hc N,
    positivePrefixTerminalBiholomorphism_projection A hc N⟩

end OriginalInput
end
end Hironaka.HironakaSharpActualCurveStoppedPrefixSharpGeometry
