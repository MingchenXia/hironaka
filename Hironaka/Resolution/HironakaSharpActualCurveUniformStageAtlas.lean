/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveUniformPrefixRestriction
import Hironaka.Resolution.HironakaSharpActualCurveOriginalGlobalEndpoint

/-! Actual uniform-stage atlas derived from OLD terminal finite histories.
All k genuine steps are retained in its prefix field; only its tail is reflexive. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveUniformStageAtlas
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupTowerTransforms BlowupTowerIsomorphism BlowupTowerIsoTail BlowupTowerSplit BlowupTowerSplitIso
  HironakaSharpActualCurveUniformPrefixes HironakaSharpActualCurveUniformPrefixRestriction
  HironakaSharpActualCurveEmptyPadding HironakaSharpActualCurveFiniteRecipeComparison
  HironakaSharpActualCurveOverlapMaps HironakaSharpActualCurveCommonOpenCocycle
  HironakaSharpActualCurveChosenOverlapCocycle HironakaSharpActualCurveEndpointGeometry
  HironakaSharpActualCurveTopologicalGluing HironakaSharpActualCurveGluedProjection
  HironakaSharpActualCurveGlobalManifold HironakaSharpActualCurveOriginalRecipeAtlas
  HironakaSharpActualCurveOriginalGlobalEndpoint HironakaSharpOriginalMemberProductDomain
  HironakaSharpOriginalMemberProduct NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealRestrictOpen BlowupRestrictOpen MaxLocusLocal NormalCrossingsInvariance
attribute [local instance] endpointChartedSpace
variable {n : ℕ} {X : CMfd.{u} n} {J : Type u}

/-- The OLD genuine padded comparison supplies the new stage map via actual
append and prefix restriction isomorphisms, not an input stage atlas. -/
theorem exists_unique_uniform_local_comparison (U V O : Opens X) (hOU : O≤U) (hOV : O≤V)
    {YU YV ZU ZV : CMfd.{u} n}
    (PU : BlowupTower (CMfd.of (n := n) U) YU) (PV : BlowupTower (CMfd.of (n := n) V) YV)
    (SU : BlowupTower YU ZU) (SV : BlowupTower YV ZV) (L : ℕ)
    (e : localEndpoint U O PU SU ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ localEndpoint V O PV SV)
    (he : IsTowerIso (commonOpenBase U V O hOU hOV)
      (localPaddedHistory U O PU SU L) (localPaddedHistory V O PV SV L) e) (k : ℕ) :
    ∃! d : CMfd.of (n := n) (openPreimage (uniformPrefix (PU.append SU) k).2 (nestedOpens U O))
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage (uniformPrefix (PV.append SV) k).2 (nestedOpens V O)),
      IsTowerIso (commonOpenBase U V O hOU hOV)
        (restrict (nestedOpens U O) (uniformPrefix (PU.append SU) k).2)
        (restrict (nestedOpens V O) (uniformPrefix (PV.append SV) k).2) d := by
  let AU := nestedOpens U O
  let AV := nestedOpens V O
  let RU := (restrict AU PU).append (restrict (openPreimage PU AU) SU)
  let RV := (restrict AV PV).append (restrict (openPreimage PV AV) SV)
  have hPad : IsTowerIso (commonOpenBase U V O hOU hOV)
      (RU.append (identityEmptyTail (CMfd.of (n := n) (openPreimage SU (openPreimage PU AU))) (L-SU.length)))
      (RV.append (identityEmptyTail (CMfd.of (n := n) (openPreimage SV (openPreimage PV AV))) (L-SV.length))) e := by
    simpa only [RU,RV,AU,AV,localPaddedHistory,paddedHistory,length_restrict,
      BlowupTower.append_assoc] using he
  obtain ⟨q,hq,_hqUnique⟩ := exists_unique_uniformPrefix_of_padded_comparison
    RU RV (L-SU.length) (L-SV.length) k hPad
  obtain ⟨a,ha⟩ := uniformPrefix_comparison (isTowerIso_restrict_append AU PU SU) k
  obtain ⟨b,hb⟩ := uniformPrefix_comparison (isTowerIso_restrict_append AV PV SV) k
  obtain ⟨f,hf,_hfUnique⟩ := exists_unique_uniformPrefix_open_restriction (PU.append SU) AU k
  obtain ⟨g,hg,_hgUnique⟩ := exists_unique_uniformPrefix_open_restriction (PV.append SV) AV k
  let d := f.symm.trans (a.trans (q.trans (b.symm.trans g)))
  have hNew := BlowupTowerSplitIso.IsTowerIso.congr_base
    (hf.symm.trans (ha.trans (hq.trans (hb.symm.trans hg))))
    (Φ' := commonOpenBase U V O hOU hOV) (fun _ => rfl)
  exact ⟨d,hNew,fun d' hd' => actual_tower_comparison_unique hd' hNew⟩

/-- Constructed stage atlas: all genuine k positions are in the prefix;
the reflexive tail/cut0 removes none of those positions. -/
def uniformStageHistories (A : ActualEndpointHistories X J) (k : ℕ) : ActualEndpointHistories X J := by
  let T := fun i => uniformPrefix ((A.prefixTower i).append (A.tail i)) k
  have hc : ∀ i j,∃ e : localEndpoint (A.openSet i) (A.openSet i⊓A.openSet j) (T i).2 .refl
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        localEndpoint (A.openSet j) (A.openSet i⊓A.openSet j) (T j).2 .refl,
      IsTowerIso (commonOpenBase (A.openSet i) (A.openSet j) (A.openSet i⊓A.openSet j)
        inf_le_left inf_le_right)
        (localPaddedHistory (A.openSet i) (A.openSet i⊓A.openSet j) (T i).2 .refl 0)
        (localPaddedHistory (A.openSet j) (A.openSet i⊓A.openSet j) (T j).2 .refl 0) e := by
    intro i j
    obtain ⟨e,he,_hUnique⟩ := exists_unique_uniform_local_comparison
      (A.openSet i) (A.openSet j) (A.openSet i⊓A.openSet j) inf_le_left inf_le_right
      (A.prefixTower i) (A.prefixTower j) (A.tail i) (A.tail j) (A.cut i j)
      (A.comparison i j) (A.stagewise i j) k
    refine ⟨e,?_⟩
    change IsTowerIso
      (commonOpenBase (A.openSet i) (A.openSet j) (A.openSet i⊓A.openSet j) inf_le_left inf_le_right)
      (restrict (nestedOpens (A.openSet i) (A.openSet i⊓A.openSet j)) (T i).2)
      (restrict (nestedOpens (A.openSet j) (A.openSet i⊓A.openSet j)) (T j).2) e
    exact he
  exact {
    openSet := A.openSet
    prefixSpace := fun i => (T i).1
    finalSpace := fun i => (T i).1
    prefixTower := fun i => (T i).2
    tail := fun _ => .refl
    cut := fun _ _ => 0
    left_bound := fun _ _ => le_refl 0
    right_bound := fun _ _ => le_refl 0
    comparison := fun i j => Classical.choose (hc i j)
    stagewise := fun i j => Classical.choose_spec (hc i j) }

theorem uniformStageHistories_length (A : ActualEndpointHistories X J) (k : ℕ) (i : J) :
    ((uniformStageHistories A k).prefixTower i).length=k :=
  uniformPrefix_length _ k

section OriginalInput
variable (hn : 0<n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
  (hdense : W⊆closure (W \ ⋃ H∈E,H)) (hr : ∀ x∈W,RegularAtDim (n := n) W x 1)

/-- ONLY original inputs construct each actual stage atlas internally. -/
def originalUniformStageHistories (k : ℕ) : ActualEndpointHistories X X :=
  uniformStageHistories (originalEndpointHistories hn hW hE hdense hr) k

theorem originalUniformStage_point_mem (k : ℕ) (x : X) :
    x∈(originalUniformStageHistories hn hW hE hdense hr k).openSet x :=
  originalEndpointHistories_point_mem hn hW hE hdense hr x

/-- Actual original TEST comes from the SAME full history, true empty
extension and its genuine head; all original ordered positions are retained. -/
theorem originalUniformStage_test (k : ℕ) (x : X) :
    let A := originalUniformStageHistories hn hW hE hdense hr k
    let U := A.openSet x
    IsGeoTestTower (originalMemberProductMarked (X := CMfd.of (n := n) U)
      ((Subtype.val : U → X) ⁻¹' W) (E.map ((Subtype.val : U → X) ⁻¹' ·)) 1) (A.prefixTower x) := by
  let A := originalEndpointHistories hn hW hE hdense hr
  let U := A.openSet x
  let M := originalMemberProductMarked (X := CMfd.of (n := n) U)
    ((Subtype.val : U → X) ⁻¹' W) (E.map ((Subtype.val : U → X) ⁻¹' ·)) 1
  let T := (A.prefixTower x).append (A.tail x)
  obtain ⟨π,hπ,_hFirst,_hPB,_hSteps,hTest,_hZ,_hD,_hProper,_hDomain,_hSNC,_hTrans,_hGood⟩ :=
    originalEndpointHistories_geometric_dictionary hn hW hE hdense hr x
  have hWU := isClosedSubmanifold_preimage_val hW U
  have hEU := isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val hE
  have hM : M.IsWellFormed :=
    ⟨hWU,isCoherent_originalMemberProduct hn hEU,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hWU⟩
  have hPad := (identityEmptyTail_geometric_dictionary M hM T hTest k).1
  change IsGeoTestTower M (head (T.append (identityEmptyTail (A.finalSpace x) k)) T.length)
  exact ((isGeoTestTower_iff_head_tail M _ _).mp hPad).1

/-- Actual complex stage geometry, never an input desired stage-space. -/
def originalUniformStageManifold (k : ℕ) : CMfd.{u} n :=
  endpointManifold (originalUniformStageHistories hn hW hE hdense hr k)
    (fun x => ⟨x,originalUniformStage_point_mem hn hW hE hdense hr k x⟩)

def originalUniformStageProjection (k : ℕ) :
    ContinuousMap (originalUniformStageManifold hn hW hE hdense hr k) X :=
  gluedProjection (originalUniformStageHistories hn hW hE hdense hr k)

theorem originalUniformStageProjection_contMDiff (k : ℕ) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (originalUniformStageProjection hn hW hE hdense hr k) :=
  gluedProjection_contMDiff (originalUniformStageHistories hn hW hE hdense hr k)
    (fun x => ⟨x,originalUniformStage_point_mem hn hW hE hdense hr k x⟩)

theorem originalUniformStageProjection_isProperMap (k : ℕ) :
    IsProperMap (originalUniformStageProjection hn hW hE hdense hr k) :=
  gluedProjection_isProperMap (originalUniformStageHistories hn hW hE hdense hr k)
    (originalUniformStage_point_mem hn hW hE hdense hr k)

theorem originalUniformStageProjection_surjective (k : ℕ) :
    Function.Surjective (originalUniformStageProjection hn hW hE hdense hr k) :=
  gluedProjection_surjective (originalUniformStageHistories hn hW hE hdense hr k)
    (fun x => ⟨x,originalUniformStage_point_mem hn hW hE hdense hr k x⟩)

end OriginalInput
end
end Hironaka.HironakaSharpActualCurveUniformStageAtlas
