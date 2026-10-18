/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveUniformSuccessorRestriction

/-! Actual local successor compatibility precedes genuine TopCat quotient
construction of global next-stage arrows. No gluing certificate is an input. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
open CategoryTheory CategoryTheory.Limits
universe u
namespace Hironaka.HironakaSharpActualCurveGlobalSuccessorMap
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsoTail MaxLocusLocal
  HironakaSharpActualCurveUniformPrefixes HironakaSharpActualCurveUniformStageAtlas
  HironakaSharpActualCurveUniformSuccessorComparison HironakaSharpActualCurveUniformSuccessorRestriction
  HironakaSharpActualCurveTopologicalGluing HironakaSharpActualCurveGluedProjection
  HironakaSharpActualCurveEndpointGeometry HironakaSharpActualCurveOriginalRecipeAtlas
  HironakaSharpActualCurveGlobalManifold HironakaSharpActualCurveChosenOverlapCocycle
variable {n : ℕ} {X : CMfd.{u} n} {J : Type u}

def localUniformSuccessor (A : ActualEndpointHistories X J) (k : ℕ) (i : J) :
    (uniformStageHistories A (k+1)).finalSpace i → (uniformStageHistories A k).finalSpace i :=
  (actualUniformSuccessor ((A.prefixTower i).append (A.tail i)) k).map

theorem localUniformSuccessor_contMDiff (A : ActualEndpointHistories X J) (k : ℕ) (i : J) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (localUniformSuccessor A k i) :=
  (actualUniformSuccessor ((A.prefixTower i).append (A.tail i)) k).blowup.contMDiff

theorem localUniformSuccessor_projection (A : ActualEndpointHistories X J) (k : ℕ) (i : J)
    (z : (uniformStageHistories A (k+1)).finalSpace i) :
    localProjection (uniformStageHistories A k) i (localUniformSuccessor A k i z)=
      localProjection (uniformStageHistories A (k+1)) i z := by
  exact congrArg Subtype.val (actualUniformSuccessor_projection
    ((A.prefixTower i).append (A.tail i)) k z).symm

theorem localUniformSuccessor_overlap_mem (A : ActualEndpointHistories X J) (k : ℕ) (i j : J)
    (z : overlapOpen (uniformStageHistories A (k+1)) i j) :
    localUniformSuccessor A k i z.val∈overlapOpen (uniformStageHistories A k) i j := by
  change localProjection (uniformStageHistories A k) i (localUniformSuccessor A k i z.val)∈A.openSet j
  rw [localUniformSuccessor_projection]
  exact z.property

theorem localUniformSuccessor_transition (A : ActualEndpointHistories X J) (k : ℕ) (i j : J)
    (z : overlapOpen (uniformStageHistories A (k+1)) i j) :
    localUniformSuccessor A k j (transition (uniformStageHistories A (k+1)) i j z).val=
      (transition (uniformStageHistories A k) i j
        ⟨localUniformSuccessor A k i z.val,localUniformSuccessor_overlap_mem A k i j z⟩).val := by
  let Ti := (A.prefixTower i).append (A.tail i)
  let Tj := (A.prefixTower j).append (A.tail j)
  let Ui := nestedOpens (A.openSet i) (A.openSet i⊓A.openSet j)
  let Uj := nestedOpens (A.openSet j) (A.openSet i⊓A.openSet j)
  let Ri := actualRestrictedUniformSuccessor Ti k Ui
  let Rj := actualRestrictedUniformSuccessor Tj k Uj
  let q := opensCongr (n := n) (endpointOverlapOpen_eq_pair (A.openSet i) (A.openSet j)
    (uniformPrefix Ti (k+1)).2 .refl) z
  let p : overlapOpen (uniformStageHistories A k) i j :=
    ⟨localUniformSuccessor A k i z.val,localUniformSuccessor_overlap_mem A k i j z⟩
  let q₀ := opensCongr (n := n) (endpointOverlapOpen_eq_pair (A.openSet i) (A.openSet j)
    (uniformPrefix Ti k).2 .refl) p
  have hq₀ : Ri.map q=q₀ := by
    apply Subtype.ext
    exact Ri.map_val q
  have hSquare := uniformStage_successor_compatible A k i j
  have hh := congrArg Subtype.val (hSquare.1 q)
  change (Rj.map ((uniformStageHistories A (k+1)).comparison i j q)).val=
    ((uniformStageHistories A k).comparison i j (Ri.map q)).val at hh
  have hRead := Rj.map_val ((uniformStageHistories A (k+1)).comparison i j q)
  have hTarget := congrArg (fun w => ((uniformStageHistories A k).comparison i j w).val) hq₀
  exact hRead.symm.trans (hh.trans hTarget)

def localUniformSuccessorToGlue (A : ActualEndpointHistories X J) (k : ℕ) (i : J) :
    ContinuousMap ((uniformStageHistories A (k+1)).finalSpace i)
      (endpointGluedSpace (uniformStageHistories A k)) :=
  ⟨fun z => endpointLocalInclusion (uniformStageHistories A k) i (localUniformSuccessor A k i z),
    (endpointLocalInclusion_openEmbedding (uniformStageHistories A k) i).continuous.comp
      (localUniformSuccessor_contMDiff A k i).continuous⟩

theorem localUniformSuccessorToGlue_compatible (A : ActualEndpointHistories X J) (k : ℕ) (ij : J×J) :
    (endpointGlueData (uniformStageHistories A (k+1))).toGlueData.diagram.fst ij ≫
        TopCat.ofHom (localUniformSuccessorToGlue A k ij.1)=
      (endpointGlueData (uniformStageHistories A (k+1))).toGlueData.diagram.snd ij ≫
        TopCat.ofHom (localUniformSuccessorToGlue A k ij.2) := by
  rcases ij with ⟨i,j⟩
  ext z
  change endpointLocalInclusion (uniformStageHistories A k) i (localUniformSuccessor A k i z.val)=
    endpointLocalInclusion (uniformStageHistories A k) j
      (localUniformSuccessor A k j (transition (uniformStageHistories A (k+1)) i j z).val)
  let w : overlapOpen (uniformStageHistories A (k+1)) i j := z
  exact (transition_inclusion (uniformStageHistories A k) i j
    ⟨_,localUniformSuccessor_overlap_mem A k i j w⟩).symm.trans
      (congrArg (endpointLocalInclusion (uniformStageHistories A k) j)
        (localUniformSuccessor_transition A k i j w).symm)

def globalUniformSuccessor (A : ActualEndpointHistories X J) (k : ℕ) :
    ContinuousMap (endpointGluedSpace (uniformStageHistories A (k+1)))
      (endpointGluedSpace (uniformStageHistories A k)) :=
  (Multicoequalizer.desc (endpointGlueData (uniformStageHistories A (k+1))).toGlueData.diagram
    (endpointGluedSpace (uniformStageHistories A k))
    (fun i => TopCat.ofHom (localUniformSuccessorToGlue A k i))
    (localUniformSuccessorToGlue_compatible A k)).hom

theorem globalUniformSuccessor_local (A : ActualEndpointHistories X J) (k : ℕ) (i : J)
    (z : (uniformStageHistories A (k+1)).finalSpace i) :
    globalUniformSuccessor A k (endpointLocalInclusion (uniformStageHistories A (k+1)) i z)=
      localUniformSuccessorToGlue A k i z := by
  have h := Multicoequalizer.π_desc (endpointGlueData (uniformStageHistories A (k+1))).toGlueData.diagram
    (endpointGluedSpace (uniformStageHistories A k))
    (fun i => TopCat.ofHom (localUniformSuccessorToGlue A k i))
    (localUniformSuccessorToGlue_compatible A k) i
  exact congrArg (fun f : (endpointGlueData (uniformStageHistories A (k+1))).U i ⟶
    endpointGluedSpace (uniformStageHistories A k) => f z) h

theorem globalUniformSuccessor_projection (A : ActualEndpointHistories X J) (k : ℕ)
    (z : endpointGluedSpace (uniformStageHistories A (k+1))) :
    gluedProjection (uniformStageHistories A k) (globalUniformSuccessor A k z)=
      gluedProjection (uniformStageHistories A (k+1)) z := by
  obtain ⟨i,y,rfl⟩ := endpointLocalInclusion_jointly_surjective (uniformStageHistories A (k+1)) z
  rw [globalUniformSuccessor_local]
  change gluedProjection (uniformStageHistories A k)
    (endpointLocalInclusion (uniformStageHistories A k) i (localUniformSuccessor A k i y))=_
  rw [gluedProjection_local,gluedProjection_local]
  exact localUniformSuccessor_projection A k i y

theorem globalUniformSuccessor_unique (A : ActualEndpointHistories X J) (k : ℕ)
    (g : ContinuousMap (endpointGluedSpace (uniformStageHistories A (k+1)))
      (endpointGluedSpace (uniformStageHistories A k)))
    (hg : ∀ i z,g (endpointLocalInclusion (uniformStageHistories A (k+1)) i z)=
      localUniformSuccessorToGlue A k i z) : g=globalUniformSuccessor A k := by
  apply ContinuousMap.ext
  intro z
  obtain ⟨i,y,rfl⟩ := endpointLocalInclusion_jointly_surjective (uniformStageHistories A (k+1)) z
  exact (hg i y).trans (globalUniformSuccessor_local A k i y).symm

section OriginalInput
variable (hn : 0<n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : NormalCrossings.IsSNCDivisor n E)
  (hdense : W⊆closure (W \ ⋃ H∈E,H)) (hr : ∀ x∈W,RegularAtDim (n := n) W x 1)

def originalUniformSuccessor (k : ℕ) :
    ContinuousMap (originalUniformStageManifold hn hW hE hdense hr (k+1))
      (originalUniformStageManifold hn hW hE hdense hr k) :=
  globalUniformSuccessor (originalEndpointHistories hn hW hE hdense hr) k

theorem originalUniformSuccessor_projection (k : ℕ)
    (z : originalUniformStageManifold hn hW hE hdense hr (k+1)) :
    originalUniformStageProjection hn hW hE hdense hr k (originalUniformSuccessor hn hW hE hdense hr k z)=
      originalUniformStageProjection hn hW hE hdense hr (k+1) z :=
  globalUniformSuccessor_projection (originalEndpointHistories hn hW hE hdense hr) k z

end OriginalInput
end
end Hironaka.HironakaSharpActualCurveGlobalSuccessorMap
