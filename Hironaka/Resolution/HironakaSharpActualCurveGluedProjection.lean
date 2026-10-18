/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveTopologicalGluing
import Hironaka.Resolution.HironakaTerminalAtlasHolomorphic

/-! Actual continuous projection, saturated local ranges and true embedding
transitions are constructed before complex manifold descent. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
open CategoryTheory CategoryTheory.Limits
universe u
namespace Hironaka.HironakaSharpActualCurveGluedProjection
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupTowerTransforms BlowupTowerIsomorphism BlowupTowerSplitIso BlowupTowerIsoTail MaxLocusLocal
  HironakaSharpActualCurveEndpointGeometry HironakaSharpActualCurveTopologicalGluing
  HironakaTerminalAtlasHolomorphic
variable {n : ℕ} {X : CMfd.{u} n} {J : Type u}

def localProjection (A : ActualEndpointHistories X J) (i : J) :
    ContinuousMap (A.finalSpace i) X :=
  ⟨endpointProjection (A.openSet i) (A.prefixTower i) (A.tail i),
    (endpointProjection_contMDiff (A.openSet i) (A.prefixTower i) (A.tail i)).continuous⟩

theorem localProjection_compatible (A : ActualEndpointHistories X J) (ij : J×J) :
    (endpointGlueData A).toGlueData.diagram.fst ij ≫ TopCat.ofHom (localProjection A ij.1)=
      (endpointGlueData A).toGlueData.diagram.snd ij ≫ TopCat.ofHom (localProjection A ij.2) := by
  rcases ij with ⟨i,j⟩
  ext z
  exact (transition_projection A i j z).symm

/-- The actual quotient universal property constructs the real continuous projection. -/
def gluedProjection (A : ActualEndpointHistories X J) : ContinuousMap (endpointGluedSpace A) X :=
  (Multicoequalizer.desc (endpointGlueData A).toGlueData.diagram (TopCat.of X)
    (fun i => TopCat.ofHom (localProjection A i)) (localProjection_compatible A)).hom

theorem gluedProjection_local (A : ActualEndpointHistories X J) (i : J) (z : A.finalSpace i) :
    gluedProjection A (endpointLocalInclusion A i z)=localProjection A i z := by
  have h := Multicoequalizer.π_desc (endpointGlueData A).toGlueData.diagram (TopCat.of X)
    (fun i => TopCat.ofHom (localProjection A i)) (localProjection_compatible A) i
  exact congrArg (fun f : (endpointGlueData A).U i ⟶ TopCat.of X => f z) h

theorem gluedProjection_unique (A : ActualEndpointHistories X J)
    (q : ContinuousMap (endpointGluedSpace A) X)
    (hq : ∀ (i : J) (z : A.finalSpace i),q (endpointLocalInclusion A i z)=localProjection A i z) :
    q=gluedProjection A := by
  apply ContinuousMap.ext
  intro z
  obtain ⟨i,y,rfl⟩ := endpointLocalInclusion_jointly_surjective A z
  exact (hq i y).trans (gluedProjection_local A i y).symm

/-- BOTH whole-range directions follow from actual overlap membership and gluing. -/
theorem localInclusion_range (A : ActualEndpointHistories X J) (i : J) :
    range (endpointLocalInclusion A i)=(gluedProjection A) ⁻¹' (A.openSet i : Set X) := by
  ext z
  constructor
  · rintro ⟨y,rfl⟩
    change gluedProjection A (endpointLocalInclusion A i y)∈A.openSet i
    rw [gluedProjection_local]
    exact ((A.prefixTower i).proj ((A.tail i).proj y)).property
  · intro hz
    obtain ⟨j,y,rfl⟩ := endpointLocalInclusion_jointly_surjective A z
    change gluedProjection A (endpointLocalInclusion A j y)∈A.openSet i at hz
    rw [gluedProjection_local] at hz
    have hy : y∈overlapOpen A j i := hz
    let s : overlapOpen A j i := ⟨y,hy⟩
    refine ⟨(transition A j i s).val,?_⟩
    have hc := (endpointGlueData A).toGlueData.glue_condition j i
    exact congrArg (fun f : (endpointGlueData A).V (j,i) ⟶ (endpointGlueData A).glued => f s) hc

theorem embeddingOverlap_eq (A : ActualEndpointHistories X J) (i j : J) :
    actualEmbeddingOverlap (endpointLocalInclusion A i) (endpointLocalInclusion A j)
      (endpointLocalInclusion_openEmbedding A i) (endpointLocalInclusion_openEmbedding A j)=
        overlapOpen A i j := by
  apply Opens.ext
  ext z
  change endpointLocalInclusion A i z∈range (endpointLocalInclusion A j) ↔
    endpointProjection (A.openSet i) (A.prefixTower i) (A.tail i) z∈A.openSet j
  rw [localInclusion_range]
  change gluedProjection A (endpointLocalInclusion A i z)∈A.openSet j ↔ localProjection A i z∈A.openSet j
  rw [gluedProjection_local]

theorem transition_inclusion (A : ActualEndpointHistories X J) (i j : J)
    (z : overlapOpen A i j) :
    endpointLocalInclusion A j (transition A i j z).val=endpointLocalInclusion A i z.val := by
  have hc := (endpointGlueData A).toGlueData.glue_condition i j
  exact congrArg (fun f : (endpointGlueData A).V (i,j) ⟶ (endpointGlueData A).glued => f z) hc

/-- Actual equal-open biholomorphisms give the true embedding-overlap transition. -/
def embeddingTransition (A : ActualEndpointHistories X J) (i j : J) :
    CMfd.of (n := n) (actualEmbeddingOverlap (endpointLocalInclusion A i) (endpointLocalInclusion A j)
      (endpointLocalInclusion_openEmbedding A i) (endpointLocalInclusion_openEmbedding A j))
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (actualEmbeddingOverlap (endpointLocalInclusion A j) (endpointLocalInclusion A i)
          (endpointLocalInclusion_openEmbedding A j) (endpointLocalInclusion_openEmbedding A i)) :=
  ((opensCongr (embeddingOverlap_eq A i j)).trans (transition A i j)).trans
    (opensCongr (embeddingOverlap_eq A j i).symm)

theorem embeddingTransition_inclusion (A : ActualEndpointHistories X J) (i j : J)
    (z : actualEmbeddingOverlap (endpointLocalInclusion A i) (endpointLocalInclusion A j)
      (endpointLocalInclusion_openEmbedding A i) (endpointLocalInclusion_openEmbedding A j)) :
    endpointLocalInclusion A j (embeddingTransition A i j z).val=endpointLocalInclusion A i z.val :=
  transition_inclusion A i j (opensCongr (embeddingOverlap_eq A i j) z)

end
end Hironaka.HironakaSharpActualCurveGluedProjection
