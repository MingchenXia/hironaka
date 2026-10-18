/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveEndpointGeometry
import Mathlib.Topology.Gluing

/-! Real endpoint transitions construct actual topological gluing data.
Complete three-node mathematics precedes substantive code. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
open CategoryTheory CategoryTheory.Limits
universe u
namespace Hironaka.HironakaSharpActualCurveTopologicalGluing
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupTowerTransforms BlowupTowerIsomorphism BlowupTowerSplitIso BlowupTowerIsoTail MaxLocusLocal
  HironakaSharpActualCurveOverlapMaps HironakaSharpActualCurveCommonOpenCocycle
  HironakaSharpActualCurveChosenOverlapCocycle HironakaSharpActualCurveEndpointGeometry
variable {n : ℕ} {X : CMfd.{u} n} {J : Type u}

/-- Ordinary actual local finite histories and their genuine stagewise maps.
There is no supplied cocycle, projection identity, separation or cover field. -/
structure ActualEndpointHistories (X : CMfd.{u} n) (J : Type u) where
  openSet : J → Opens X
  prefixSpace : J → CMfd.{u} n
  finalSpace : J → CMfd.{u} n
  prefixTower : ∀ i, BlowupTower (CMfd.of (n := n) (openSet i)) (prefixSpace i)
  tail : ∀ i, BlowupTower (prefixSpace i) (finalSpace i)
  cut : J → J → ℕ
  left_bound : ∀ i j, (tail i).length≤cut i j
  right_bound : ∀ i j, (tail j).length≤cut i j
  comparison : ∀ i j,
    localEndpoint (openSet i) (openSet i⊓openSet j) (prefixTower i) (tail i)
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        localEndpoint (openSet j) (openSet i⊓openSet j) (prefixTower j) (tail j)
  stagewise : ∀ i j,
    IsTowerIso (commonOpenBase (openSet i) (openSet j) (openSet i⊓openSet j) inf_le_left inf_le_right)
      (localPaddedHistory (openSet i) (openSet i⊓openSet j) (prefixTower i) (tail i) (cut i j))
      (localPaddedHistory (openSet j) (openSet i⊓openSet j) (prefixTower j) (tail j) (cut i j))
      (comparison i j)

def overlapOpen (A : ActualEndpointHistories X J) (i j : J) : Opens (A.finalSpace i) :=
  endpointOverlapOpen (A.openSet i) (A.openSet j) (A.prefixTower i) (A.tail i)

def transition (A : ActualEndpointHistories X J) (i j : J) :
    CMfd.of (n := n) (overlapOpen A i j) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (overlapOpen A j i) :=
  endpointTransition (A.openSet i) (A.openSet j) (A.prefixTower i) (A.prefixTower j)
    (A.tail i) (A.tail j) (A.comparison i j)

theorem transition_projection (A : ActualEndpointHistories X J) (i j : J)
    (z : overlapOpen A i j) :
    endpointProjection (A.openSet j) (A.prefixTower j) (A.tail j) (transition A i j z).val =
      endpointProjection (A.openSet i) (A.prefixTower i) (A.tail i) z.val :=
  endpointTransition_projection (A.openSet i) (A.openSet j) (A.prefixTower i) (A.prefixTower j)
    (A.tail i) (A.tail j) (A.cut i j) (A.comparison i j) (A.stagewise i j) z

theorem overlapOpen_self (A : ActualEndpointHistories X J) (i : J) : overlapOpen A i i=⊤ :=
  endpointOverlapOpen_self (A.openSet i) (A.prefixTower i) (A.tail i)

theorem transition_self (A : ActualEndpointHistories X J) (i : J) :
    transition A i i=Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) (overlapOpen A i i)) ∞ :=
  endpointTransition_self (A.openSet i) (A.prefixTower i) (A.tail i)
    (A.cut i i) (A.comparison i i) (A.stagewise i i)

theorem transition_inter (A : ActualEndpointHistories X J) (i j k : J)
    (z : overlapOpen A i j) (hz : z.val∈overlapOpen A i k) :
    (transition A i j z).val∈overlapOpen A j k := by
  change endpointProjection (A.openSet j) (A.prefixTower j) (A.tail j) (transition A i j z).val ∈ A.openSet k
  rw [transition_projection]
  exact hz

/-- The OLD chosen transitions, not merely newly chosen common-open maps,
satisfy the true literal TopCat gluing cocycle. -/
theorem transition_cocycle (A : ActualEndpointHistories X J) (i j k : J)
    (z : overlapOpen A i j) (hz : z.val∈overlapOpen A i k) :
    (transition A j k ⟨(transition A i j z).val,transition_inter A i j k z hz⟩).val =
      (transition A i k ⟨z.val,hz⟩).val := by
  let O := (A.openSet i⊓A.openSet j)⊓A.openSet k
  have hOi : O≤A.openSet i := fun _ h => h.1.1
  have hOj : O≤A.openSet j := fun _ h => h.1.2
  have hOk : O≤A.openSet k := fun _ h => h.2
  obtain ⟨e12,e23,e13,_he12,_he23,_he13,hPoint12,hPoint23,hPoint13,hComp⟩ :=
    exists_chosen_pairwise_overlap_cocycle (A.openSet i) (A.openSet j) (A.openSet k) O
      hOi hOj hOk (A.prefixTower i) (A.prefixTower j) (A.prefixTower k)
      (A.tail i) (A.tail j) (A.tail k) (A.cut i j) (A.cut j k) (A.cut i k)
      (A.left_bound i j) (A.right_bound i j) (A.left_bound j k) (A.right_bound j k)
      (A.left_bound i k) (A.right_bound i k)
      (A.comparison i j) (A.comparison j k) (A.comparison i k)
      (A.stagewise i j) (A.stagewise j k) (A.stagewise i k)
  have hzO : z.val∈openPreimage (A.tail i) (openPreimage (A.prefixTower i) (nestedOpens (A.openSet i) O)) := by
    change endpointProjection (A.openSet i) (A.prefixTower i) (A.tail i) z.val∈O
    exact ⟨⟨((A.prefixTower i).proj ((A.tail i).proj z.val)).property,z.property⟩,hz⟩
  let zp : localEndpoint (A.openSet i) O (A.prefixTower i) (A.tail i) := ⟨z.val,hzO⟩
  have h12 : (e12 zp).val=(transition A i j z).val := hPoint12 zp
  let q : overlapOpen A j k := ⟨(transition A i j z).val,transition_inter A i j k z hz⟩
  let qp : localEndpoint (A.openSet j) (A.openSet j⊓A.openSet k) (A.prefixTower j) (A.tail j) :=
    ⟨(e12 zp).val,openPreimage_mono (A.tail j) (openPreimage_mono (A.prefixTower j)
      (commonWindowInclusion (A.openSet j) (A.openSet j⊓A.openSet k) O (le_inf hOj hOk))) (e12 zp).property⟩
  have hqp : qp=opensCongr (endpointOverlapOpen_eq_pair (A.openSet j) (A.openSet k)
      (A.prefixTower j) (A.tail j)) q := Subtype.ext h12
  have h23 : (e23 (e12 zp)).val=(transition A j k q).val := by
    have hPoint := hPoint23 (e12 zp)
    change (e23 (e12 zp)).val=(A.comparison j k qp).val at hPoint
    rw [hqp] at hPoint
    exact hPoint
  have h13 : (e13 zp).val=(transition A i k ⟨z.val,hz⟩).val := hPoint13 zp
  have hc := congrArg (fun w => (w zp).val) hComp
  exact h23.symm.trans (hc.trans h13)

/-- Every gluing field is produced from actual finite-history geometry. -/
def endpointGlueCore (A : ActualEndpointHistories X J) : TopCat.GlueData.MkCore where
  J := J
  U i := TopCat.of (A.finalSpace i)
  V := overlapOpen A
  t i j := TopCat.ofHom ⟨transition A i j,(transition A i j).contMDiff.continuous⟩
  V_id := overlapOpen_self A
  t_id := by
    intro i
    funext z
    change transition A i i z=z
    rw [transition_self]
    rfl
  t_inter := fun {i j} k z hz => transition_inter A i j k z hz
  cocycle := transition_cocycle A

def endpointGlueData (A : ActualEndpointHistories X J) : TopCat.GlueData :=
  TopCat.GlueData.mk' (endpointGlueCore A)

def endpointGluedSpace (A : ActualEndpointHistories X J) : TopCat :=
  (endpointGlueData A).glued

def endpointLocalInclusion (A : ActualEndpointHistories X J) (i : J) :
    A.finalSpace i → endpointGluedSpace A := (endpointGlueData A).ι i

theorem endpointLocalInclusion_openEmbedding (A : ActualEndpointHistories X J) (i : J) :
    Topology.IsOpenEmbedding (endpointLocalInclusion A i) :=
  (endpointGlueData A).ι_isOpenEmbedding i

theorem endpointLocalInclusion_jointly_surjective (A : ActualEndpointHistories X J)
    (z : endpointGluedSpace A) :
    ∃ (i : J) (y : A.finalSpace i),endpointLocalInclusion A i y=z :=
  (endpointGlueData A).ι_jointly_surjective z

end
end Hironaka.HironakaSharpActualCurveTopologicalGluing
