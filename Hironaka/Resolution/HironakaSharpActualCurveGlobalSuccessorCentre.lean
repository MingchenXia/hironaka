/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveGlobalSuccessorGeometry

/-! Actual local successor centres descend through OLD chosen transitions.
Whole local preimages precede global closed smooth thin geometry. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveGlobalSuccessorCentre
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerIsoTail
  HironakaSharpActualCurveUniformPrefixes HironakaSharpActualCurveUniformStageAtlas
  HironakaSharpActualCurveUniformSuccessorComparison HironakaSharpActualCurveUniformSuccessorRestriction
  HironakaSharpActualCurveTopologicalGluing HironakaSharpActualCurveGluedProjection
  HironakaSharpActualCurveGlobalManifold HironakaSharpActualCurveLocalRangeBiholomorphism
  HironakaSharpActualCurveOriginalRecipeAtlas HironakaSharpActualCurveGlobalSuccessorGeometry
  HironakaSharpActualCurveEndpointGeometry HironakaSharpActualCurveChosenOverlapCocycle
attribute [local instance] endpointChartedSpace
variable {n : ℕ} {X : CMfd.{u} n} {J : Type u}

def localUniformCentre (A : ActualEndpointHistories X J) (k : ℕ) (i : J) :
    Set ((uniformStageHistories A k).finalSpace i) :=
  (actualUniformSuccessor ((A.prefixTower i).append (A.tail i)) k).centre

theorem transition_localUniformCentre (A : ActualEndpointHistories X J) (k : ℕ) (i j : J)
    (z : overlapOpen (uniformStageHistories A k) i j) :
    (transition (uniformStageHistories A k) i j z).val∈localUniformCentre A k j ↔
      z.val∈localUniformCentre A k i := by
  let Ti := (A.prefixTower i).append (A.tail i)
  let Tj := (A.prefixTower j).append (A.tail j)
  let Ui := MaxLocusLocal.nestedOpens (A.openSet i) (A.openSet i⊓A.openSet j)
  let Uj := MaxLocusLocal.nestedOpens (A.openSet j) (A.openSet i⊓A.openSet j)
  let Ri := actualRestrictedUniformSuccessor Ti k Ui
  let Rj := actualRestrictedUniformSuccessor Tj k Uj
  let q := opensCongr (n := n) (endpointOverlapOpen_eq_pair (A.openSet i) (A.openSet j)
    (uniformPrefix Ti k).2 .refl) z
  have h := Set.ext_iff.mp (uniformStage_successor_compatible A k i j).2 q
  have hi := Set.ext_iff.mp Ri.centre_eq q
  have hj := Set.ext_iff.mp Rj.centre_eq ((uniformStageHistories A k).comparison i j q)
  exact hj.symm.trans (h.trans hi)

def globalUniformCentre (A : ActualEndpointHistories X J) (k : ℕ) :
    Set (endpointGluedSpace (uniformStageHistories A k)) :=
  ⋃ i,endpointLocalInclusion (uniformStageHistories A k) i '' localUniformCentre A k i

theorem mem_globalUniformCentre_iff (A : ActualEndpointHistories X J) (k : ℕ) (i : J)
    (z : (uniformStageHistories A k).finalSpace i) :
    endpointLocalInclusion (uniformStageHistories A k) i z∈globalUniformCentre A k ↔
      z∈localUniformCentre A k i := by
  constructor
  · intro hz
    obtain ⟨j,w,hw,heq⟩ := mem_iUnion.mp hz
    obtain ⟨q,hqSource,hqTarget⟩ :=
      ((endpointGlueData (uniformStageHistories A k)).ι_eq_iff_rel j i w z).mp heq
    change q.val=w at hqSource
    change (transition (uniformStageHistories A k) j i q).val=z at hqTarget
    have hs : q.val∈localUniformCentre A k j := by rw [hqSource];exact hw
    have ht := (transition_localUniformCentre A k j i q).mpr hs
    rwa [hqTarget] at ht
  · intro hz
    exact mem_iUnion.mpr ⟨i,z,hz,rfl⟩

theorem preimage_globalUniformCentre (A : ActualEndpointHistories X J) (k : ℕ) (i : J) :
    endpointLocalInclusion (uniformStageHistories A k) i ⁻¹' globalUniformCentre A k=
      localUniformCentre A k i := by
  ext z
  exact mem_globalUniformCentre_iff A k i z

theorem isClosed_globalUniformCentre (A : ActualEndpointHistories X J) (k : ℕ) :
    IsClosed (globalUniformCentre A k) := by
  rw [←isOpen_compl_iff]
  apply ((endpointGlueData (uniformStageHistories A k)).isOpen_iff _).mpr
  change ∀ i : J,IsOpen (endpointLocalInclusion (uniformStageHistories A k) i ⁻¹'
    (globalUniformCentre A k)ᶜ)
  intro i
  have hLocal := (actualUniformSuccessor ((A.prefixTower i).append (A.tail i)) k).blowup.1.1.isOpen_compl
  have hEq := congrArg (fun B : Set ((uniformStageHistories A k).finalSpace i) => Bᶜ)
    (preimage_globalUniformCentre A k i)
  exact Eq.mpr (congrArg IsOpen hEq) hLocal

theorem localUniformCentre_regularAtDim_iff (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ) (i : J)
    (z : (uniformStageHistories A k).finalSpace i) (d : ℕ) :
    RegularAtDim (n := n) (localUniformCentre A k i) z d ↔
      RegularAtDim (n := n) (globalUniformCentre A k : Set (endpointManifold (uniformStageHistories A k) hc))
        (endpointLocalInclusion (uniformStageHistories A k) i z) d := by
  have hEq : (localBiholomorphism (uniformStageHistories A k) hc i) ⁻¹'
      ((Subtype.val : localRangeOpen (uniformStageHistories A k) hc i →
        endpointManifold (uniformStageHistories A k) hc) ⁻¹' globalUniformCentre A k)=
      localUniformCentre A k i := by
    ext w
    exact mem_globalUniformCentre_iff A k i w
  have h := CodimOnePartCanonical.regularAtDim_preimage_iff
    (localBiholomorphism (uniformStageHistories A k) hc i)
    (A := (Subtype.val : localRangeOpen (uniformStageHistories A k) hc i →
      endpointManifold (uniformStageHistories A k) hc) ⁻¹' globalUniformCentre A k)
    (x := z) (k := d)
  rw [hEq] at h
  exact h.trans AnalyticSubsetOpens.regularAtDim_preimage_val_iff

theorem isClosedSubmanifold_globalUniformCentre (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ) :
    IsClosedSubmanifold n (globalUniformCentre A k : Set (endpointManifold (uniformStageHistories A k) hc)) := by
  refine ⟨isClosed_globalUniformCentre A k,?_⟩
  intro q hq
  obtain ⟨i,z,rfl⟩ := endpointLocalInclusion_jointly_surjective (uniformStageHistories A k) q
  have hz := (mem_globalUniformCentre_iff A k i z).mp hq
  obtain ⟨d,hd⟩ := (actualUniformSuccessor ((A.prefixTower i).append (A.tail i)) k).blowup.1.2 z hz
  exact ⟨d,(localUniformCentre_regularAtDim_iff A hc k i z d).mp hd⟩

theorem interior_globalUniformCentre (A : ActualEndpointHistories X J) (k : ℕ) :
    interior (globalUniformCentre A k)=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro q hq
  obtain ⟨i,z,rfl⟩ := endpointLocalInclusion_jointly_surjective (uniformStageHistories A k) q
  have hz := preimage_interior_subset_interior_preimage
    (endpointLocalInclusion_openEmbedding (uniformStageHistories A k) i).continuous hq
  rw [preimage_globalUniformCentre] at hz
  change z∈interior (actualUniformSuccessor ((A.prefixTower i).append (A.tail i)) k).centre at hz
  rw [(actualUniformSuccessor ((A.prefixTower i).append (A.tail i)) k).blowup.2.1] at hz
  exact hz

section OriginalInput
variable (hn : 0<n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : NormalCrossings.IsSNCDivisor n E)
  (hdense : W⊆closure (W \ ⋃ H∈E,H)) (hr : ∀ x∈W,RegularAtDim (n := n) W x 1)

def originalUniformCentre (k : ℕ) : Set (originalUniformStageManifold hn hW hE hdense hr k) :=
  globalUniformCentre (originalEndpointHistories hn hW hE hdense hr) k

theorem isClosedSubmanifold_originalUniformCentre (k : ℕ) :
    IsClosedSubmanifold n (originalUniformCentre hn hW hE hdense hr k) :=
  isClosedSubmanifold_globalUniformCentre (originalEndpointHistories hn hW hE hdense hr)
    (originalEndpointHistories_cover hn hW hE hdense hr) k

theorem interior_originalUniformCentre (k : ℕ) :
    interior (originalUniformCentre hn hW hE hdense hr k)=∅ :=
  interior_globalUniformCentre (originalEndpointHistories hn hW hE hdense hr) k

end OriginalInput
end
end Hironaka.HironakaSharpActualCurveGlobalSuccessorCentre
