/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveStoppedAtlasTransition

/-! Actual quotient independence precedes global stopped-open gluing.
All local maps are the SAME already constructed stopped identifications. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveStoppedOpenGluing
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupRestrictOpen
  HironakaSharpActualCurveUniformPrefixes HironakaSharpActualCurveUniformStageAtlas
  HironakaSharpActualCurveTopologicalGluing HironakaSharpActualCurveGluedProjection
  HironakaSharpActualCurveGlobalManifold HironakaSharpActualCurveLocalRangeBiholomorphism
  HironakaSharpActualCurveStoppedStageTerminalRanges HironakaSharpActualCurveStoppedAtlasTransition
  HironakaSharpActualCurveOriginalRecipeAtlas
attribute [local instance] endpointChartedSpace
variable {n : ℕ} {X : CMfd.{u} n} {J : Type u}

def stoppedBaseOpen (A : ActualEndpointHistories X J) (k : ℕ) : Opens X :=
  ⨆ (i : J) (_h : ((A.prefixTower i).append (A.tail i)).length≤k),A.openSet i

theorem mem_stoppedBaseOpen (A : ActualEndpointHistories X J) (k : ℕ) (x : X) :
    x∈stoppedBaseOpen A k ↔ ∃ i,((A.prefixTower i).append (A.tail i)).length≤k ∧ x∈A.openSet i := by
  simp only [stoppedBaseOpen,Opens.mem_iSup,exists_prop]

def stoppedStageOpen (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ) : Opens (endpointManifold (uniformStageHistories A k) hc) :=
  ⟨(gluedProjection (uniformStageHistories A k)) ⁻¹' (stoppedBaseOpen A k : Set X),
    (stoppedBaseOpen A k).isOpen.preimage (gluedProjection (uniformStageHistories A k)).continuous⟩

def stoppedTerminalOpen (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ) : Opens (endpointManifold A hc) :=
  ⟨(gluedProjection A) ⁻¹' (stoppedBaseOpen A k : Set X),
    (stoppedBaseOpen A k).isOpen.preimage (gluedProjection A).continuous⟩

/-- Genuine chosen transition relations and actual embeddings force representation independence. -/
theorem stopped_local_inclusion_eq (A : ActualEndpointHistories X J) (k : ℕ) (i j : J)
    (hi : ((A.prefixTower i).append (A.tail i)).length≤k)
    (hj : ((A.prefixTower j).append (A.tail j)).length≤k)
    (a : (uniformStageHistories A k).finalSpace i) (b : (uniformStageHistories A k).finalSpace j)
    (hab : endpointLocalInclusion (uniformStageHistories A k) i a=
      endpointLocalInclusion (uniformStageHistories A k) j b) :
    endpointLocalInclusion A i (stoppedPrefixBiholomorphism ((A.prefixTower i).append (A.tail i)) k hi a)=
      endpointLocalInclusion A j (stoppedPrefixBiholomorphism ((A.prefixTower j).append (A.tail j)) k hj b) := by
  let Ak := uniformStageHistories A k
  have ha : a∈overlapOpen Ak i j := by
    have hh : gluedProjection Ak (endpointLocalInclusion Ak i a)∈A.openSet j := by
      rw [hab,gluedProjection_local_full]
      exact (((Ak.prefixTower j).append (Ak.tail j)).proj b).property
    rw [gluedProjection_local] at hh
    exact hh
  have hTrans : (transition Ak i j ⟨a,ha⟩).val=b :=
    (endpointLocalInclusion_openEmbedding Ak j).injective
      ((transition_inclusion Ak i j ⟨a,ha⟩).trans hab)
  have hSquare := stoppedAtlasTransition_square A i j k hi hj ⟨a,ha⟩
  calc
    endpointLocalInclusion A i (stoppedPrefixBiholomorphism ((A.prefixTower i).append (A.tail i)) k hi a)=
        endpointLocalInclusion A j (transition A i j
          ⟨stoppedPrefixBiholomorphism ((A.prefixTower i).append (A.tail i)) k hi a,
            stoppedPoint_overlap_mem A i j k hi ⟨a,ha⟩⟩).val := (transition_inclusion A i j
          ⟨stoppedPrefixBiholomorphism ((A.prefixTower i).append (A.tail i)) k hi a,
            stoppedPoint_overlap_mem A i j k hi ⟨a,ha⟩⟩).symm
    _=endpointLocalInclusion A j (stoppedPrefixBiholomorphism ((A.prefixTower j).append (A.tail j)) k hj
        (transition Ak i j ⟨a,ha⟩).val) := congrArg (endpointLocalInclusion A j) hSquare.symm
    _=endpointLocalInclusion A j (stoppedPrefixBiholomorphism ((A.prefixTower j).append (A.tail j)) k hj b) :=
      congrArg (fun q => endpointLocalInclusion A j
        (stoppedPrefixBiholomorphism ((A.prefixTower j).append (A.tail j)) k hj q)) hTrans

private theorem exists_stopped_representative (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ) (z : stoppedStageOpen A hc k) :
    ∃ i,((A.prefixTower i).append (A.tail i)).length≤k ∧
      ∃ y : (uniformStageHistories A k).finalSpace i,
        endpointLocalInclusion (uniformStageHistories A k) i y=z.val := by
  obtain ⟨i,hi,hz⟩ := (mem_stoppedBaseOpen A k _).mp z.property
  have hrange : z.val∈range (endpointLocalInclusion (uniformStageHistories A k) i) := by
    rw [localInclusion_range]
    exact hz
  obtain ⟨y,hy⟩ := hrange
  exact ⟨i,hi,y,hy⟩

private theorem exists_stopped_value (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ) (z : stoppedStageOpen A hc k) :
    ∃ w : endpointManifold A hc,∀ (i : J) (hi : ((A.prefixTower i).append (A.tail i)).length≤k)
      (y : (uniformStageHistories A k).finalSpace i),
      endpointLocalInclusion (uniformStageHistories A k) i y=z.val →
      w=endpointLocalInclusion A i (stoppedPrefixBiholomorphism ((A.prefixTower i).append (A.tail i)) k hi y) := by
  obtain ⟨i,hi,y,hy⟩ := exists_stopped_representative A hc k z
  refine ⟨endpointLocalInclusion A i (stoppedPrefixBiholomorphism ((A.prefixTower i).append (A.tail i)) k hi y),?_⟩
  intro j hj t ht
  exact stopped_local_inclusion_eq A k i j hi hj y t (hy.trans ht.symm)

def stoppedPointMap (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ) : stoppedStageOpen A hc k → endpointManifold A hc :=
  fun z => Classical.choose (exists_stopped_value A hc k z)

theorem stoppedPointMap_local (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ) (z : stoppedStageOpen A hc k)
    (i : J) (hi : ((A.prefixTower i).append (A.tail i)).length≤k)
    (y : (uniformStageHistories A k).finalSpace i)
    (hy : endpointLocalInclusion (uniformStageHistories A k) i y=z.val) :
    stoppedPointMap A hc k z=
      endpointLocalInclusion A i (stoppedPrefixBiholomorphism ((A.prefixTower i).append (A.tail i)) k hi y) :=
  Classical.choose_spec (exists_stopped_value A hc k z) i hi y hy

theorem stoppedPointMap_projection (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ) (z : stoppedStageOpen A hc k) :
    gluedProjection A (stoppedPointMap A hc k z)=gluedProjection (uniformStageHistories A k) z.val := by
  obtain ⟨i,hi,y,hy⟩ := exists_stopped_representative A hc k z
  calc
    gluedProjection A (stoppedPointMap A hc k z)=
        (((A.prefixTower i).append (A.tail i)).proj
          (stoppedPrefixBiholomorphism ((A.prefixTower i).append (A.tail i)) k hi y) : X) := by
      rw [stoppedPointMap_local A hc k z i hi y hy,gluedProjection_local_full]
    _=((uniformPrefix ((A.prefixTower i).append (A.tail i)) k).2.proj y : X) :=
      congrArg Subtype.val (stoppedPrefixBiholomorphism_projection _ k hi y)
    _=gluedProjection (uniformStageHistories A k) z.val :=
      (gluedProjection_local_full (uniformStageHistories A k) i y).symm.trans
        (congrArg (gluedProjection (uniformStageHistories A k)) hy)

def stoppedOpenMap (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ) : stoppedStageOpen A hc k → stoppedTerminalOpen A hc k :=
  fun z => ⟨stoppedPointMap A hc k z,by
    change gluedProjection A (stoppedPointMap A hc k z)∈stoppedBaseOpen A k
    rw [stoppedPointMap_projection]
    exact z.property⟩

theorem stoppedOpenMap_bijective (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ) : Function.Bijective (stoppedOpenMap A hc k) := by
  let Ak := uniformStageHistories A k
  constructor
  · intro z w heq
    have he : stoppedPointMap A hc k z=stoppedPointMap A hc k w := congrArg Subtype.val heq
    have hp : gluedProjection Ak z.val=gluedProjection Ak w.val :=
      (stoppedPointMap_projection A hc k z).symm.trans
        ((congrArg (gluedProjection A) he).trans (stoppedPointMap_projection A hc k w))
    obtain ⟨i,hi,y,hy⟩ := exists_stopped_representative A hc k z
    have hzi : gluedProjection Ak z.val∈A.openSet i := by
      rw [←hy,gluedProjection_local_full]
      exact (((Ak.prefixTower i).append (Ak.tail i)).proj y).property
    have hw : w.val∈range (endpointLocalInclusion Ak i) := by
      rw [localInclusion_range]
      change gluedProjection Ak w.val∈A.openSet i
      exact hp ▸ hzi
    obtain ⟨t,ht⟩ := hw
    have hLocal := (stoppedPointMap_local A hc k z i hi y hy).symm.trans
      (he.trans (stoppedPointMap_local A hc k w i hi t ht))
    have hyt := (stoppedPrefixBiholomorphism ((A.prefixTower i).append (A.tail i)) k hi).injective
      ((endpointLocalInclusion_openEmbedding A i).injective hLocal)
    exact Subtype.ext (hy.symm.trans ((congrArg (endpointLocalInclusion Ak i) hyt).trans ht))
  · intro w
    obtain ⟨i,hi,hwi⟩ := (mem_stoppedBaseOpen A k _).mp w.property
    have hw : w.val∈range (endpointLocalInclusion A i) := by rw [localInclusion_range];exact hwi
    obtain ⟨y,hy⟩ := hw
    let e := stoppedPrefixBiholomorphism ((A.prefixTower i).append (A.tail i)) k hi
    let t : Ak.finalSpace i := e.symm y
    let q := endpointLocalInclusion Ak i t
    have hp : gluedProjection Ak q=gluedProjection A w.val := by
      change gluedProjection Ak (endpointLocalInclusion Ak i t)=gluedProjection A w.val
      rw [gluedProjection_local_full]
      change ((uniformPrefix ((A.prefixTower i).append (A.tail i)) k).2.proj t : X)=_
      rw [←stoppedPrefixBiholomorphism_projection _ k hi t]
      change (((A.prefixTower i).append (A.tail i)).proj (e (e.symm y)) : X)=_
      rw [e.apply_symm_apply]
      exact (gluedProjection_local_full A i y).symm.trans (congrArg (gluedProjection A) hy)
    let z : stoppedStageOpen A hc k := ⟨q,by
      change gluedProjection Ak q∈stoppedBaseOpen A k
      rw [hp]
      exact w.property⟩
    refine ⟨z,Subtype.ext ?_⟩
    change stoppedPointMap A hc k z=w.val
    rw [stoppedPointMap_local A hc k z i hi t rfl]
    change endpointLocalInclusion A i (e (e.symm y))=w.val
    rw [e.apply_symm_apply]
    exact hy

theorem stoppedPointMap_range (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ) (z : stoppedStageOpen A hc k)
    (i : J) (hi : ((A.prefixTower i).append (A.tail i)).length≤k)
    (hz : z.val∈localRangeOpen (uniformStageHistories A k) hc i) :
    stoppedPointMap A hc k z=(stoppedStageTerminalRangeBiholomorphism A hc i k hi ⟨z.val,hz⟩).val := by
  let a := localBiholomorphism (uniformStageHistories A k) hc i
  let y := a.symm ⟨z.val,hz⟩
  have hy : endpointLocalInclusion (uniformStageHistories A k) i y=z.val :=
    congrArg Subtype.val (a.apply_symm_apply ⟨z.val,hz⟩)
  exact stoppedPointMap_local A hc k z i hi y hy

theorem stoppedPointMap_contMDiff (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (stoppedPointMap A hc k) := by
  intro z
  obtain ⟨i,hi,y,hy⟩ := exists_stopped_representative A hc k z
  let R := localRangeOpen (uniformStageHistories A k) hc i
  let V : Opens (stoppedStageOpen A hc k) :=
    ⟨(Subtype.val : stoppedStageOpen A hc k → endpointManifold (uniformStageHistories A k) hc) ⁻¹' R,
      R.isOpen.preimage continuous_subtype_val⟩
  have hzV : z∈V := show z.val∈R from ⟨y,hy⟩
  have hLift : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (fun v : V => (⟨v.val.val,v.property⟩ : R)) :=
    contMDiff_opens_mk (contMDiff_subtype_val.comp contMDiff_subtype_val) (fun v => v.property)
  let e := stoppedStageTerminalRangeBiholomorphism A hc i k hi
  have hLoc : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (fun v : V => stoppedPointMap A hc k v.val) := by
    have hEq : (fun v : V => stoppedPointMap A hc k v.val)=
        fun v => (e ⟨v.val.val,v.property⟩).val :=
      funext (fun v => stoppedPointMap_range A hc k v.val i hi v.property)
    rw [hEq]
    exact contMDiff_subtype_val.comp (e.contMDiff.comp hLift)
  exact contMDiffAt_subtype_iff.mp (hLoc ⟨z,hzV⟩)

theorem stoppedOpenMap_contMDiff (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (stoppedOpenMap A hc k) :=
  contMDiff_opens_mk (stoppedPointMap_contMDiff A hc k) (fun z => (stoppedOpenMap A hc k z).property)

def stoppedOpenEquiv (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ) : stoppedStageOpen A hc k ≃ stoppedTerminalOpen A hc k :=
  Equiv.ofBijective (stoppedOpenMap A hc k) (stoppedOpenMap_bijective A hc k)

/-- The actual inverse's whole local formula follows from the proved forward bijection. -/
theorem stoppedOpenEquiv_symm_range (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ) (w : stoppedTerminalOpen A hc k)
    (i : J) (hi : ((A.prefixTower i).append (A.tail i)).length≤k)
    (hw : w.val∈localRangeOpen A hc i) :
    ((stoppedOpenEquiv A hc k).symm w).val=
      ((stoppedStageTerminalRangeBiholomorphism A hc i k hi).symm ⟨w.val,hw⟩).val := by
  let e := stoppedOpenEquiv A hc k
  let a := stoppedStageTerminalRangeBiholomorphism A hc i k hi
  let q := a.symm ⟨w.val,hw⟩
  have hp : gluedProjection (uniformStageHistories A k) q.val=gluedProjection A w.val := by
    have hh := stoppedStageTerminalRangeBiholomorphism_projection A hc i k hi q
    have hEq : (a q).val=w.val := congrArg Subtype.val (a.apply_symm_apply ⟨w.val,hw⟩)
    exact hh.symm.trans (congrArg (gluedProjection A) hEq)
  let z : stoppedStageOpen A hc k := ⟨q.val,by
    change gluedProjection (uniformStageHistories A k) q.val∈stoppedBaseOpen A k
    rw [hp]
    exact w.property⟩
  have hez : e z=w := by
    apply Subtype.ext
    change stoppedPointMap A hc k z=w.val
    rw [stoppedPointMap_range A hc k z i hi q.property]
    exact congrArg Subtype.val (a.apply_symm_apply ⟨w.val,hw⟩)
  have hInv : e.symm w=z := e.injective ((e.apply_symm_apply w).trans hez.symm)
  exact congrArg Subtype.val hInv

theorem stoppedOpenEquiv_symm_contMDiff (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (stoppedOpenEquiv A hc k).symm := by
  have hAmbient : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (fun w : stoppedTerminalOpen A hc k => ((stoppedOpenEquiv A hc k).symm w).val) := by
    intro w
    obtain ⟨i,hi,hwi⟩ := (mem_stoppedBaseOpen A k _).mp w.property
    let R := localRangeOpen A hc i
    have hwR : w.val∈R := by change w.val∈range (endpointLocalInclusion A i);rw [localInclusion_range];exact hwi
    let V : Opens (stoppedTerminalOpen A hc k) :=
      ⟨(Subtype.val : stoppedTerminalOpen A hc k → endpointManifold A hc) ⁻¹' R,
        R.isOpen.preimage continuous_subtype_val⟩
    have hLift : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
        (fun v : V => (⟨v.val.val,v.property⟩ : R)) :=
      contMDiff_opens_mk (contMDiff_subtype_val.comp contMDiff_subtype_val) (fun v => v.property)
    let a := stoppedStageTerminalRangeBiholomorphism A hc i k hi
    have hLoc : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
        (fun v : V => ((stoppedOpenEquiv A hc k).symm v.val).val) := by
      have hEq : (fun v : V => ((stoppedOpenEquiv A hc k).symm v.val).val)=
          fun v => (a.symm ⟨v.val.val,v.property⟩).val :=
        funext (fun v => stoppedOpenEquiv_symm_range A hc k v.val i hi v.property)
      rw [hEq]
      exact contMDiff_subtype_val.comp (a.symm.contMDiff.comp hLift)
    exact (contMDiffAt_subtype_iff (U := V)
      (f := fun u : stoppedTerminalOpen A hc k => ((stoppedOpenEquiv A hc k).symm u).val)
      (x := ⟨w,hwR⟩)).mp (hLoc ⟨w,hwR⟩)
  exact contMDiff_opens_mk hAmbient (fun w => ((stoppedOpenEquiv A hc k).symm w).property)

def stoppedOpenBiholomorphism (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ) :
    CMfd.of (n := n) (stoppedStageOpen A hc k) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (stoppedTerminalOpen A hc k) where
  toEquiv := stoppedOpenEquiv A hc k
  contMDiff_toFun := stoppedOpenMap_contMDiff A hc k
  contMDiff_invFun := stoppedOpenEquiv_symm_contMDiff A hc k

theorem stoppedOpenBiholomorphism_projection (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ) (z : stoppedStageOpen A hc k) :
    gluedProjection A (stoppedOpenBiholomorphism A hc k z).val=
      gluedProjection (uniformStageHistories A k) z.val := stoppedPointMap_projection A hc k z

theorem stoppedOpenBiholomorphism_local (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ) (z : stoppedStageOpen A hc k)
    (i : J) (hi : ((A.prefixTower i).append (A.tail i)).length≤k)
    (hz : z.val∈localRangeOpen (uniformStageHistories A k) hc i) :
    (stoppedOpenBiholomorphism A hc k z).val=
      (stoppedStageTerminalRangeBiholomorphism A hc i k hi ⟨z.val,hz⟩).val :=
  stoppedPointMap_range A hc k z i hi hz

theorem stoppedBaseOpen_mono (A : ActualEndpointHistories X J) {k l : ℕ} (hkl : k≤l) :
    stoppedBaseOpen A k≤stoppedBaseOpen A l := by
  intro x hx
  obtain ⟨i,hi,hxi⟩ := (mem_stoppedBaseOpen A k x).mp hx
  exact (mem_stoppedBaseOpen A l x).mpr ⟨i,hi.trans hkl,hxi⟩

theorem stoppedBaseOpen_cover (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (x : X) : ∃ k,x∈stoppedBaseOpen A k := by
  obtain ⟨i,hxi⟩ := hc x
  exact ⟨((A.prefixTower i).append (A.tail i)).length,
    (mem_stoppedBaseOpen A _ x).mpr ⟨i,le_refl _,hxi⟩⟩

section OriginalInput
variable (hn : 0<n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : NormalCrossings.IsSNCDivisor n E)
  (hdense : W⊆closure (W \ ⋃ H∈E,H)) (hr : ∀ x∈W,RegularAtDim (n := n) W x 1)

/-- Original geometry supplies the actual atlas, every map and its proved inverse internally. -/
def originalStoppedOpenBiholomorphism (k : ℕ) :
    let A := originalEndpointHistories hn hW hE hdense hr
    let hc := originalEndpointHistories_cover hn hW hE hdense hr
    CMfd.of (n := n) (stoppedStageOpen A hc k) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (stoppedTerminalOpen A hc k) :=
  stoppedOpenBiholomorphism (originalEndpointHistories hn hW hE hdense hr)
    (originalEndpointHistories_cover hn hW hE hdense hr) k

theorem originalStoppedOpenBiholomorphism_projection (k : ℕ) :
    let A := originalEndpointHistories hn hW hE hdense hr
    let hc := originalEndpointHistories_cover hn hW hE hdense hr
    ∀ z : stoppedStageOpen A hc k,
      gluedProjection A (originalStoppedOpenBiholomorphism hn hW hE hdense hr k z).val=
        gluedProjection (uniformStageHistories A k) z.val := by
  dsimp only
  intro z
  exact stoppedOpenBiholomorphism_projection (originalEndpointHistories hn hW hE hdense hr)
    (originalEndpointHistories_cover hn hW hE hdense hr) k z

theorem originalStoppedOpen_point_mem (x : X) :
    let A := originalEndpointHistories hn hW hE hdense hr
    x∈stoppedBaseOpen A ((A.prefixTower x).append (A.tail x)).length :=
  (mem_stoppedBaseOpen (originalEndpointHistories hn hW hE hdense hr) _ x).mpr
    ⟨x,le_refl _,originalEndpointHistories_point_mem hn hW hE hdense hr x⟩

end OriginalInput

end
end Hironaka.HironakaSharpActualCurveStoppedOpenGluing
