/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalTerminalOverlapRestriction
import Hironaka.Resolution.HironakaEmbeddedResolutionLocal
import Mathlib.Topology.Gluing
/-! Original-input canonical terminal atlases and actual topological gluing.
Complete initial four-node mathematics preceded code; the additional real range
dictionary node was completed before its new projection/range proof code. Genuine singleton local drivers
supply every local history internally before any overlap/gluing construction. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
open CategoryTheory CategoryTheory.Limits
universe u
namespace Hironaka.HironakaOriginalTerminalAtlas
noncomputable section
open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms CanonicalCentres MaxLocusLocal
  HironakaOriginalTerminalOverlapComparison HironakaOriginalTerminalOverlapRestriction
open MarkedIdealBiholomorphism.MarkedIdeal (pullback)
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {X : CMfd.{u} n}

/-- Actual OUTPUT data, constructed below from ONLY original marked input.
No caller local-resolution/CAN/cover/transition certificate is an input. -/
structure ActualLocalTerminalAtlas (M : MarkedIdeal n X) : Type (u+1) where
  openSet : X → Opens X
  point_mem : ∀ x, x ∈ openSet x
  finalSpace : X → CMfd.{u} n
  tower : ∀ x, BlowupTower (CMfd.of (n := n) (openSet x)) (finalSpace x)
  canonical : ∀ x, IsCanonical (pullback (Subtype.val : openSet x → X) M)
    ((canonicalInvariant n).inv (pullback (Subtype.val : openSet x → X) M)) (tower x)
  terminal : ∀ x, IsGeoResolution (pullback (Subtype.val : openSet x → X) M) (tower x)

/-- Original domain and actual compact SINGLETONS internally construct ONE
actual point-indexed covering family of canonical terminal local histories. -/
def actualLocalTerminalAtlas (M : MarkedIdeal n X) (hM : IsInvDomain n M) :
    ActualLocalTerminalAtlas M := by
  have hx : ∀ x : X, ∃ U : Opens X, x ∈ U ∧ ∃ (Y : CMfd.{u} n)
      (T : BlowupTower (CMfd.of (n := n) U) Y),
      IsCanonical (pullback (Subtype.val : U → X) M)
        ((canonicalInvariant n).inv (pullback (Subtype.val : U → X) M)) T ∧
      IsGeoResolution (pullback (Subtype.val : U → X) M) T := by
    intro x
    obtain ⟨U,hKU,Y,T,hc,hr⟩ := HironakaEmbeddedResolutionLocal.exists_local_resolution_isCanonical
      (canonicalInvariant n) hM (K := ({x} : Set X)) isCompact_singleton
    exact ⟨U,hKU (Set.mem_singleton x),Y,T,hc,hr⟩
  choose U hU Y T hc hr using hx
  exact ⟨U,hU,Y,T,hc,hr⟩

def originalTerminalOverlapOpen (M : MarkedIdeal n X) (hM : IsInvDomain n M) (i j : X) :
    Opens ((actualLocalTerminalAtlas M hM).finalSpace i) :=
  openPreimage ((actualLocalTerminalAtlas M hM).tower i)
    (nestedOpens ((actualLocalTerminalAtlas M hM).openSet i) ((actualLocalTerminalAtlas M hM).openSet j))

theorem originalTerminalOverlapOpen_eq_pair (M : MarkedIdeal n X) (hM : IsInvDomain n M) (i j : X) :
    originalTerminalOverlapOpen M hM i j=
      openPreimage ((actualLocalTerminalAtlas M hM).tower i)
        (nestedOpens ((actualLocalTerminalAtlas M hM).openSet i)
          (((actualLocalTerminalAtlas M hM).openSet i) ⊓ ((actualLocalTerminalAtlas M hM).openSet j))) := by
  apply Opens.ext
  ext y
  change (((actualLocalTerminalAtlas M hM).tower i).proj y).val ∈ (actualLocalTerminalAtlas M hM).openSet j ↔
    (((actualLocalTerminalAtlas M hM).tower i).proj y).val ∈
      ((actualLocalTerminalAtlas M hM).openSet i) ⊓ ((actualLocalTerminalAtlas M hM).openSet j)
  exact ⟨fun hy => ⟨(((actualLocalTerminalAtlas M hM).tower i).proj y).property,hy⟩,fun hy => hy.2⟩

def originalTerminalTransition (M : MarkedIdeal n X) (hM : IsInvDomain n M) (i j : X) :
    CMfd.of (n := n) (originalTerminalOverlapOpen M hM i j)
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (originalTerminalOverlapOpen M hM j i) := by
  let A := actualLocalTerminalAtlas M hM
  let η := commonOpenTerminalComparison M hM (W := A.openSet i ⊓ A.openSet j) inf_le_left inf_le_right
    (A.tower i) (A.tower j) (A.canonical i) (A.canonical j) (A.terminal i) (A.terminal j)
  have htarget : openPreimage (A.tower j) (nestedOpens (A.openSet j) (A.openSet i ⊓ A.openSet j))=
      originalTerminalOverlapOpen M hM j i := by
    rw [inf_comm]
    exact (originalTerminalOverlapOpen_eq_pair M hM j i).symm
  exact ((BlowupTowerIsoTail.opensCongr (originalTerminalOverlapOpen_eq_pair M hM i j)).trans η).trans
    (BlowupTowerIsoTail.opensCongr htarget)

theorem originalTerminalTransition_pair_point (M : MarkedIdeal n X) (hM : IsInvDomain n M) (i j : X)
    (y : originalTerminalOverlapOpen M hM i j) :
    (originalTerminalTransition M hM i j y).val=
      (commonOpenTerminalComparison M hM
        (W := (actualLocalTerminalAtlas M hM).openSet i ⊓ (actualLocalTerminalAtlas M hM).openSet j)
        inf_le_left inf_le_right
        ((actualLocalTerminalAtlas M hM).tower i) ((actualLocalTerminalAtlas M hM).tower j)
        ((actualLocalTerminalAtlas M hM).canonical i) ((actualLocalTerminalAtlas M hM).canonical j)
        ((actualLocalTerminalAtlas M hM).terminal i) ((actualLocalTerminalAtlas M hM).terminal j)
        ⟨y.val,⟨(((actualLocalTerminalAtlas M hM).tower i).proj y.val).property,y.property⟩⟩).val := rfl

theorem originalTerminalTransition_proj (M : MarkedIdeal n X) (hM : IsInvDomain n M) (i j : X)
    (y : originalTerminalOverlapOpen M hM i j) :
    (((actualLocalTerminalAtlas M hM).tower j).proj (originalTerminalTransition M hM i j y).val).val=
      (((actualLocalTerminalAtlas M hM).tower i).proj y.val).val := by
  rw [originalTerminalTransition_pair_point,commonOpenTerminalComparison_proj]

theorem originalTerminalOverlapOpen_self (M : MarkedIdeal n X) (hM : IsInvDomain n M) (i : X) :
    originalTerminalOverlapOpen M hM i i=⊤ := by
  apply Opens.ext
  ext y
  change (((actualLocalTerminalAtlas M hM).tower i).proj y).val ∈
    (actualLocalTerminalAtlas M hM).openSet i ↔ True
  exact ⟨fun _ => trivial,fun _ => (((actualLocalTerminalAtlas M hM).tower i).proj y).property⟩

theorem originalTerminalTransition_self (M : MarkedIdeal n X) (hM : IsInvDomain n M) (i : X) :
    originalTerminalTransition M hM i i=
      Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) (originalTerminalOverlapOpen M hM i i)) ∞ := by
  exact biholomorphisms_eq_of_common_open_original_proj_eq ((actualLocalTerminalAtlas M hM).tower i)
    _ _ (originalTerminalTransition_proj M hM i i)

theorem originalTerminalTransition_inter (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (i j k : X) (y : originalTerminalOverlapOpen M hM i j)
    (hy : y.val ∈ originalTerminalOverlapOpen M hM i k) :
    (originalTerminalTransition M hM i j y).val ∈ originalTerminalOverlapOpen M hM j k := by
  change (((actualLocalTerminalAtlas M hM).tower j).proj
    (originalTerminalTransition M hM i j y).val).val ∈ (actualLocalTerminalAtlas M hM).openSet k
  rw [originalTerminalTransition_proj]
  exact hy

theorem originalTerminalTransition_cocycle (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (i j k : X) (y : originalTerminalOverlapOpen M hM i j)
    (hy : y.val ∈ originalTerminalOverlapOpen M hM i k) :
    (originalTerminalTransition M hM j k
      ⟨(originalTerminalTransition M hM i j y).val,originalTerminalTransition_inter M hM i j k y hy⟩).val=
      (originalTerminalTransition M hM i k ⟨y.val,hy⟩).val := by
  let A := actualLocalTerminalAtlas M hM
  let yp : openPreimage (A.tower i) (nestedOpens (A.openSet i) (A.openSet i ⊓ A.openSet j)) :=
    ⟨y.val,⟨((A.tower i).proj y.val).property,y.property⟩⟩
  have hyk : ((A.tower i).proj y.val).val ∈ A.openSet k := hy
  obtain ⟨z,hz,hc⟩ := original_pairwise_terminal_triple_transition M hM (A.openSet i) (A.openSet j)
    (A.openSet k) (A.tower i) (A.tower j) (A.tower k)
    (A.canonical i) (A.canonical j) (A.canonical k) (A.terminal i) (A.terminal j) (A.terminal k) yp hyk
  let q : originalTerminalOverlapOpen M hM j k :=
    ⟨(originalTerminalTransition M hM i j y).val,originalTerminalTransition_inter M hM i j k y hy⟩
  let zp : openPreimage (A.tower j) (nestedOpens (A.openSet j) (A.openSet j ⊓ A.openSet k)) :=
    ⟨q.val,⟨((A.tower j).proj q.val).property,q.property⟩⟩
  have hzp : z=zp := by
    apply Subtype.ext
    change z.val=(originalTerminalTransition M hM i j y).val
    rw [originalTerminalTransition_pair_point]
    exact hz
  rw [hzp] at hc
  have hleft := originalTerminalTransition_pair_point M hM j k q
  have hright := originalTerminalTransition_pair_point M hM i k ⟨y.val,hy⟩
  exact hleft.trans (hc.trans hright.symm)

/-- ONLY original M/domain: all actual local objects, true transitions and
every gluing field have been constructed internally from genuine producers. -/
def originalTerminalGlueCore (M : MarkedIdeal n X) (hM : IsInvDomain n M) : TopCat.GlueData.MkCore where
  J := X
  U i := TopCat.of ((actualLocalTerminalAtlas M hM).finalSpace i)
  V := originalTerminalOverlapOpen M hM
  t i j := TopCat.ofHom ⟨originalTerminalTransition M hM i j,
    (originalTerminalTransition M hM i j).contMDiff.continuous⟩
  V_id := originalTerminalOverlapOpen_self M hM
  t_id := by
    intro i
    funext y
    change originalTerminalTransition M hM i i y=y
    rw [originalTerminalTransition_self]
    rfl
  t_inter := fun {i j} k y hy => originalTerminalTransition_inter M hM i j k y hy
  cocycle := originalTerminalTransition_cocycle M hM

def originalTerminalGlueData (M : MarkedIdeal n X) (hM : IsInvDomain n M) : TopCat.GlueData :=
  TopCat.GlueData.mk' (originalTerminalGlueCore M hM)

def originalTerminalGluedSpace (M : MarkedIdeal n X) (hM : IsInvDomain n M) : TopCat :=
  (originalTerminalGlueData M hM).glued

def originalTerminalLocalInclusion (M : MarkedIdeal n X) (hM : IsInvDomain n M) (i : X) :
    (actualLocalTerminalAtlas M hM).finalSpace i → originalTerminalGluedSpace M hM :=
  (originalTerminalGlueData M hM).ι i

theorem originalTerminalLocalInclusion_openEmbedding (M : MarkedIdeal n X) (hM : IsInvDomain n M) (i : X) :
    Topology.IsOpenEmbedding (originalTerminalLocalInclusion M hM i) :=
  (originalTerminalGlueData M hM).ι_isOpenEmbedding i

theorem originalTerminalLocalInclusion_jointly_surjective (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (z : originalTerminalGluedSpace M hM) :
    ∃ (i : X) (y : (actualLocalTerminalAtlas M hM).finalSpace i), originalTerminalLocalInclusion M hM i y=z :=
  (originalTerminalGlueData M hM).ι_jointly_surjective z

def originalTerminalLocalProjection (M : MarkedIdeal n X) (hM : IsInvDomain n M) (i : X) :
    ContinuousMap ((actualLocalTerminalAtlas M hM).finalSpace i) X :=
  ⟨fun y => (((actualLocalTerminalAtlas M hM).tower i).proj y).val,
    continuous_subtype_val.comp ((actualLocalTerminalAtlas M hM).tower i).contMDiff_proj.continuous⟩

theorem originalTerminalLocalProjection_compatible (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (ij : X × X) :
    (originalTerminalGlueData M hM).toGlueData.diagram.fst ij ≫
      TopCat.ofHom (originalTerminalLocalProjection M hM ij.1)=
    (originalTerminalGlueData M hM).toGlueData.diagram.snd ij ≫
      TopCat.ofHom (originalTerminalLocalProjection M hM ij.2) := by
  rcases ij with ⟨i,j⟩
  ext y
  exact (originalTerminalTransition_proj M hM i j y).symm

def originalTerminalGluedProjection (M : MarkedIdeal n X) (hM : IsInvDomain n M) :
    ContinuousMap (originalTerminalGluedSpace M hM) X :=
  (Multicoequalizer.desc (originalTerminalGlueData M hM).toGlueData.diagram (TopCat.of X)
    (fun i => TopCat.ofHom (originalTerminalLocalProjection M hM i))
    (originalTerminalLocalProjection_compatible M hM)).hom

theorem originalTerminalGluedProjection_local (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (i : X) (y : (actualLocalTerminalAtlas M hM).finalSpace i) :
    originalTerminalGluedProjection M hM (originalTerminalLocalInclusion M hM i y)=
      originalTerminalLocalProjection M hM i y := by
  have h := Multicoequalizer.π_desc (originalTerminalGlueData M hM).toGlueData.diagram (TopCat.of X)
    (fun i => TopCat.ofHom (originalTerminalLocalProjection M hM i))
    (originalTerminalLocalProjection_compatible M hM) i
  exact congrArg (fun f : (originalTerminalGlueData M hM).U i ⟶ TopCat.of X => f y) h

theorem originalTerminalGluedProjection_unique (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (q : ContinuousMap (originalTerminalGluedSpace M hM) X)
    (hq : ∀ (i : X) (y : (actualLocalTerminalAtlas M hM).finalSpace i),
      q (originalTerminalLocalInclusion M hM i y)=originalTerminalLocalProjection M hM i y) :
    q=originalTerminalGluedProjection M hM := by
  apply ContinuousMap.ext
  intro z
  obtain ⟨i,y,rfl⟩ := originalTerminalLocalInclusion_jointly_surjective M hM z
  exact (hq i y).trans (originalTerminalGluedProjection_local M hM i y).symm

/-- The ENTIRE saturated range is a true consequence of actual overlap
membership and the REAL gluing condition; no surjectivity of P is assumed. -/
theorem originalTerminalLocalInclusion_range (M : MarkedIdeal n X) (hM : IsInvDomain n M) (i : X) :
    range (originalTerminalLocalInclusion M hM i)=
      (originalTerminalGluedProjection M hM) ⁻¹' ((actualLocalTerminalAtlas M hM).openSet i : Set X) := by
  ext z
  constructor
  · rintro ⟨y,rfl⟩
    change originalTerminalGluedProjection M hM (originalTerminalLocalInclusion M hM i y) ∈
      (actualLocalTerminalAtlas M hM).openSet i
    rw [originalTerminalGluedProjection_local]
    exact (((actualLocalTerminalAtlas M hM).tower i).proj y).property
  · intro hz
    obtain ⟨j,y,rfl⟩ := originalTerminalLocalInclusion_jointly_surjective M hM z
    change originalTerminalGluedProjection M hM (originalTerminalLocalInclusion M hM j y) ∈
      (actualLocalTerminalAtlas M hM).openSet i at hz
    rw [originalTerminalGluedProjection_local] at hz
    have hy : y ∈ originalTerminalOverlapOpen M hM j i := hz
    let s : originalTerminalOverlapOpen M hM j i := ⟨y,hy⟩
    refine ⟨(originalTerminalTransition M hM j i s).val,?_⟩
    have hc := (originalTerminalGlueData M hM).toGlueData.glue_condition j i
    exact congrArg (fun f : (originalTerminalGlueData M hM).V (j,i) ⟶
      (originalTerminalGlueData M hM).glued => f s) hc

end
end Hironaka.HironakaOriginalTerminalAtlas
