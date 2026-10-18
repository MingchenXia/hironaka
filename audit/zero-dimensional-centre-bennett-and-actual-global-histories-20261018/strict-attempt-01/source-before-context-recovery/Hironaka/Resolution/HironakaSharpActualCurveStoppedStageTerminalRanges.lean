/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveLocalStationaryCentres

/-! Whole actual prefix packets give genuine same-terminal history
isomorphisms and stopped-stage/terminal range biholomorphisms. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveStoppedStageTerminalRanges
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerIsomorphism
  HironakaSharpActualCurveUniformPrefixes HironakaSharpActualCurveUniformPrefixSuccessors
  HironakaSharpActualCurveEmptyPadding HironakaSharpActualCurveUniformStageAtlas
  HironakaSharpActualCurveTopologicalGluing HironakaSharpActualCurveGluedProjection
  HironakaSharpActualCurveGlobalManifold HironakaSharpActualCurveOriginalRecipeAtlas
  HironakaSharpActualCurveLocalRangeBiholomorphism
attribute [local instance] endpointChartedSpace
variable {n : ℕ} {X Y : CMfd.{u} n} {J : Type u}

private theorem actual_stopped_prefix_identification (T : BlowupTower X Y)
    (k : ℕ) (hk : T.length≤k) :
    ∃ e : (uniformPrefix T k).1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y,
      IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞)
        (uniformPrefix T k).2 (T.append (identityEmptyTail Y (k-T.length))) e := by
  let S := T.append (identityEmptyTail Y (k-T.length))
  let P : (Σ V : CMfd.{u} n,BlowupTower X V) → Prop := fun R =>
    ∃ e : R.1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y,
      IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) R.2 S e
  have hSame : P ⟨Y,S⟩ := ⟨Diffeomorph.refl _ _ _,IsTowerIso.refl_self S⟩
  exact Eq.mpr (congrArg P (uniformPrefix_of_length_le T k hk)) hSame

def stoppedPrefixBiholomorphism (T : BlowupTower X Y) (k : ℕ) (hk : T.length≤k) :
    (uniformPrefix T k).1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y :=
  Classical.choose (actual_stopped_prefix_identification T k hk)

theorem stoppedPrefixBiholomorphism_stagewise (T : BlowupTower X Y)
    (k : ℕ) (hk : T.length≤k) :
    IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞)
      (uniformPrefix T k).2 (T.append (identityEmptyTail Y (k-T.length)))
      (stoppedPrefixBiholomorphism T k hk) :=
  Classical.choose_spec (actual_stopped_prefix_identification T k hk)

theorem stoppedPrefixBiholomorphism_projection (T : BlowupTower X Y)
    (k : ℕ) (hk : T.length≤k) (z : (uniformPrefix T k).1) :
    T.proj (stoppedPrefixBiholomorphism T k hk z)=(uniformPrefix T k).2.proj z := by
  have h := (stoppedPrefixBiholomorphism_stagewise T k hk).proj_comm z
  change (uniformPrefix T k).2.proj z=
    (T.append (identityEmptyTail Y (k-T.length))).proj (stoppedPrefixBiholomorphism T k hk z) at h
  rw [BlowupTower.proj_append,identityEmptyTail_proj,Function.comp_id] at h
  exact h.symm

/-- These are actual already constructed ranges, not a supplied comparison atlas. -/
def stoppedStageTerminalRangeBiholomorphism (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (i : J) (k : ℕ)
    (hk : ((A.prefixTower i).append (A.tail i)).length≤k) :
    CMfd.of (n := n) (localRangeOpen (uniformStageHistories A k) hc i)
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (localRangeOpen A hc i) :=
  (localBiholomorphism (uniformStageHistories A k) hc i).symm.trans
    ((stoppedPrefixBiholomorphism ((A.prefixTower i).append (A.tail i)) k hk).trans
      (localBiholomorphism A hc i))

theorem stoppedStageTerminalRangeBiholomorphism_projection (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (i : J) (k : ℕ)
    (hk : ((A.prefixTower i).append (A.tail i)).length≤k)
    (q : localRangeOpen (uniformStageHistories A k) hc i) :
    gluedProjection A (stoppedStageTerminalRangeBiholomorphism A hc i k hk q).val=
      gluedProjection (uniformStageHistories A k) q.val := by
  let a := localBiholomorphism (uniformStageHistories A k) hc i
  let b := stoppedPrefixBiholomorphism ((A.prefixTower i).append (A.tail i)) k hk
  let z := a.symm q
  have hInv : endpointLocalInclusion (uniformStageHistories A k) i z=q.val :=
    congrArg Subtype.val (a.apply_symm_apply q)
  calc
    gluedProjection A (stoppedStageTerminalRangeBiholomorphism A hc i k hk q).val=
        (((A.prefixTower i).append (A.tail i)).proj (b z) : X) :=
      gluedProjection_local_full A i (b z)
    _=((uniformPrefix ((A.prefixTower i).append (A.tail i)) k).2.proj z : X) :=
      congrArg Subtype.val (stoppedPrefixBiholomorphism_projection _ k hk z)
    _=gluedProjection (uniformStageHistories A k) (endpointLocalInclusion (uniformStageHistories A k) i z) :=
      (gluedProjection_local_full (uniformStageHistories A k) i z).symm
    _=gluedProjection (uniformStageHistories A k) q.val :=
      congrArg (gluedProjection (uniformStageHistories A k)) hInv

section OriginalInput
variable (hn : 0<n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : NormalCrossings.IsSNCDivisor n E)
  (hdense : W⊆closure (W \ ⋃ H∈E,H)) (hr : ∀ x∈W,RegularAtDim (n := n) W x 1)

def originalStoppedStageTerminalRangeBiholomorphism (x : X) (r : ℕ) :
    let A := originalEndpointHistories hn hW hE hdense hr
    let hc := originalEndpointHistories_cover hn hW hE hdense hr
    let L := ((A.prefixTower x).append (A.tail x)).length
    CMfd.of (n := n) (localRangeOpen (uniformStageHistories A (L+r)) hc x)
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (localRangeOpen A hc x) :=
  stoppedStageTerminalRangeBiholomorphism (originalEndpointHistories hn hW hE hdense hr)
    (originalEndpointHistories_cover hn hW hE hdense hr) x _ (by omega)

theorem originalStoppedStageTerminalRangeBiholomorphism_projection (x : X) (r : ℕ) :
    let A := originalEndpointHistories hn hW hE hdense hr
    let hc := originalEndpointHistories_cover hn hW hE hdense hr
    let L := ((A.prefixTower x).append (A.tail x)).length
    ∀ q : localRangeOpen (uniformStageHistories A (L+r)) hc x,
      gluedProjection A (originalStoppedStageTerminalRangeBiholomorphism hn hW hE hdense hr x r q).val=
        gluedProjection (uniformStageHistories A (L+r)) q.val := by
  dsimp only
  intro q
  exact stoppedStageTerminalRangeBiholomorphism_projection (originalEndpointHistories hn hW hE hdense hr)
    (originalEndpointHistories_cover hn hW hE hdense hr) x
    ((((originalEndpointHistories hn hW hE hdense hr).prefixTower x).append
      ((originalEndpointHistories hn hW hE hdense hr).tail x)).length+r) (by omega) q

end OriginalInput
end
end Hironaka.HironakaSharpActualCurveStoppedStageTerminalRanges
