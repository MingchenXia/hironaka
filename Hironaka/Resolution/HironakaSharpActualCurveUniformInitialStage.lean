/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveGlobalSuccessorBlowup

/-! The actual zero-stage projection itself is the original-space
biholomorphism, with its holomorphic inverse constructed on real original opens. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveUniformInitialStage
noncomputable section
open Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualCurveUniformPrefixes HironakaSharpActualCurveUniformPrefixSuccessors
  HironakaSharpActualCurveUniformStageAtlas HironakaSharpActualCurveTopologicalGluing
  HironakaSharpActualCurveGluedProjection HironakaSharpActualCurveGlobalManifold
  HironakaSharpActualCurveOriginalRecipeAtlas
attribute [local instance] endpointChartedSpace
variable {n : ℕ} {X Y : CMfd.{u} n} {J : Type u}

private theorem actual_zero_prefix_inverse (T : BlowupTower X Y) :
    ∃ e : (uniformPrefix T 0).1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X,
      ∀ z,e z=(uniformPrefix T 0).2.proj z := by
  let P : (Σ V : CMfd.{u} n,BlowupTower X V) → Prop := fun R =>
    ∃ e : R.1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X,∀ z,e z=R.2.proj z
  have hRefl : P ⟨X,BlowupTower.refl⟩ := ⟨Diffeomorph.refl _ _ _,fun _ => rfl⟩
  exact Eq.mpr (congrArg P (uniformPrefix_zero T)) hRefl

def zeroPrefixBiholomorphism (T : BlowupTower X Y) :
    (uniformPrefix T 0).1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X :=
  Classical.choose (actual_zero_prefix_inverse T)

theorem zeroPrefixBiholomorphism_point (T : BlowupTower X Y) (z : (uniformPrefix T 0).1) :
    zeroPrefixBiholomorphism T z=(uniformPrefix T 0).2.proj z :=
  Classical.choose_spec (actual_zero_prefix_inverse T) z

private theorem actual_zero_projection_local (A : ActualEndpointHistories X J)
    (i : J) (z : (uniformStageHistories A 0).finalSpace i) :
    gluedProjection (uniformStageHistories A 0)
      (endpointLocalInclusion (uniformStageHistories A 0) i z)=
        (zeroPrefixBiholomorphism ((A.prefixTower i).append (A.tail i)) z).val := by
  rw [gluedProjection_local_full]
  change ((uniformPrefix ((A.prefixTower i).append (A.tail i)) 0).2.proj z : X)=_
  exact (congrArg Subtype.val (zeroPrefixBiholomorphism_point _ z)).symm

theorem initialProjection_bijective (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) :
    Function.Bijective (gluedProjection (uniformStageHistories A 0)) := by
  constructor
  · intro z w hzw
    obtain ⟨i,hi⟩ := hc (gluedProjection (uniformStageHistories A 0) z)
    have hz : z∈range (endpointLocalInclusion (uniformStageHistories A 0) i) := by
      rw [localInclusion_range]
      exact hi
    have hw : w∈range (endpointLocalInclusion (uniformStageHistories A 0) i) := by
      rw [localInclusion_range]
      change gluedProjection (uniformStageHistories A 0) w∈A.openSet i
      exact hzw ▸ hi
    obtain ⟨a,rfl⟩ := hz
    obtain ⟨b,rfl⟩ := hw
    have hab : zeroPrefixBiholomorphism ((A.prefixTower i).append (A.tail i)) a=
        zeroPrefixBiholomorphism ((A.prefixTower i).append (A.tail i)) b := by
      apply Subtype.ext
      exact (actual_zero_projection_local A i a).symm.trans
        (hzw.trans (actual_zero_projection_local A i b))
    exact congrArg (endpointLocalInclusion (uniformStageHistories A 0) i)
      ((zeroPrefixBiholomorphism _).injective hab)
  · intro x
    obtain ⟨i,hi⟩ := hc x
    let e := zeroPrefixBiholomorphism ((A.prefixTower i).append (A.tail i))
    refine ⟨endpointLocalInclusion (uniformStageHistories A 0) i (e.symm ⟨x,hi⟩),?_⟩
    exact (actual_zero_projection_local A i _).trans (congrArg Subtype.val (e.apply_symm_apply ⟨x,hi⟩))

/-- Underlying map is exactly the already constructed actual projection. -/
def initialProjectionBiholomorphism (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) :
    endpointManifold (uniformStageHistories A 0) hc
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X := by
  let e := Equiv.ofBijective (gluedProjection (uniformStageHistories A 0)) (initialProjection_bijective A hc)
  have hInv : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (e.symm : X → endpointManifold (uniformStageHistories A 0) hc) := by
    intro x
    obtain ⟨i,hi⟩ := hc x
    let a := zeroPrefixBiholomorphism ((A.prefixTower i).append (A.tail i))
    have hPoint (z : A.openSet i) :
        e.symm z.val=endpointLocalInclusion (uniformStageHistories A 0) i (a.symm z) := by
      apply e.injective
      exact (e.apply_symm_apply z.val).trans
        ((actual_zero_projection_local A i (a.symm z)).trans
          (congrArg Subtype.val (a.apply_symm_apply z))).symm
    have hLoc : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
        (fun z : A.openSet i => e.symm z.val) := by
      have hEq : (fun z : A.openSet i => e.symm z.val)=
          (endpointLocalInclusion (uniformStageHistories A 0) i) ∘ a.symm := funext hPoint
      rw [hEq]
      exact (localInclusion_contMDiff (uniformStageHistories A 0) hc i).comp a.symm.contMDiff
    exact contMDiffAt_subtype_iff.mp (hLoc ⟨x,hi⟩)
  exact {
    toEquiv := e
    contMDiff_toFun := gluedProjection_contMDiff (uniformStageHistories A 0) hc
    contMDiff_invFun := hInv }

theorem initialProjectionBiholomorphism_point (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i)
    (z : endpointManifold (uniformStageHistories A 0) hc) :
    initialProjectionBiholomorphism A hc z=gluedProjection (uniformStageHistories A 0) z := rfl

section OriginalInput
variable (hn : 0<n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : NormalCrossings.IsSNCDivisor n E)
  (hdense : W⊆closure (W \ ⋃ H∈E,H)) (hr : ∀ x∈W,RegularAtDim (n := n) W x 1)

def originalInitialBiholomorphism :
    originalUniformStageManifold hn hW hE hdense hr 0
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X :=
  initialProjectionBiholomorphism (originalEndpointHistories hn hW hE hdense hr)
    (originalEndpointHistories_cover hn hW hE hdense hr)

theorem originalInitialBiholomorphism_point
    (z : originalUniformStageManifold hn hW hE hdense hr 0) :
    originalInitialBiholomorphism hn hW hE hdense hr z=
      originalUniformStageProjection hn hW hE hdense hr 0 z := rfl

end OriginalInput
end
end Hironaka.HironakaSharpActualCurveUniformInitialStage
