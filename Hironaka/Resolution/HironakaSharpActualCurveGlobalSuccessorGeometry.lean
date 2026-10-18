/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveGlobalSuccessorMap

/-! Genuine actual source charts, one-blowup fibres and whole projection
factorization give actual global successor complex/proper geometry. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
open IsManifold
universe u
namespace Hironaka.HironakaSharpActualCurveGlobalSuccessorGeometry
noncomputable section
open Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualCurveUniformPrefixes HironakaSharpActualCurveUniformStageAtlas
  HironakaSharpActualCurveUniformSuccessorComparison HironakaSharpActualCurveGlobalSuccessorMap
  HironakaSharpActualCurveTopologicalGluing HironakaSharpActualCurveGluedProjection
  HironakaSharpActualCurveGlobalManifold HironakaSharpActualCurveOriginalRecipeAtlas
attribute [local instance] endpointChartedSpace
variable {n : ℕ} {X : CMfd.{u} n} {J : Type u}

theorem globalUniformSuccessor_contMDiff (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (k : ℕ) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (globalUniformSuccessor A k : endpointManifold (uniformStageHistories A (k+1)) hc →
        endpointManifold (uniformStageHistories A k) hc) := by
  intro z
  obtain ⟨i,x,rfl⟩ := endpointLocalInclusion_jointly_surjective (uniformStageHistories A (k+1)) z
  let e := chartAt (ComplexModel n) x
  let c := e.lift_openEmbedding (endpointLocalInclusion_openEmbedding (uniformStageHistories A (k+1)) i)
  have hcAtlas : c∈atlas (ComplexModel n) (endpointManifold (uniformStageHistories A (k+1)) hc) :=
    ⟨i,e,chart_mem_atlas (ComplexModel n) x,rfl⟩
  have hx : x∈e.source := mem_chart_source (ComplexModel n) x
  have hz : endpointLocalInclusion (uniformStageHistories A (k+1)) i x∈c.source := ⟨x,hx,rfl⟩
  have heMax : e∈maximalAtlas 𝓘(ℂ,ComplexModel n) ∞ ((uniformStageHistories A (k+1)).finalSpace i) :=
    chart_mem_maximalAtlas x
  have hcMax : c∈maximalAtlas 𝓘(ℂ,ComplexModel n) ∞
      (endpointManifold (uniformStageHistories A (k+1)) hc) := subset_maximalAtlas hcAtlas
  have hlocal : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (localUniformSuccessorToGlue A k i : (uniformStageHistories A (k+1)).finalSpace i →
        endpointManifold (uniformStageHistories A k) hc) :=
    (localInclusion_contMDiff (uniformStageHistories A k) hc i).comp (localUniformSuccessor_contMDiff A k i)
  have hcx : c (endpointLocalInclusion (uniformStageHistories A (k+1)) i x)=e x :=
    e.lift_openEmbedding_apply (endpointLocalInclusion_openEmbedding (uniformStageHistories A (k+1)) i)
  have hsinv : ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ e.symm
      (c (endpointLocalInclusion (uniformStageHistories A (k+1)) i x)) :=
    contMDiffAt_symm_of_mem_maximalAtlas heMax (by rw [hcx];exact e.map_source hx)
  have hh := (hlocal.contMDiffAt.comp _ hsinv).comp _ (contMDiffAt_of_mem_maximalAtlas hcMax hz)
  apply hh.congr_of_eventuallyEq
  filter_upwards [c.open_source.mem_nhds hz] with y hy
  obtain ⟨b,hb,rfl⟩ := hy
  change globalUniformSuccessor A k (endpointLocalInclusion (uniformStageHistories A (k+1)) i b)=
    localUniformSuccessorToGlue A k i (e.symm (c (endpointLocalInclusion (uniformStageHistories A (k+1)) i b)))
  rw [globalUniformSuccessor_local,e.lift_openEmbedding_apply,e.left_inv hb]

theorem globalUniformSuccessor_surjective (A : ActualEndpointHistories X J) (k : ℕ) :
    Function.Surjective (globalUniformSuccessor A k) := by
  intro z
  obtain ⟨i,y,rfl⟩ := endpointLocalInclusion_jointly_surjective (uniformStageHistories A k) z
  let D := actualUniformSuccessor ((A.prefixTower i).append (A.tail i)) k
  let R := BlowupTower.step (.refl : BlowupTower (uniformStageHistories A k |>.finalSpace i)
      (uniformStageHistories A k |>.finalSpace i)) D.centre D.map D.blowup
  obtain ⟨w,hw⟩ := HironakaLocalPrincipalization.IsBlowupSequence.surjective R.isBlowupSequence y
  refine ⟨endpointLocalInclusion (uniformStageHistories A (k+1)) i w,?_⟩
  exact (globalUniformSuccessor_local A k i w).trans
    (congrArg (endpointLocalInclusion (uniformStageHistories A k) i) hw)

section OriginalInput
variable (hn : 0<n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : NormalCrossings.IsSNCDivisor n E)
  (hdense : W⊆closure (W \ ⋃ H∈E,H)) (hr : ∀ x∈W,RegularAtDim (n := n) W x 1)

theorem originalUniformSuccessor_contMDiff (k : ℕ) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (originalUniformSuccessor hn hW hE hdense hr k) :=
  globalUniformSuccessor_contMDiff (originalEndpointHistories hn hW hE hdense hr)
    (originalEndpointHistories_cover hn hW hE hdense hr) k

theorem originalUniformSuccessor_isProperMap (k : ℕ) :
    IsProperMap (originalUniformSuccessor hn hW hE hdense hr k) := by
  have hComp : (originalUniformStageProjection hn hW hE hdense hr k) ∘
      (originalUniformSuccessor hn hW hE hdense hr k)=
      (originalUniformStageProjection hn hW hE hdense hr (k+1)) :=
    funext (originalUniformSuccessor_projection hn hW hE hdense hr k)
  apply isProperMap_of_comp_of_t2 (originalUniformSuccessor hn hW hE hdense hr k).continuous
    (originalUniformStageProjection hn hW hE hdense hr k).continuous
  rw [hComp]
  exact originalUniformStageProjection_isProperMap hn hW hE hdense hr (k+1)

theorem originalUniformSuccessor_surjective (k : ℕ) :
    Function.Surjective (originalUniformSuccessor hn hW hE hdense hr k) :=
  globalUniformSuccessor_surjective (originalEndpointHistories hn hW hE hdense hr) k

end OriginalInput
end
end Hironaka.HironakaSharpActualCurveGlobalSuccessorGeometry
