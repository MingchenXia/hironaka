/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalTerminalAtlas
import Hironaka.Resolution.HironakaTerminalAtlasHolomorphic
/-! Original marked input constructs an actual global complex terminal manifold.
Complete four-node mathematics preceded proof code. Every local history,
overlap, separation, countability and holomorphic chart is supplied internally. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Topology Function IsManifold
open scoped Manifold ContDiff Topology
open CategoryTheory
universe u
namespace Hironaka.HironakaOriginalTerminalManifold
noncomputable section
open BlowupTowers MarkedIdeals HironakaOriginalTerminalAtlas
  HironakaTerminalAtlasTopology HironakaTerminalAtlasHolomorphic
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X : CMfd.{u} n}

/-- Literal embedding overlaps equal the actual original canonical domains. -/
theorem originalTerminalEmbeddingOverlap_eq (M : MarkedIdeal n X) (hM : IsInvDomain n M) (i j : X) :
    actualEmbeddingOverlap (originalTerminalLocalInclusion M hM i) (originalTerminalLocalInclusion M hM j)
      (originalTerminalLocalInclusion_openEmbedding M hM i) (originalTerminalLocalInclusion_openEmbedding M hM j)=
      originalTerminalOverlapOpen M hM i j := by
  apply Opens.ext
  ext y
  change originalTerminalLocalInclusion M hM i y ∈ range (originalTerminalLocalInclusion M hM j) ↔
    (((actualLocalTerminalAtlas M hM).tower i).proj y).val ∈ (actualLocalTerminalAtlas M hM).openSet j
  rw [originalTerminalLocalInclusion_range]
  change originalTerminalGluedProjection M hM (originalTerminalLocalInclusion M hM i y) ∈
      (actualLocalTerminalAtlas M hM).openSet j ↔ _
  rw [originalTerminalGluedProjection_local]
  rfl

def originalTerminalEmbeddingTransition (M : MarkedIdeal n X) (hM : IsInvDomain n M) (i j : X) :
    actualEmbeddingOverlap (originalTerminalLocalInclusion M hM i) (originalTerminalLocalInclusion M hM j)
      (originalTerminalLocalInclusion_openEmbedding M hM i) (originalTerminalLocalInclusion_openEmbedding M hM j)
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
    actualEmbeddingOverlap (originalTerminalLocalInclusion M hM j) (originalTerminalLocalInclusion M hM i)
      (originalTerminalLocalInclusion_openEmbedding M hM j) (originalTerminalLocalInclusion_openEmbedding M hM i) :=
  ((BlowupTowerIsoTail.opensCongr (originalTerminalEmbeddingOverlap_eq M hM i j)).trans
    (originalTerminalTransition M hM i j)).trans
      (BlowupTowerIsoTail.opensCongr (originalTerminalEmbeddingOverlap_eq M hM j i).symm)

theorem originalTerminalEmbeddingTransition_inclusion
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) (i j : X)
    (x : actualEmbeddingOverlap (originalTerminalLocalInclusion M hM i) (originalTerminalLocalInclusion M hM j)
      (originalTerminalLocalInclusion_openEmbedding M hM i) (originalTerminalLocalInclusion_openEmbedding M hM j)) :
    originalTerminalLocalInclusion M hM j (originalTerminalEmbeddingTransition M hM i j x).val=
      originalTerminalLocalInclusion M hM i x.val := by
  let q := BlowupTowerIsoTail.opensCongr (n := n) (originalTerminalEmbeddingOverlap_eq M hM i j) x
  have hc := (originalTerminalGlueData M hM).toGlueData.glue_condition i j
  exact congrArg (fun f : (originalTerminalGlueData M hM).V (i,j) ⟶
    (originalTerminalGlueData M hM).glued => f q) hc

theorem originalTerminalGluedSpace_t2 (M : MarkedIdeal n X) (hM : IsInvDomain n M) :
    T2Space (originalTerminalGluedSpace M hM) :=
  t2Space_of_actual_saturated_projection_atlas (originalTerminalGluedProjection M hM)
    (originalTerminalGluedProjection M hM).continuous (actualLocalTerminalAtlas M hM).openSet
    (fun x => ⟨x,(actualLocalTerminalAtlas M hM).point_mem x⟩)
    (originalTerminalLocalInclusion M hM) (originalTerminalLocalInclusion_openEmbedding M hM)
    (originalTerminalLocalInclusion_range M hM)

theorem originalTerminalGluedSpace_secondCountable (M : MarkedIdeal n X) (hM : IsInvDomain n M) :
    SecondCountableTopology (originalTerminalGluedSpace M hM) :=
  secondCountable_of_actual_saturated_projection_atlas (originalTerminalGluedProjection M hM)
    (actualLocalTerminalAtlas M hM).openSet (fun x => ⟨x,(actualLocalTerminalAtlas M hM).point_mem x⟩)
    (originalTerminalLocalInclusion M hM) (originalTerminalLocalInclusion_openEmbedding M hM)
    (originalTerminalLocalInclusion_range M hM)

@[instance_reducible]
def originalTerminalChartedSpace (M : MarkedIdeal n X) (hM : IsInvDomain n M) :
    ChartedSpace (ComplexModel n) (originalTerminalGluedSpace M hM) :=
  actualLiftedTerminalChartedSpace n (originalTerminalLocalInclusion M hM)
    (originalTerminalLocalInclusion_openEmbedding M hM) (originalTerminalLocalInclusion_jointly_surjective M hM)

attribute [local instance] originalTerminalChartedSpace

theorem originalTerminalGluedSpace_isComplexManifold (M : MarkedIdeal n X) (hM : IsInvDomain n M) :
    letI := originalTerminalChartedSpace M hM
    IsComplexManifold n (originalTerminalGluedSpace M hM) := by
  let := originalTerminalChartedSpace M hM
  have : T2Space (originalTerminalGluedSpace M hM) := originalTerminalGluedSpace_t2 M hM
  have : SecondCountableTopology (originalTerminalGluedSpace M hM) :=
    originalTerminalGluedSpace_secondCountable M hM
  have : IsManifold 𝓘(ℂ,ComplexModel n) ∞ (originalTerminalGluedSpace M hM) :=
    actualLiftedTerminalChartedSpace_isManifold (originalTerminalLocalInclusion M hM)
      (originalTerminalLocalInclusion_openEmbedding M hM) (originalTerminalLocalInclusion_jointly_surjective M hM)
      (originalTerminalEmbeddingTransition M hM) (originalTerminalEmbeddingTransition_inclusion M hM)
  exact {}

attribute [local instance] originalTerminalGluedSpace_isComplexManifold

def originalTerminalManifold (M : MarkedIdeal n X) (hM : IsInvDomain n M) : CMfd.{u} n :=
  letI := originalTerminalChartedSpace M hM
  letI := originalTerminalGluedSpace_isComplexManifold M hM
  CMfd.of (originalTerminalGluedSpace M hM)

theorem originalTerminalLocalInclusion_contMDiff (M : MarkedIdeal n X) (hM : IsInvDomain n M) (i : X) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (originalTerminalLocalInclusion M hM i : (actualLocalTerminalAtlas M hM).finalSpace i →
        originalTerminalManifold M hM) :=
  actualLiftedTerminal_local_inclusion_contMDiff (originalTerminalLocalInclusion M hM)
    (originalTerminalLocalInclusion_openEmbedding M hM) (originalTerminalLocalInclusion_jointly_surjective M hM)
    (originalTerminalEmbeddingTransition M hM) (originalTerminalEmbeddingTransition_inclusion M hM) i

theorem originalTerminalGluedProjection_contMDiff (M : MarkedIdeal n X) (hM : IsInvDomain n M) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (originalTerminalGluedProjection M hM : originalTerminalManifold M hM → X) := by
  intro z
  obtain ⟨i,x,rfl⟩ := originalTerminalLocalInclusion_jointly_surjective M hM z
  let e := chartAt (ComplexModel n) x
  let c := e.lift_openEmbedding (originalTerminalLocalInclusion_openEmbedding M hM i)
  have hc : c ∈ atlas (ComplexModel n) (originalTerminalManifold M hM) :=
    ⟨i,e,chart_mem_atlas (ComplexModel n) x,rfl⟩
  have hx : x ∈ e.source := mem_chart_source (ComplexModel n) x
  have hz : originalTerminalLocalInclusion M hM i x ∈ c.source := ⟨x,hx,rfl⟩
  have heMax : e ∈ maximalAtlas 𝓘(ℂ,ComplexModel n) ∞ ((actualLocalTerminalAtlas M hM).finalSpace i) :=
    chart_mem_maximalAtlas x
  have hcMax : c ∈ maximalAtlas 𝓘(ℂ,ComplexModel n) ∞ (originalTerminalManifold M hM) := subset_maximalAtlas hc
  have hlocal : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (originalTerminalLocalProjection M hM i) :=
    contMDiff_subtype_val.comp ((actualLocalTerminalAtlas M hM).tower i).contMDiff_proj
  have hcx : c (originalTerminalLocalInclusion M hM i x)=e x :=
    e.lift_openEmbedding_apply (originalTerminalLocalInclusion_openEmbedding M hM i)
  have hsinv : ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ e.symm
      (c (originalTerminalLocalInclusion M hM i x)) :=
    contMDiffAt_symm_of_mem_maximalAtlas heMax (by rw [hcx];exact e.map_source hx)
  have hh := (hlocal.contMDiffAt.comp _ hsinv).comp _ (contMDiffAt_of_mem_maximalAtlas hcMax hz)
  apply hh.congr_of_eventuallyEq
  filter_upwards [c.open_source.mem_nhds hz] with y hy
  obtain ⟨b,hb,rfl⟩ := hy
  change originalTerminalGluedProjection M hM (originalTerminalLocalInclusion M hM i b)=
    originalTerminalLocalProjection M hM i (e.symm (c (originalTerminalLocalInclusion M hM i b)))
  rw [originalTerminalGluedProjection_local,e.lift_openEmbedding_apply,e.left_inv hb]

end
end Hironaka.HironakaOriginalTerminalManifold
