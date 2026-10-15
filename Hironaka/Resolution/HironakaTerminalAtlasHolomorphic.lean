/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaTerminalAtlasTopology
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Diffeomorph
/-! Genuine holomorphic compatibility of actual lifted terminal charts.
Complete three-node mathematics preceded proof code. Actual biholomorphic
local overlap geometry internally gives all global coordinate regularity. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Topology Function IsManifold
open scoped Manifold ContDiff Topology
universe u v w
namespace Hironaka.HironakaTerminalAtlasHolomorphic
noncomputable section
open HironakaTerminalAtlasTopology
variable {n : ℕ} {A B : Type v} {G : Type w}
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace G]
  [ChartedSpace (ComplexModel n) A] [ChartedSpace (ComplexModel n) B]
  [IsManifold 𝓘(ℂ,ComplexModel n) ∞ A] [IsManifold 𝓘(ℂ,ComplexModel n) ∞ B]

def actualEmbeddingOverlap {F : Type v} [TopologicalSpace F] {K : Type v} [TopologicalSpace K]
    (ι : F → G) (κ : K → G) (hι : IsOpenEmbedding ι) (hκ : IsOpenEmbedding κ) : Opens F :=
  ⟨ι ⁻¹' range κ,hκ.isOpen_range.preimage hι.continuous⟩

theorem lifted_chart_transition_contDiff
    (ι : A → G) (κ : B → G) (hι : IsOpenEmbedding ι) (hκ : IsOpenEmbedding κ)
    (δ : actualEmbeddingOverlap ι κ hι hκ
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ actualEmbeddingOverlap κ ι hκ hι)
    (hδ : ∀ x, κ (δ x).val=ι x.val)
    (e : OpenPartialHomeomorph A (ComplexModel n)) (e' : OpenPartialHomeomorph B (ComplexModel n))
    (he : e ∈ atlas (ComplexModel n) A) (he' : e' ∈ atlas (ComplexModel n) B) :
    ContDiffOn ℂ ∞ ((e.lift_openEmbedding hι).symm.trans (e'.lift_openEmbedding hκ))
      ((e.lift_openEmbedding hι).symm.trans (e'.lift_openEmbedding hκ)).source := by
  intro z hz
  have hz₁ : z ∈ e.target := hz.1
  have hz₂ : ι (e.symm z) ∈ κ '' e'.source := hz.2
  obtain ⟨y,hy,hyι⟩ := hz₂
  let U := actualEmbeddingOverlap ι κ hι hκ
  have hxU : e.symm z ∈ U := ⟨y,hyι⟩
  have hs : Nonempty U := ⟨⟨e.symm z,hxU⟩⟩
  have hmem : ∀ t, t ∈ ((e.lift_openEmbedding hι).symm.trans (e'.lift_openEmbedding hκ)).source →
      t ∈ (e.subtypeRestr hs).target := by
    intro t ht
    have ht₁ : t ∈ e.target := ht.1
    have ht₂ : ι (e.symm t) ∈ κ '' e'.source := ht.2
    obtain ⟨b,hb,hbι⟩ := ht₂
    have hx : e.symm t ∈ U := ⟨b,hbι⟩
    have hm := e.map_subtype_source hs (x := ⟨e.symm t,hx⟩) (e.map_target ht₁)
    rw [e.right_inv ht₁] at hm
    exact hm
  have hzsub := hmem z hz
  have heSub : e.subtypeRestr hs ∈ maximalAtlas 𝓘(ℂ,ComplexModel n) ∞ U :=
    StructureGroupoid.subtypeRestr_mem_maximalAtlas (G := contDiffGroupoid ∞ 𝓘(ℂ,ComplexModel n)) he hs
  have hsymm := contMDiffAt_symm_of_mem_maximalAtlas heSub hzsub
  have hxi : ((e.subtypeRestr hs).symm z).val=e.symm z := e.subtypeRestr_symm_apply hs hzsub
  have hpoint : (δ ((e.subtypeRestr hs).symm z)).val=y :=
    hκ.injective ((hδ _).trans ((congrArg ι hxi).trans hyι.symm))
  have hmap : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (fun q : U => (δ q).val) := contMDiff_subtype_val.comp δ.contMDiff
  have hbhol : ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ e'
      ((δ ((e.subtypeRestr hs).symm z)).val) :=
    contMDiffAt_of_mem_maximalAtlas (subset_maximalAtlas he') (by rw [hpoint];exact hy)
  have hc := hbhol.comp z ((hmap.contMDiffAt).comp z hsymm)
  apply hc.contDiffAt.contDiffWithinAt.congr_of_mem _ hz
  intro t ht
  change (e'.lift_openEmbedding hκ) (ι (e.symm t))=e' (δ ((e.subtypeRestr hs).symm t)).val
  have hxt : ((e.subtypeRestr hs).symm t).val=e.symm t := e.subtypeRestr_symm_apply hs (hmem t ht)
  rw [← hxt,← hδ ((e.subtypeRestr hs).symm t),OpenPartialHomeomorph.lift_openEmbedding_apply]

variable {J : Type u} {F : J → Type v} [∀ i, TopologicalSpace (F i)]
  [∀ i, ChartedSpace (ComplexModel n) (F i)] [∀ i, IsManifold 𝓘(ℂ,ComplexModel n) ∞ (F i)]

theorem actualLiftedTerminalChartedSpace_isManifold
    (ι : ∀ i, F i → G) (hι : ∀ i, IsOpenEmbedding (ι i)) (hcover : ∀ z : G, ∃ i y, ι i y=z)
    (δ : ∀ i j, actualEmbeddingOverlap (ι i) (ι j) (hι i) (hι j)
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ actualEmbeddingOverlap (ι j) (ι i) (hι j) (hι i))
    (hδ : ∀ i j x, ι j (δ i j x).val=ι i x.val) :
    letI := actualLiftedTerminalChartedSpace n ι hι hcover
    IsManifold 𝓘(ℂ,ComplexModel n) ∞ G := by
  let := actualLiftedTerminalChartedSpace n ι hι hcover
  apply isManifold_of_contDiffOn
  intro a b ha hb
  obtain ⟨i,e,he,rfl⟩ := ha
  obtain ⟨j,e',he',rfl⟩ := hb
  simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,id_comp,Function.comp_id,
    preimage_id,range_id,inter_univ] using
    lifted_chart_transition_contDiff (ι i) (ι j) (hι i) (hι j) (δ i j) (hδ i j) e e' he he'

theorem actualLiftedTerminal_local_inclusion_contMDiff
    (ι : ∀ i, F i → G) (hι : ∀ i, IsOpenEmbedding (ι i)) (hcover : ∀ z : G, ∃ i y, ι i y=z)
    (δ : ∀ i j, actualEmbeddingOverlap (ι i) (ι j) (hι i) (hι j)
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ actualEmbeddingOverlap (ι j) (ι i) (hι j) (hι i))
    (hδ : ∀ i j x, ι j (δ i j x).val=ι i x.val) (i : J) :
    letI := actualLiftedTerminalChartedSpace n ι hι hcover
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (ι i) := by
  let := actualLiftedTerminalChartedSpace n ι hι hcover
  have : IsManifold 𝓘(ℂ,ComplexModel n) ∞ G :=
    actualLiftedTerminalChartedSpace_isManifold ι hι hcover δ hδ
  change ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (ι i)
  intro x
  let e := chartAt (ComplexModel n) x
  have he : e.lift_openEmbedding (hι i) ∈ atlas (ComplexModel n) G :=
    ⟨i,e,chart_mem_atlas (ComplexModel n) x,rfl⟩
  have hx := mem_chart_source (ComplexModel n) x
  have hz : e x ∈ (e.lift_openEmbedding (hι i)).target := e.map_source hx
  have hgMax : e.lift_openEmbedding (hι i) ∈ maximalAtlas 𝓘(ℂ,ComplexModel n) ∞ G :=
    subset_maximalAtlas he
  have heMax : e ∈ maximalAtlas 𝓘(ℂ,ComplexModel n) ∞ (F i) := chart_mem_maximalAtlas x
  have hh := (contMDiffAt_symm_of_mem_maximalAtlas hgMax hz).comp x
    (contMDiffAt_of_mem_maximalAtlas heMax hx)
  apply hh.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hx] with y hy
  change ι i y=ι i (e.symm (e y))
  rw [e.left_inv hy]

end
end Hironaka.HironakaTerminalAtlasHolomorphic
