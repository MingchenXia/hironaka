/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalTerminalManifold
/-! Genuine original local biholomorphisms onto actual saturated ranges.
Complete three-node mathematics preceded code. True lifted charts prove
inverse regularity before actual local geometric transport is consumed. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Topology Function IsManifold
open scoped Manifold ContDiff Topology
universe u
namespace Hironaka.HironakaOriginalTerminalLocalBiholomorphism
noncomputable section
open BlowupTowers MarkedIdeals HironakaOriginalTerminalAtlas HironakaOriginalTerminalManifold
open ResolutionInvariantSpec (IsInvDomain)
attribute [local instance] originalTerminalChartedSpace originalTerminalGluedSpace_isComplexManifold
variable {n : ℕ} {X : CMfd.{u} n}

def originalTerminalLocalRangeOpen (M : MarkedIdeal n X) (hM : IsInvDomain n M) (i : X) :
    Opens (originalTerminalManifold M hM) :=
  ⟨range (originalTerminalLocalInclusion M hM i),(originalTerminalLocalInclusion_openEmbedding M hM i).isOpen_range⟩

def originalTerminalLocalHomeomorphism (M : MarkedIdeal n X) (hM : IsInvDomain n M) (i : X) :
    (actualLocalTerminalAtlas M hM).finalSpace i ≃ₜ originalTerminalLocalRangeOpen M hM i :=
  (originalTerminalLocalInclusion_openEmbedding M hM i).isEmbedding.toHomeomorph

theorem originalTerminalLocalHomeomorphism_point (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (i : X) (x : (actualLocalTerminalAtlas M hM).finalSpace i) :
    (originalTerminalLocalHomeomorphism M hM i x).val=originalTerminalLocalInclusion M hM i x := rfl

theorem originalTerminalLocalHomeomorphism_inverse_point (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (i : X) (q : originalTerminalLocalRangeOpen M hM i) :
    originalTerminalLocalInclusion M hM i ((originalTerminalLocalHomeomorphism M hM i).symm q)=q.val :=
  congrArg Subtype.val ((originalTerminalLocalHomeomorphism M hM i).apply_symm_apply q)

theorem originalTerminalLocalHomeomorphism_contMDiff (M : MarkedIdeal n X) (hM : IsInvDomain n M) (i : X) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (originalTerminalLocalHomeomorphism M hM i) :=
  BlowupRestrictOpen.contMDiff_opens_mk (V := originalTerminalLocalRangeOpen M hM i)
    (originalTerminalLocalInclusion_contMDiff M hM i) (fun x => ⟨x,rfl⟩)

theorem originalTerminalLocalHomeomorphism_symm_contMDiff
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) (i : X) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (originalTerminalLocalHomeomorphism M hM i).symm := by
  intro q
  let H := originalTerminalLocalHomeomorphism M hM i
  let x := H.symm q
  let e := chartAt (ComplexModel n) x
  let c := e.lift_openEmbedding (originalTerminalLocalInclusion_openEmbedding M hM i)
  have hp : originalTerminalLocalInclusion M hM i x=q.val :=
    originalTerminalLocalHomeomorphism_inverse_point M hM i q
  have hc : c ∈ atlas (ComplexModel n) (originalTerminalManifold M hM) :=
    ⟨i,e,chart_mem_atlas (ComplexModel n) x,rfl⟩
  have hx : x ∈ e.source := mem_chart_source (ComplexModel n) x
  have hz : q.val ∈ c.source := ⟨x,hx,hp⟩
  have hcx : c q.val=e x := by rw [← hp];exact e.lift_openEmbedding_apply _
  have heMax : e ∈ maximalAtlas 𝓘(ℂ,ComplexModel n) ∞ ((actualLocalTerminalAtlas M hM).finalSpace i) :=
    chart_mem_maximalAtlas x
  have hcMax : c ∈ maximalAtlas 𝓘(ℂ,ComplexModel n) ∞ (originalTerminalManifold M hM) := subset_maximalAtlas hc
  have hinv : ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ e.symm (c q.val) :=
    contMDiffAt_symm_of_mem_maximalAtlas heMax (by rw [hcx];exact e.map_source hx)
  have hval : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (Subtype.val : originalTerminalLocalRangeOpen M hM i → originalTerminalManifold M hM) := contMDiff_subtype_val
  have hh := hinv.comp q ((contMDiffAt_of_mem_maximalAtlas hcMax hz).comp q hval.contMDiffAt)
  apply hh.congr_of_eventuallyEq
  filter_upwards [(c.open_source.preimage continuous_subtype_val).mem_nhds hz] with t ht
  obtain ⟨b,hb,hbΓ⟩ := ht
  have hpoint : H.symm t=b :=
    (originalTerminalLocalInclusion_openEmbedding M hM i).injective
      ((originalTerminalLocalHomeomorphism_inverse_point M hM i t).trans hbΓ.symm)
  change H.symm t=e.symm (c t.val)
  rw [hpoint]
  change b=e.symm ((e.lift_openEmbedding (originalTerminalLocalInclusion_openEmbedding M hM i)) t.val)
  rw [← hbΓ,e.lift_openEmbedding_apply,e.left_inv hb]

def originalTerminalLocalBiholomorphism (M : MarkedIdeal n X) (hM : IsInvDomain n M) (i : X) :
    (actualLocalTerminalAtlas M hM).finalSpace i
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (originalTerminalLocalRangeOpen M hM i) where
  toEquiv := (originalTerminalLocalHomeomorphism M hM i).toEquiv
  contMDiff_toFun := originalTerminalLocalHomeomorphism_contMDiff M hM i
  contMDiff_invFun := originalTerminalLocalHomeomorphism_symm_contMDiff M hM i

theorem originalTerminalLocalBiholomorphism_point (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (i : X) (x : (actualLocalTerminalAtlas M hM).finalSpace i) :
    (originalTerminalLocalBiholomorphism M hM i x).val=originalTerminalLocalInclusion M hM i x := rfl

def originalTerminalLocalRangeProjection (M : MarkedIdeal n X) (hM : IsInvDomain n M) (i : X) :
    originalTerminalLocalRangeOpen M hM i → (actualLocalTerminalAtlas M hM).openSet i := fun q =>
  ⟨originalTerminalGluedProjection M hM q.val,by
    change q.val ∈ (originalTerminalGluedProjection M hM) ⁻¹' ((actualLocalTerminalAtlas M hM).openSet i : Set X)
    rw [← originalTerminalLocalInclusion_range]
    exact q.property⟩

theorem originalTerminalLocalRangeProjection_biholomorphism
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) (i : X)
    (x : (actualLocalTerminalAtlas M hM).finalSpace i) :
    originalTerminalLocalRangeProjection M hM i (originalTerminalLocalBiholomorphism M hM i x)=
      ((actualLocalTerminalAtlas M hM).tower i).proj x := by
  apply Subtype.ext
  exact originalTerminalGluedProjection_local M hM i x

theorem originalTerminalLocalRangeProjection_inverse
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) (i : X) (q : originalTerminalLocalRangeOpen M hM i) :
    originalTerminalLocalRangeProjection M hM i q=
      ((actualLocalTerminalAtlas M hM).tower i).proj ((originalTerminalLocalBiholomorphism M hM i).symm q) := by
  have h := originalTerminalLocalRangeProjection_biholomorphism M hM i
    ((originalTerminalLocalBiholomorphism M hM i).symm q)
  rw [Diffeomorph.apply_symm_apply] at h
  exact h

theorem originalTerminalLocalRangeProjection_contMDiff (M : MarkedIdeal n X) (hM : IsInvDomain n M) (i : X) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (originalTerminalLocalRangeProjection M hM i) := by
  have he : originalTerminalLocalRangeProjection M hM i=
      ((actualLocalTerminalAtlas M hM).tower i).proj ∘ (originalTerminalLocalBiholomorphism M hM i).symm :=
    funext (originalTerminalLocalRangeProjection_inverse M hM i)
  rw [he]
  exact ((actualLocalTerminalAtlas M hM).tower i).contMDiff_proj.comp
    (originalTerminalLocalBiholomorphism M hM i).symm.contMDiff

end
end Hironaka.HironakaOriginalTerminalLocalBiholomorphism
