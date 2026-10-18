/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveGlobalManifold

/-! Genuine actual local inverse holomorphicity and both finite-history
projection dictionaries precede global strict-carrier and divisor descent. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Topology Function IsManifold
open scoped Manifold ContDiff Topology
universe u
namespace Hironaka.HironakaSharpActualCurveLocalRangeBiholomorphism
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupTowerTransforms BlowupTowerIsomorphism BlowupTowerSplitIso BlowupTowerIsoTail
  HironakaSharpActualCurveTopologicalGluing HironakaSharpActualCurveGluedProjection
  HironakaSharpActualCurveEndpointGeometry HironakaSharpActualCurveOriginalRecipeAtlas
  HironakaSharpActualCurveGlobalManifold HironakaTerminalAtlasTopology HironakaTerminalAtlasHolomorphic
  NormalCrossings
attribute [local instance] endpointChartedSpace
variable {n : ℕ} {X : CMfd.{u} n} {J : Type u}

def localRangeOpen (A : ActualEndpointHistories X J) (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (i : J) :
    Opens (endpointManifold A hc) :=
  ⟨range (endpointLocalInclusion A i),(endpointLocalInclusion_openEmbedding A i).isOpen_range⟩

def localHomeomorphism (A : ActualEndpointHistories X J) (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (i : J) :
    A.finalSpace i ≃ₜ localRangeOpen A hc i := (endpointLocalInclusion_openEmbedding A i).isEmbedding.toHomeomorph

theorem localHomeomorphism_point (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (i : J) (z : A.finalSpace i) :
    (localHomeomorphism A hc i z).val=endpointLocalInclusion A i z := rfl

theorem localHomeomorphism_inverse_point (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (i : J) (z : localRangeOpen A hc i) :
    endpointLocalInclusion A i ((localHomeomorphism A hc i).symm z)=z.val :=
  congrArg Subtype.val ((localHomeomorphism A hc i).apply_symm_apply z)

theorem localHomeomorphism_contMDiff (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (i : J) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (localHomeomorphism A hc i) :=
  BlowupRestrictOpen.contMDiff_opens_mk (V := localRangeOpen A hc i)
    (localInclusion_contMDiff A hc i) (fun z => ⟨z,rfl⟩)

/-- The actual inverse is holomorphic by the genuine lifted chart formulas,
not by an assumed inverse-regularity or arbitrary open-map certificate. -/
theorem localHomeomorphism_symm_contMDiff (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (i : J) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (localHomeomorphism A hc i).symm := by
  intro q
  let H := localHomeomorphism A hc i
  let x := H.symm q
  let e := chartAt (ComplexModel n) x
  let c := e.lift_openEmbedding (endpointLocalInclusion_openEmbedding A i)
  have hp : endpointLocalInclusion A i x=q.val := localHomeomorphism_inverse_point A hc i q
  have hcmem : c∈atlas (ComplexModel n) (endpointManifold A hc) :=
    ⟨i,e,chart_mem_atlas (ComplexModel n) x,rfl⟩
  have hx : x∈e.source := mem_chart_source (ComplexModel n) x
  have hz : q.val∈c.source := ⟨x,hx,hp⟩
  have hcx : c q.val=e x := by rw [←hp];exact e.lift_openEmbedding_apply _
  have heMax : e∈maximalAtlas 𝓘(ℂ,ComplexModel n) ∞ (A.finalSpace i) := chart_mem_maximalAtlas x
  have hcMax : c∈maximalAtlas 𝓘(ℂ,ComplexModel n) ∞ (endpointManifold A hc) := subset_maximalAtlas hcmem
  have hinv : ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ e.symm (c q.val) :=
    contMDiffAt_symm_of_mem_maximalAtlas heMax (by rw [hcx];exact e.map_source hx)
  have hval : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (Subtype.val : localRangeOpen A hc i → endpointManifold A hc) := contMDiff_subtype_val
  have hh := hinv.comp q ((contMDiffAt_of_mem_maximalAtlas hcMax hz).comp q hval.contMDiffAt)
  apply hh.congr_of_eventuallyEq
  filter_upwards [(c.open_source.preimage continuous_subtype_val).mem_nhds hz] with t ht
  obtain ⟨b,hb,hbι⟩ := ht
  have hpoint : H.symm t=b := (endpointLocalInclusion_openEmbedding A i).injective
    ((localHomeomorphism_inverse_point A hc i t).trans hbι.symm)
  change H.symm t=e.symm (c t.val)
  rw [hpoint]
  change b=e.symm ((e.lift_openEmbedding (endpointLocalInclusion_openEmbedding A i)) t.val)
  rw [←hbι,e.lift_openEmbedding_apply,e.left_inv hb]

def localBiholomorphism (A : ActualEndpointHistories X J) (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (i : J) :
    A.finalSpace i ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (localRangeOpen A hc i) where
  toEquiv := (localHomeomorphism A hc i).toEquiv
  contMDiff_toFun := localHomeomorphism_contMDiff A hc i
  contMDiff_invFun := localHomeomorphism_symm_contMDiff A hc i

theorem localBiholomorphism_point (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (i : J) (z : A.finalSpace i) :
    (localBiholomorphism A hc i z).val=endpointLocalInclusion A i z := rfl

def localRangeProjection (A : ActualEndpointHistories X J) (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (i : J) :
    localRangeOpen A hc i → A.openSet i := fun q =>
  ⟨gluedProjection A q.val,by
    change q.val∈(gluedProjection A) ⁻¹' (A.openSet i : Set X)
    rw [←localInclusion_range]
    exact q.property⟩

/-- The real restricted global projection is EXACTLY the SAME old finite
prefix/tail projection, on the whole actual range. -/
theorem localRangeProjection_biholomorphism (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (i : J) (z : A.finalSpace i) :
    localRangeProjection A hc i (localBiholomorphism A hc i z)=
      ((A.prefixTower i).append (A.tail i)).proj z := by
  apply Subtype.ext
  exact gluedProjection_local_full A i z

theorem localRangeProjection_inverse (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (i : J) (q : localRangeOpen A hc i) :
    localRangeProjection A hc i q=
      ((A.prefixTower i).append (A.tail i)).proj ((localBiholomorphism A hc i).symm q) := by
  have h := localRangeProjection_biholomorphism A hc i ((localBiholomorphism A hc i).symm q)
  rw [Diffeomorph.apply_symm_apply] at h
  exact h

theorem localRangeProjection_contMDiff (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (i : J) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (localRangeProjection A hc i) := by
  have h : localRangeProjection A hc i=
      ((A.prefixTower i).append (A.tail i)).proj ∘ (localBiholomorphism A hc i).symm :=
    funext (localRangeProjection_inverse A hc i)
  rw [h]
  exact ((A.prefixTower i).append (A.tail i)).contMDiff_proj.comp (localBiholomorphism A hc i).symm.contMDiff

section OriginalInput
variable (hn : 0<n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
  (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)

/-- ONLY original inputs internally provide the real atlas, cover, complex
manifold and both actual local holomorphic directions. -/
def originalLocalBiholomorphism (x : X) :
    (originalEndpointHistories hn hW hE hdense hr).finalSpace x
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (localRangeOpen (originalEndpointHistories hn hW hE hdense hr)
          (originalEndpointHistories_cover hn hW hE hdense hr) x) :=
  localBiholomorphism (originalEndpointHistories hn hW hE hdense hr)
    (originalEndpointHistories_cover hn hW hE hdense hr) x

theorem originalLocalBiholomorphism_projection (x : X)
    (z : (originalEndpointHistories hn hW hE hdense hr).finalSpace x) :
    localRangeProjection (originalEndpointHistories hn hW hE hdense hr)
      (originalEndpointHistories_cover hn hW hE hdense hr) x (originalLocalBiholomorphism hn hW hE hdense hr x z)=
      (((originalEndpointHistories hn hW hE hdense hr).prefixTower x).append
        ((originalEndpointHistories hn hW hE hdense hr).tail x)).proj z :=
  localRangeProjection_biholomorphism (originalEndpointHistories hn hW hE hdense hr)
    (originalEndpointHistories_cover hn hW hE hdense hr) x z

end OriginalInput

end
end Hironaka.HironakaSharpActualCurveLocalRangeBiholomorphism
