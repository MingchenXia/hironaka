/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualProductHSProfileReflection
import Hironaka.Resolution.HironakaActualOpenIntrinsicHS

/-! The EXISTING intrinsic HS of the genuine original coordinate projection. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualProjectionIntrinsicHS
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicPointJets HironakaHolomorphicJetRankLoci
  HironakaActualWholeStalkHolomorphicPullback HironakaActualBiholomorphicWholeStalkHS
  HironakaSmoothCentreRealDomainActualAmbientHS HironakaRelativeNormalIdeal
  HironakaRelativeNormalMonomialBasis HironakaActualProductMixedHS
  HironakaActualProductHSProfileReflection

section ActualInverseMaps
variable {n m : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]

/-- Actual inverse original maps give whole germ algebra equivalence without identifying model dimension labels. -/
def actualBiholomorphicGermAlgEquiv_models
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel n)⟯ X) (y : Y) :
    HolGerm (ComplexModel n) ≃ₐ[ℂ] HolGerm (ComplexModel m) := by
  apply AlgEquiv.ofAlgHom (actualHolomorphicGermPullback e.contMDiff y)
    (actualHolomorphicGermPullback e.symm.contMDiff (e y))
  · have h := actualHolomorphicGermPullback_comp e.symm.contMDiff e.contMDiff y
    simpa only [Function.comp_def,e.symm_apply_apply,actualHolomorphicGermPullback_id] using h.symm
  · have h := actualHolomorphicGermPullback_comp e.contMDiff e.symm.contMDiff (e y)
    simpa only [Function.comp_def,e.apply_symm_apply,e.symm_apply_apply,actualHolomorphicGermPullback_id] using h.symm

/-- EVERY original whole germ retains its independently defined actual pullback. -/
theorem actualBiholomorphicGermAlgEquiv_models_apply
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel n)⟯ X) (y : Y)
    (g : HolGerm (ComplexModel n)) :
    actualBiholomorphicGermAlgEquiv_models e y g = actualHolomorphicGermPullback e.contMDiff y g := rfl

/-- Genuine original biholomorphic geometry preserves EXISTING intrinsic HS for any original model labels. -/
theorem hilbertSamuelAt_actual_biholomorphic_models
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel m),𝓘(ℂ,ComplexModel n)⟯ X)
    (A : GermIdeal n X) (hA : A.IsCoherent) (y : Y) (ℓ : ℕ) :
    hilbertSamuelAt (GermIdeal.pullback (m := m) e A) y ℓ = hilbertSamuelAt A (e y) ℓ := by
  unfold hilbertSamuelAt
  rw [← map_wholeChartStalkIdeal_actual_pullback e.contMDiff A hA y]
  exact (actualLocalAmbientJetAlgEquiv (actualBiholomorphicGermAlgEquiv_models e y) _ (ℓ+1)).toLinearEquiv.finrank_eq.symm
end ActualInverseMaps

/-- The ACTUAL original projection has the SAME genuine centred germ map at EVERY original source point. -/
theorem actualHolomorphicGermPullback_tangentProjection (d t : ℕ) (p : ComplexModel (d+t)) :
    actualHolomorphicGermPullback (f := (tangentProjection d t))
      (tangentProjection d t).contDiff.contMDiff p = tangentPullback d t := by
  apply AlgHom.ext
  intro g
  induction g using HolGerm.induction_on with
  | h F hF =>
    unfold actualHolomorphicGermPullback tangentPullback
    rw [compAlgHom_mk,compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    apply Eventually.of_forall
    intro z
    apply congrArg F
    change tangentProjection d t (z+p)-tangentProjection d t p=tangentProjection d t z
    rw [map_add,add_sub_cancel_right]

/-- ONLY original coherence gives BOTH whole original projection-stalk ideal directions. -/
theorem wholeChartStalkIdeal_actual_projection (d t : ℕ)
    (A : GermIdeal d (ComplexModel d)) (hA : A.IsCoherent) (p : ComplexModel (d+t)) :
    wholeChartStalkIdeal (GermIdeal.pullback (m := d+t) (tangentProjection d t) A) p p (mem_chart_source _ p) =
      Ideal.map (tangentPullback d t).toRingHom
        (wholeChartStalkIdeal A (tangentProjection d t p) (tangentProjection d t p) (mem_chart_source _ _)) := by
  rw [← map_wholeChartStalkIdeal_actual_pullback (tangentProjection d t).contDiff.contMDiff A hA p,
    actualHolomorphicGermPullback_tangentProjection]

/-- EVERY intrinsic original HS order under the true projection is the genuine original convolution. -/
theorem hilbertSamuelAt_actual_projection_convolution (d t : ℕ)
    (A : GermIdeal d (ComplexModel d)) (hA : A.IsCoherent) (p : ComplexModel (d+t)) (ℓ : ℕ) :
    let := normalExponentFintype t (ℓ+1)
    hilbertSamuelAt (GermIdeal.pullback (m := d+t) (tangentProjection d t) A) p ℓ =
      ∑ α : normalExponentIndex t (ℓ+1), hilbertSamuelAt A (tangentProjection d t p) (ℓ-normalExponentDegree α.val) := by
  unfold hilbertSamuelAt
  rw [wholeChartStalkIdeal_actual_projection d t A hA p]
  exact actualProductHilbertSamuel_convolution d t _ ℓ

/-- BOTH ENTIRE actual intrinsic HS profile directions retain the two true ORIGINAL image profiles. -/
theorem hilbertSamuelAt_actual_projection_entire_profile_eq_iff (d t : ℕ)
    (A : GermIdeal d (ComplexModel d)) (hA : A.IsCoherent) (p q : ComplexModel (d+t)) :
    (∀ ℓ, hilbertSamuelAt (GermIdeal.pullback (m := d+t) (tangentProjection d t) A) p ℓ =
      hilbertSamuelAt (GermIdeal.pullback (m := d+t) (tangentProjection d t) A) q ℓ) ↔
        ∀ ℓ, hilbertSamuelAt A (tangentProjection d t p) ℓ = hilbertSamuelAt A (tangentProjection d t q) ℓ := by
  unfold hilbertSamuelAt
  rw [wholeChartStalkIdeal_actual_projection d t A hA p,wholeChartStalkIdeal_actual_projection d t A hA q]
  exact actualProductHS_entire_profile_eq_iff d t _ _
end
end Hironaka.HironakaActualProjectionIntrinsicHS
