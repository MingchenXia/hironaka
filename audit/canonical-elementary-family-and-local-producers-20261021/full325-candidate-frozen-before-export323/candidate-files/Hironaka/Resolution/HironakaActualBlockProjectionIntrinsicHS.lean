/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualProjectionIntrinsicHS
import Hironaka.Resolution.HironakaSmoothSubmersionMonomialChartPullback

/-! The actual original second-block projection retains whole ideals and every intrinsic HS order on real opens. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualBlockProjectionIntrinsicHS
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicPointJets HironakaHolomorphicJetRankLoci
  HironakaActualWholeStalkHolomorphicPullback HironakaActualBiholomorphicWholeStalkHS
  HironakaSmoothCentreRealDomainActualAmbientHS HironakaRelativeNormalIdeal
  HironakaRelativeNormalMonomialBasis HironakaActualProductMixedHS
  HironakaActualProductHSProfileReflection HironakaActualProjectionIntrinsicHS HironakaActualOpenIntrinsicHS
  HironakaSmoothSubmersionMonomialChartPullback

/-- The actual original coordinate-block interchange, with its genuine continuous complex-linear inverse. -/
def actualBlockSwapCoordinates (r n : ℕ) : ComplexModel (r+n) ≃L[ℂ] ComplexModel (n+r) :=
  (splitCoordinates r n).trans
    ((ContinuousLinearEquiv.prodComm ℂ (ComplexModel r) (ComplexModel n)).trans (splitCoordinates n r).symm)

/-- Genuine original block interchange is an actual holomorphic equivalence between the original model manifolds. -/
def actualBlockSwapDiffeomorph (r n : ℕ) :
    ComplexModel (r+n) ≃ₘ⟮𝓘(ℂ,ComplexModel (r+n)),𝓘(ℂ,ComplexModel (n+r))⟯ ComplexModel (n+r) where
  toEquiv := (actualBlockSwapCoordinates r n).toEquiv
  contMDiff_toFun := (actualBlockSwapCoordinates r n).contDiff.contMDiff
  contMDiff_invFun := (actualBlockSwapCoordinates r n).symm.contDiff.contMDiff

/-- The whole actual first block after interchange is precisely the SAME original second block. -/
theorem actualBlockSwap_firstProjection (r n : ℕ) (p : ComplexModel (r+n)) :
    tangentProjection n r (actualBlockSwapDiffeomorph r n p) = blockProjection r n p := by
  change tangentProjection n r
    (joinCoordinates n r (blockProjection r n p) (fibreProjection r n p)) = _
  ext i
  rw [tangentProjection_apply]
  have h := congrArg (fun z : ComplexModel n => z i)
    (fibreProjection_join n r (blockProjection r n p) (fibreProjection r n p))
  simpa only [fibreProjection_apply] using h

/-- EVERY genuine original block-projection germ factors through the ACTUAL independent block swap. -/
theorem actualGermPullback_blockProjection (r n : ℕ) (p : ComplexModel (r+n)) :
    actualHolomorphicGermPullback (contMDiff_blockProjection r n) p =
      (actualHolomorphicGermPullback (actualBlockSwapDiffeomorph r n).contMDiff p).comp (tangentPullback n r) := by
  have hf : (tangentProjection n r) ∘ actualBlockSwapDiffeomorph r n = blockProjection r n :=
    funext (actualBlockSwap_firstProjection r n)
  have h := actualHolomorphicGermPullback_comp (tangentProjection n r).contDiff.contMDiff
    (actualBlockSwapDiffeomorph r n).contMDiff p
  simpa only [hf,actualHolomorphicGermPullback_tangentProjection] using h

/-- Original coherence gives BOTH whole ideal directions before genuine block-projection HS. -/
theorem wholeChartStalkIdeal_actual_block_projection (r n : ℕ)
    (A : GermIdeal n (ComplexModel n)) (hA : A.IsCoherent) (p : ComplexModel (r+n)) :
    wholeChartStalkIdeal (GermIdeal.pullback (m := r+n) (blockProjection r n) A) p p (mem_chart_source _ p) =
      Ideal.map (actualBiholomorphicGermAlgEquiv_models (actualBlockSwapDiffeomorph r n) p).toRingEquiv.toRingHom
        (Ideal.map (tangentPullback n r).toRingHom
          (wholeChartStalkIdeal A (blockProjection r n p) (blockProjection r n p) (mem_chart_source _ _))) := by
  rw [← map_wholeChartStalkIdeal_actual_pullback (contMDiff_blockProjection r n) A hA p,
    actualGermPullback_blockProjection,Ideal.map_map]
  rfl

/-- The EXISTING block-projection intrinsic HS is the SAME genuine original smooth-product HS at EVERY order. -/
theorem hilbertSamuelAt_actual_block_projection_eq_product (r n : ℕ)
    (A : GermIdeal n (ComplexModel n)) (hA : A.IsCoherent) (p : ComplexModel (r+n)) (ℓ : ℕ) :
    hilbertSamuelAt (GermIdeal.pullback (m := r+n) (blockProjection r n) A) p ℓ =
      hilbertSamuelValue (Ideal.map (tangentPullback n r).toRingHom
        (wholeChartStalkIdeal A (blockProjection r n p) (blockProjection r n p) (mem_chart_source _ _))) ℓ := by
  unfold hilbertSamuelAt
  rw [wholeChartStalkIdeal_actual_block_projection r n A hA p]
  exact (actualLocalAmbientJetAlgEquiv
    (actualBiholomorphicGermAlgEquiv_models (actualBlockSwapDiffeomorph r n) p) _ (ℓ+1)).toLinearEquiv.finrank_eq.symm

/-- The REAL open inclusion and genuine original functorial germ maps retain the WHOLE original block pullback. -/
theorem wholeChartStalkIdeal_actual_open_block_projection (r n : ℕ)
    (A : GermIdeal n (ComplexModel n)) (hA : A.IsCoherent)
    (U : Opens (ComplexModel (r+n))) (p : U) :
    wholeChartStalkIdeal (GermIdeal.pullback (m := r+n) (fun q : U => blockProjection r n q) A)
      p p (mem_chart_source _ p) =
      wholeChartStalkIdeal (GermIdeal.pullback (m := r+n) (blockProjection r n) A)
        (p : ComplexModel (r+n)) (p : ComplexModel (r+n)) (mem_chart_source _ _) := by
  have hc := actualHolomorphicGermPullback_comp (f := blockProjection r n)
    (g := (Subtype.val : U → ComplexModel (r+n))) (contMDiff_blockProjection r n) contMDiff_subtype_val p
  rw [actualHolomorphicGermPullback_val U p] at hc
  change actualHolomorphicGermPullback (f := (fun q : U => blockProjection r n q))
    ((contMDiff_blockProjection r n).comp contMDiff_subtype_val) p = _ at hc
  rw [← map_wholeChartStalkIdeal_actual_pullback (f := (fun q : U => blockProjection r n q))
    ((contMDiff_blockProjection r n).comp contMDiff_subtype_val) A hA p,
    ← map_wholeChartStalkIdeal_actual_pullback (contMDiff_blockProjection r n) A hA (p : ComplexModel (r+n)),hc]
  rfl

/-- Every actual original open block-projection point retains its SAME genuine original product HS. -/
theorem hilbertSamuelAt_actual_open_block_projection_eq_product (r n : ℕ)
    (A : GermIdeal n (ComplexModel n)) (hA : A.IsCoherent)
    (U : Opens (ComplexModel (r+n))) (p : U) (ℓ : ℕ) :
    hilbertSamuelAt (GermIdeal.pullback (m := r+n) (fun q : U => blockProjection r n q) A) p ℓ =
      hilbertSamuelValue (Ideal.map (tangentPullback n r).toRingHom
        (wholeChartStalkIdeal A (blockProjection r n p) (blockProjection r n p) (mem_chart_source _ _))) ℓ := by
  change hilbertSamuelValue (wholeChartStalkIdeal _ p p (mem_chart_source _ p)) ℓ = _
  rw [wholeChartStalkIdeal_actual_open_block_projection r n A hA U p]
  exact hilbertSamuelAt_actual_block_projection_eq_product r n A hA p ℓ

/-- EVERY intrinsic HS order for the actual block projection on ANY true original open. -/
theorem hilbertSamuelAt_actual_open_block_projection_convolution (r n : ℕ)
    (A : GermIdeal n (ComplexModel n)) (hA : A.IsCoherent)
    (U : Opens (ComplexModel (r+n))) (p : U) (ℓ : ℕ) :
    let := normalExponentFintype r (ℓ+1)
    hilbertSamuelAt (GermIdeal.pullback (m := r+n) (fun q : U => blockProjection r n q) A) p ℓ =
      ∑ α : normalExponentIndex r (ℓ+1), hilbertSamuelAt A (blockProjection r n p) (ℓ-normalExponentDegree α.val) := by
  rw [hilbertSamuelAt_actual_open_block_projection_eq_product r n A hA U p ℓ]
  exact actualProductHilbertSamuel_convolution n r _ ℓ

/-- BOTH ENTIRE original profile directions at actual points of the SAME real product open. -/
theorem hilbertSamuelAt_actual_open_block_projection_entire_profile_eq_iff (r n : ℕ)
    (A : GermIdeal n (ComplexModel n)) (hA : A.IsCoherent)
    (U : Opens (ComplexModel (r+n))) (p q : U) :
    (∀ ℓ, hilbertSamuelAt (GermIdeal.pullback (m := r+n) (fun a : U => blockProjection r n a) A) p ℓ =
      hilbertSamuelAt (GermIdeal.pullback (m := r+n) (fun a : U => blockProjection r n a) A) q ℓ) ↔
        ∀ ℓ, hilbertSamuelAt A (blockProjection r n p) ℓ = hilbertSamuelAt A (blockProjection r n q) ℓ := by
  simp only [hilbertSamuelAt_actual_open_block_projection_eq_product r n A hA U]
  exact actualProductHS_entire_profile_eq_iff n r _ _
end
end Hironaka.HironakaActualBlockProjectionIntrinsicHS
