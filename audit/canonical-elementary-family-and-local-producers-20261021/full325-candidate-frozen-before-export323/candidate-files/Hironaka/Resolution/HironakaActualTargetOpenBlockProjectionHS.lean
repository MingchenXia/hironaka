/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualBlockProjectionIntrinsicHS

/-! Genuine source/target OPEN block projections and ENTIRE original HS.
Original ideal coherence is required only on the actual target open itself. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualTargetOpenBlockProjectionHS
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaSmoothSubmersionMonomialChartPullback HironakaRelativeNormalIdeal
  HironakaActualBlockProjectionIntrinsicHS HironakaActualProjectionIntrinsicHS
  HironakaActualWholeStalkHolomorphicPullback HironakaActualBiholomorphicWholeStalkHS
  HironakaActualOpenIntrinsicHS HironakaActualProductMixedHS HironakaActualProductHSProfileReflection
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetRankLoci
  HironakaRelativeNormalMonomialBasis
  HironakaHolomorphicPointJets HironakaSmoothCentreRealDomainActualAmbientHS

/-- The literal actual projection lands in the GENUINE target open. -/
def actualTargetOpenBlockProjection {r n : ℕ} (U : Opens (ComplexModel n))
    (V : Opens (ComplexModel (r+n))) (himage : ∀ p : V,blockProjection r n p ∈ U) : V → U :=
  fun p => ⟨blockProjection r n p,himage p⟩

theorem actualTargetOpenBlockProjection_contMDiff {r n : ℕ} (U : Opens (ComplexModel n))
    (V : Opens (ComplexModel (r+n))) (himage : ∀ p : V,blockProjection r n p ∈ U) :
    ContMDiff 𝓘(ℂ,ComplexModel (r+n)) 𝓘(ℂ,ComplexModel n) ∞ (actualTargetOpenBlockProjection U V himage) := by
  apply (ContMDiff.subtypeVal_comp_iff U _).mp
  exact (contMDiff_blockProjection r n).comp contMDiff_subtype_val

/-- BOTH actual open-inclusion identities give the true entire block germ map
BEFORE any ideal, HS or chart-extension assertion. -/
theorem actualTargetOpenBlockProjection_germ {r n : ℕ} (U : Opens (ComplexModel n))
    (V : Opens (ComplexModel (r+n))) (himage : ∀ p : V,blockProjection r n p ∈ U) (p : V) :
    actualHolomorphicGermPullback (actualTargetOpenBlockProjection_contMDiff U V himage) p=
      (actualHolomorphicGermPullback (actualBlockSwapDiffeomorph r n).contMDiff (p : ComplexModel (r+n))).comp
        (tangentPullback n r) := by
  have h1 := actualHolomorphicGermPullback_comp
    (f := (Subtype.val : U → ComplexModel n)) (g := actualTargetOpenBlockProjection U V himage)
    contMDiff_subtype_val (actualTargetOpenBlockProjection_contMDiff U V himage) p
  rw [actualHolomorphicGermPullback_val U (actualTargetOpenBlockProjection U V himage p)] at h1
  simp only [AlgHom.comp_id] at h1
  have h2 := actualHolomorphicGermPullback_comp (f := blockProjection r n)
    (g := (Subtype.val : V → ComplexModel (r+n))) (contMDiff_blockProjection r n) contMDiff_subtype_val p
  rw [actualHolomorphicGermPullback_val V p] at h2
  simp only [AlgHom.id_comp] at h2
  exact h1.symm.trans (h2.trans (actualGermPullback_blockProjection r n (p : ComplexModel (r+n))))

/-- ONLY original coherence on the ACTUAL TARGET OPEN supplies the WHOLE
original stalk ideal factorization, without a global ideal extension. -/
theorem wholeChartStalkIdeal_actual_target_open_block_projection {r n : ℕ}
    (U : Opens (ComplexModel n)) (V : Opens (ComplexModel (r+n)))
    (himage : ∀ p : V,blockProjection r n p ∈ U)
    (A : GermIdeal n U) (hA : A.IsCoherent) (p : V) :
    wholeChartStalkIdeal (GermIdeal.pullback (m := r+n) (actualTargetOpenBlockProjection U V himage) A)
      p p (mem_chart_source _ p)=
      Ideal.map (actualBiholomorphicGermAlgEquiv_models (actualBlockSwapDiffeomorph r n)
        (p : ComplexModel (r+n))).toRingEquiv.toRingHom
        (Ideal.map (tangentPullback n r).toRingHom
          (wholeChartStalkIdeal A (actualTargetOpenBlockProjection U V himage p)
            (actualTargetOpenBlockProjection U V himage p) (mem_chart_source _ _))) := by
  rw [←map_wholeChartStalkIdeal_actual_pullback (actualTargetOpenBlockProjection_contMDiff U V himage) A hA p,
    actualTargetOpenBlockProjection_germ,Ideal.map_map]
  rfl

/-- The EXISTING actual target-open pullback HS is the genuine product of the
SAME original target-open whole stalk at EVERY order. -/
theorem hilbertSamuelAt_actual_target_open_block_projection_eq_product {r n : ℕ}
    (U : Opens (ComplexModel n)) (V : Opens (ComplexModel (r+n)))
    (himage : ∀ p : V,blockProjection r n p ∈ U)
    (A : GermIdeal n U) (hA : A.IsCoherent) (p : V) (ℓ : ℕ) :
    hilbertSamuelAt (GermIdeal.pullback (m := r+n) (actualTargetOpenBlockProjection U V himage) A) p ℓ=
      hilbertSamuelValue (Ideal.map (tangentPullback n r).toRingHom
        (wholeChartStalkIdeal A (actualTargetOpenBlockProjection U V himage p)
          (actualTargetOpenBlockProjection U V himage p) (mem_chart_source _ _))) ℓ := by
  unfold hilbertSamuelAt
  rw [wholeChartStalkIdeal_actual_target_open_block_projection U V himage A hA p]
  exact (actualLocalAmbientJetAlgEquiv
    (actualBiholomorphicGermAlgEquiv_models (actualBlockSwapDiffeomorph r n) (p : ComplexModel (r+n)))
    _ (ℓ+1)).toLinearEquiv.finrank_eq.symm

/-- EVERY target-open original HS order is the actual free-parameter convolution. -/
theorem hilbertSamuelAt_actual_target_open_block_projection_convolution {r n : ℕ}
    (U : Opens (ComplexModel n)) (V : Opens (ComplexModel (r+n)))
    (himage : ∀ p : V,blockProjection r n p ∈ U)
    (A : GermIdeal n U) (hA : A.IsCoherent) (p : V) (ℓ : ℕ) :
    let := normalExponentFintype r (ℓ+1)
    hilbertSamuelAt (GermIdeal.pullback (m := r+n) (actualTargetOpenBlockProjection U V himage) A) p ℓ=
      ∑ α : normalExponentIndex r (ℓ+1),hilbertSamuelAt A (actualTargetOpenBlockProjection U V himage p)
        (ℓ-normalExponentDegree α.val) := by
  rw [hilbertSamuelAt_actual_target_open_block_projection_eq_product U V himage A hA p ℓ]
  exact actualProductHilbertSamuel_convolution n r _ ℓ

/-- BOTH ENTIRE actual profiles reflect the SAME original target-open profiles
at their actual original image points, requiring no coherence outside the open. -/
theorem hilbertSamuelAt_actual_target_open_block_projection_entire_profile_eq_iff {r n : ℕ}
    (U : Opens (ComplexModel n)) (V : Opens (ComplexModel (r+n)))
    (himage : ∀ p : V,blockProjection r n p ∈ U)
    (A : GermIdeal n U) (hA : A.IsCoherent) (p q : V) :
    (∀ ℓ,hilbertSamuelAt (GermIdeal.pullback (m := r+n) (actualTargetOpenBlockProjection U V himage) A) p ℓ=
      hilbertSamuelAt (GermIdeal.pullback (m := r+n) (actualTargetOpenBlockProjection U V himage) A) q ℓ) ↔
      ∀ ℓ,hilbertSamuelAt A (actualTargetOpenBlockProjection U V himage p) ℓ=
        hilbertSamuelAt A (actualTargetOpenBlockProjection U V himage q) ℓ := by
  simp only [hilbertSamuelAt_actual_target_open_block_projection_eq_product U V himage A hA]
  exact actualProductHS_entire_profile_eq_iff n r _ _

end
end Hironaka.HironakaActualTargetOpenBlockProjectionHS
