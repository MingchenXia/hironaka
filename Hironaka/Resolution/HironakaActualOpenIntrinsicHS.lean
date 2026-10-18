/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualBiholomorphicWholeStalkHS
import Hironaka.Invariant.SmoothCentreHomogeneity

/-! Genuine original open inclusions preserve the entire actual ideal and EXISTING intrinsic all-order HS. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualOpenIntrinsicHS
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetRankLoci
  HironakaActualWholeStalkHolomorphicPullback HironakaActualBiholomorphicWholeStalkHS
  HironakaActualWholeAmbientHSSuperlevel
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [IsComplexManifold n M] in
/-- The actual preferred subtype chart and ambient inverse give the SAME original coordinate near zero. -/
theorem actualTranslatedMap_val_eventually (U : Opens M) (y : U) :
    actualTranslatedMap (n := n) (m := n) (Subtype.val : U → M) y =ᶠ[𝓝 (0 : ComplexModel n)] id := by
  filter_upwards [(actualTranslatedMapDomain_isOpen (f := (Subtype.val : U → M)) contMDiff_subtype_val y).mem_nhds
    (zero_mem_actualTranslatedMapDomain (n := n) (m := n) (Subtype.val : U → M) y)] with z hz
  have hc : (chartAt (ComplexModel n) y) y = (chartAt (ComplexModel n) (y : M)) (y : M) := rfl
  have ht : z + (chartAt (ComplexModel n) y) y ∈
      ((chartAt (ComplexModel n) (y : M)).subtypeRestr ⟨y⟩).target := by
    simpa only [Opens.chartAt_eq] using hz.1
  have hi := (chartAt (ComplexModel n) (y : M)).subtypeRestr_symm_apply (⟨y⟩ : Nonempty U) ht
  simp only [Function.comp_apply] at hi
  change (chartAt (ComplexModel n) (y : M))
    (((chartAt (ComplexModel n) y).symm (z + (chartAt (ComplexModel n) y) y) : U) : M) -
      (chartAt (ComplexModel n) (y : M)) (y : M) = z
  change (chartAt (ComplexModel n) (y : M))
    ((((chartAt (ComplexModel n) (y : M)).subtypeRestr ⟨y⟩).symm
      (z + (chartAt (ComplexModel n) y) y) : U) : M) -
      (chartAt (ComplexModel n) (y : M)) (y : M) = z
  rw [hi,(chartAt (ComplexModel n) (y : M)).right_inv
    ((chartAt (ComplexModel n) (y : M)).subtypeRestr_target_subset ⟨y⟩ ht),hc,add_sub_cancel_right]

/-- The independently defined whole original open-inclusion pullback is the actual identity algebra map. -/
theorem actualHolomorphicGermPullback_val (U : Opens M) (y : U) :
    actualHolomorphicGermPullback (f := (Subtype.val : U → M)) contMDiff_subtype_val y =
      AlgHom.id ℂ (HolGerm (ComplexModel n)) := by
  apply AlgHom.ext
  intro a
  induction a using HolGerm.induction_on with
  | h F hF =>
    change actualHolomorphicGermPullback (f := (Subtype.val : U → M)) contMDiff_subtype_val y
      (HolGerm.mk F hF) = HolGerm.mk F hF
    unfold actualHolomorphicGermPullback
    rw [compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact (actualTranslatedMap_val_eventually U y).mono (fun z hz => congrArg F hz)

/-- ONLY original coherence gives BOTH entire original whole-stalk ideal directions under the genuine open inclusion. -/
theorem wholeChartStalkIdeal_actual_open_pullback (A : GermIdeal n M) (hA : A.IsCoherent)
    (U : Opens M) (y : U) :
    wholeChartStalkIdeal (GermIdeal.pullback (m := n) (Subtype.val : U → M) A) y y (mem_chart_source _ y) =
      wholeChartStalkIdeal A (y : M) (y : M) (mem_chart_source _ (y : M)) := by
  have h := map_wholeChartStalkIdeal_actual_pullback (f := (Subtype.val : U → M)) contMDiff_subtype_val A hA y
  rw [actualHolomorphicGermPullback_val U y] at h
  change Ideal.map (RingHom.id _) (wholeChartStalkIdeal A (y : M) (y : M) (mem_chart_source _ (y : M))) =
    wholeChartStalkIdeal (GermIdeal.pullback (m := n) (Subtype.val : U → M) A) y y (mem_chart_source _ y) at h
  simpa only [Ideal.map_id] using h.symm

/-- The EXISTING intrinsic original ambient HS value agrees at EVERY actual order after true open restriction. -/
theorem hilbertSamuelAt_actual_open_pullback (A : GermIdeal n M) (hA : A.IsCoherent)
    (U : Opens M) (y : U) (ℓ : ℕ) :
    hilbertSamuelAt (GermIdeal.pullback (m := n) (Subtype.val : U → M) A) y ℓ =
      hilbertSamuelAt A (y : M) ℓ := by
  unfold hilbertSamuelAt
  rw [wholeChartStalkIdeal_actual_open_pullback A hA U y]

/-- BOTH literal ALL-order original HS-condition directions retain the actual original threshold profile. -/
theorem actualWholeAmbientHSSuperlevel_actual_open_pullback (A : GermIdeal n M) (hA : A.IsCoherent)
    (U : Opens M) (h : ℕ → ℕ) :
    actualWholeAmbientHSSuperlevel (GermIdeal.pullback (m := n) (Subtype.val : U → M) A) h =
      (Subtype.val : U → M) ⁻¹' actualWholeAmbientHSSuperlevel A h := by
  ext y
  change (∀ ℓ, h ℓ ≤ hilbertSamuelAt (GermIdeal.pullback (m := n) (Subtype.val : U → M) A) y ℓ) ↔
    ∀ ℓ, h ℓ ≤ hilbertSamuelAt A (y : M) ℓ
  simp only [hilbertSamuelAt_actual_open_pullback A hA U]

/-- ONLY actual analyticity supplies genuine reduced-carrier ALL-order intrinsic HS transport to an actual open. -/
theorem hilbertSamuelAt_vanishing_actual_open {W : Set M}
    (hW : IsComplexAnalyticSubset (n := n) W) (U : Opens M) (y : U) (ℓ : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n := n) ((Subtype.val : U → M) ⁻¹' W)) y ℓ =
      hilbertSamuelAt (vanishingIdeal (n := n) W) (y : M) ℓ := by
  rw [← SmoothCentreHomogeneity.pullback_val_vanishingIdeal U W]
  exact hilbertSamuelAt_actual_open_pullback _ (CartanIrreducible.cartanCoherence W hW) U y ℓ

end
end Hironaka.HironakaActualOpenIntrinsicHS
