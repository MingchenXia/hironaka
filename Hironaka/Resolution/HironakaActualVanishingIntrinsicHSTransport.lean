/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualOpenIntrinsicHS
import Hironaka.Blowup.BlowupRestrictOpen

set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualVanishingIntrinsicHSTransport
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaHolomorphicJetRankLoci HironakaHolomorphicJetChartInvariance
  HironakaActualWholeStalkHolomorphicPullback HironakaActualBiholomorphicWholeStalkHS
  HironakaActualOpenIntrinsicHS HironakaSmoothCentreRealDomainActualAmbientHS
variable {n : ℕ}
section Biholomorphic
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- Actual inverse functions prove both entire original vanishing-ideal image directions for ANY subset. -/
theorem map_wholeChartStalkIdeal_vanishing_actual_biholomorphic
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X) (W : Set X) (y : Y) :
    Ideal.map (actualHolomorphicGermPullback e.contMDiff y).toRingHom
      (wholeChartStalkIdeal (vanishingIdeal (n := n) W) (e y) (e y) (mem_chart_source _ (e y)))=
      wholeChartStalkIdeal (vanishingIdeal (n := n) (e ⁻¹' W)) y y (mem_chart_source _ y) := by
  apply le_antisymm
  · rw [wholeChartStalkIdeal,Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro _ ⟨g,⟨f,hf,hfW,rfl⟩,rfl⟩
    change actualHolomorphicGermPullback e.contMDiff y
      (chartTranslatedGerm (e y) (e y) (mem_chart_source _ (e y)) f hf) ∈ _
    rw [actualHolomorphicGermPullback_original_function]
    have hcomp : HolomorphicAt n (f ∘ e) y :=
      hf.comp_contMDiff (Eventually.of_forall fun _ => e.contMDiff.contMDiffAt)
    apply Ideal.subset_span
    refine ⟨f ∘ e,hcomp,⟨hcomp,?_⟩,rfl⟩
    exact (e.contMDiff.continuous.tendsto y).eventually hfW.2
  · apply Ideal.span_le.mpr
    rintro _ ⟨h,hh,hhW,rfl⟩
    let f : X → ℂ := h ∘ e.symm
    have hhbase : HolomorphicAt n h (e.symm (e y)) := by
      simpa only [e.symm_apply_apply] using hh
    have hf : HolomorphicAt n f (e y) :=
      hhbase.comp_contMDiff (Eventually.of_forall fun _ => e.symm.contMDiff.contMDiffAt)
    have hfW : (vanishingIdeal (n := n) W).mem (e y) f := by
      refine ⟨hf,?_⟩
      have ht : Tendsto e.symm (𝓝 (e y)) (𝓝 y) := by
        simpa only [e.symm_apply_apply] using e.symm.contMDiff.continuous.tendsto (e y)
      filter_upwards [ht.eventually hhW.2] with x hx hxW
      exact hx (by simpa only [mem_preimage,e.apply_symm_apply] using hxW)
    have hsource : chartTranslatedGerm (e y) (e y) (mem_chart_source _ (e y)) f hf ∈
        wholeChartStalkIdeal (vanishingIdeal (n := n) W) (e y) (e y) (mem_chart_source _ (e y)) :=
      Ideal.subset_span ⟨f,hf,hfW,rfl⟩
    have hmem := Ideal.mem_map_of_mem (actualHolomorphicGermPullback e.contMDiff y).toRingHom hsource
    change actualHolomorphicGermPullback e.contMDiff y
      (chartTranslatedGerm (e y) (e y) (mem_chart_source _ (e y)) f hf) ∈ _ at hmem
    rw [actualHolomorphicGermPullback_original_function] at hmem
    have hcomp : HolomorphicAt n (f ∘ e) y :=
      hf.comp_contMDiff (Eventually.of_forall fun _ => e.contMDiff.contMDiffAt)
    have he : f ∘ e=h := by
      funext z
      simp [f]
    have heq : chartTranslatedGerm y y (mem_chart_source _ y) (f ∘ e) hcomp=
        chartTranslatedGerm y y (mem_chart_source _ y) h hh := by
      unfold chartTranslatedGerm translatedGerm
      apply HolGerm.mk_eq_mk_iff.mpr
      exact Eventually.of_forall fun z => congrFun he
        ((chartAt (ComplexModel n) y).symm (z+(chartAt (ComplexModel n) y) y))
    exact heq ▸ hmem

/-- Every existing intrinsic order is invariant under actual biholomorphic transport of ANY subset. -/
theorem hilbertSamuelAt_vanishing_actual_biholomorphic_any
    (e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X) (W : Set X) (y : Y) (ℓ : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n := n) (e ⁻¹' W)) y ℓ=
      hilbertSamuelAt (vanishingIdeal (n := n) W) (e y) ℓ := by
  unfold hilbertSamuelAt
  rw [← map_wholeChartStalkIdeal_vanishing_actual_biholomorphic e W y]
  exact actualAmbientHS_eq_of_genuineAlgEquiv (actualBiholomorphicGermAlgEquiv e y) _ ℓ
end Biholomorphic
section OpenRestriction
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- True restriction and original zero extension prove both entire image directions for ANY subset. -/
theorem map_wholeChartStalkIdeal_vanishing_actual_open (U : Opens M) (W : Set M) (y : U) :
    Ideal.map (actualHolomorphicGermPullback (f := (Subtype.val : U → M)) contMDiff_subtype_val y).toRingHom
      (wholeChartStalkIdeal (vanishingIdeal (n := n) W) (y : M) (y : M) (mem_chart_source _ (y : M)))=
      wholeChartStalkIdeal (vanishingIdeal (n := n) ((Subtype.val : U → M) ⁻¹' W)) y y (mem_chart_source _ y) := by
  apply le_antisymm
  · rw [wholeChartStalkIdeal,Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro _ ⟨g,⟨f,hf,hfW,rfl⟩,rfl⟩
    change actualHolomorphicGermPullback (f := (Subtype.val : U → M)) contMDiff_subtype_val y
      (chartTranslatedGerm (y : M) (y : M) (mem_chart_source _ (y : M)) f hf) ∈ _
    rw [actualHolomorphicGermPullback_original_function]
    have hcomp : HolomorphicAt n (f ∘ (Subtype.val : U → M)) y :=
      hf.comp_contMDiff (Eventually.of_forall fun _ => contMDiff_subtype_val.contMDiffAt)
    exact Ideal.subset_span ⟨f ∘ (Subtype.val : U → M),hcomp,
      BlowupRestrictOpen.vanishingIdeal_opens_mem_comp_val U hfW,rfl⟩
  · apply Ideal.span_le.mpr
    rintro _ ⟨h,hh,hhW,rfl⟩
    let f : M → ℂ := extendOpens U h
    have hf : HolomorphicAt n f (y : M) := (holomorphicAt_iff_extendOpens U).mp hh
    have hfW : (vanishingIdeal (n := n) W).mem (y : M) f :=
      (BlowupRestrictOpen.vanishingIdeal_opens_mem_iff U).mp hhW
    have hsource : chartTranslatedGerm (y : M) (y : M) (mem_chart_source _ (y : M)) f hf ∈
        wholeChartStalkIdeal (vanishingIdeal (n := n) W) (y : M) (y : M) (mem_chart_source _ (y : M)) :=
      Ideal.subset_span ⟨f,hf,hfW,rfl⟩
    have hmem := Ideal.mem_map_of_mem
      (actualHolomorphicGermPullback (f := (Subtype.val : U → M)) contMDiff_subtype_val y).toRingHom hsource
    change actualHolomorphicGermPullback (f := (Subtype.val : U → M)) contMDiff_subtype_val y
      (chartTranslatedGerm (y : M) (y : M) (mem_chart_source _ (y : M)) f hf) ∈ _ at hmem
    rw [actualHolomorphicGermPullback_original_function] at hmem
    have hcomp : HolomorphicAt n (f ∘ (Subtype.val : U → M)) y :=
      hf.comp_contMDiff (Eventually.of_forall fun _ => contMDiff_subtype_val.contMDiffAt)
    have he : f ∘ (Subtype.val : U → M)=h := by
      funext z
      exact extendOpens_val U h z
    have heq : chartTranslatedGerm y y (mem_chart_source _ y) (f ∘ (Subtype.val : U → M)) hcomp=
        chartTranslatedGerm y y (mem_chart_source _ y) h hh := by
      unfold chartTranslatedGerm translatedGerm
      apply HolGerm.mk_eq_mk_iff.mpr
      exact Eventually.of_forall fun z => congrFun he
        ((chartAt (ComplexModel n) y).symm (z+(chartAt (ComplexModel n) y) y))
    exact heq ▸ hmem

/-- The actual open germ map is the existing identity, giving equality of the same original whole ideals. -/
theorem wholeChartStalkIdeal_vanishing_actual_open (U : Opens M) (W : Set M) (y : U) :
    wholeChartStalkIdeal (vanishingIdeal (n := n) ((Subtype.val : U → M) ⁻¹' W)) y y (mem_chart_source _ y)=
      wholeChartStalkIdeal (vanishingIdeal (n := n) W) (y : M) (y : M) (mem_chart_source _ (y : M)) := by
  have h := map_wholeChartStalkIdeal_vanishing_actual_open (n := n) U W y
  rw [actualHolomorphicGermPullback_val (n := n) U y] at h
  change Ideal.map (RingHom.id _)
    (wholeChartStalkIdeal (vanishingIdeal (n := n) W) (y : M) (y : M) (mem_chart_source _ (y : M)))=
    wholeChartStalkIdeal (vanishingIdeal (n := n) ((Subtype.val : U → M) ⁻¹' W)) y y (mem_chart_source _ y) at h
  simpa only [Ideal.map_id] using h.symm

/-- The unchanged intrinsic point function agrees at every order on the true open subtype for ANY subset. -/
theorem hilbertSamuelAt_vanishing_actual_open_any (U : Opens M) (W : Set M) (y : U) (ℓ : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n := n) ((Subtype.val : U → M) ⁻¹' W)) y ℓ=
      hilbertSamuelAt (vanishingIdeal (n := n) W) (y : M) ℓ := by
  unfold hilbertSamuelAt
  rw [wholeChartStalkIdeal_vanishing_actual_open (n := n) U W y]
end OpenRestriction
end
end Hironaka.HironakaActualVanishingIntrinsicHSTransport
