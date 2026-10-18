/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualPointExceptionalVanishing
import Hironaka.Resolution.HironakaActualPointBlowupExceptionalLocus

/-! The original whole vanishing ideals and point-chart geometric Hilbert–Samuel comparison. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualPointGeometricBennett
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm OkaRelationSheaf
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetRankLoci HironakaHolomorphicPointJets
  HironakaRelativeNormalDeformationInitialRelations HironakaActualPointExceptionalVanishing
  HironakaActualAnalyticBlowupTaylor HironakaActualAnalyticStrictGenerators
  HironakaActualPointInitialIdealInclusion HironakaActualPointNormalizedBennett
  HironakaActualPointBlowupExceptionalLocus
variable {n : ℕ}

private theorem originalVanishingOriginIdeal_representative (A : Set (ComplexModel n))
    (g : HolGerm (ComplexModel n)) (hg : g ∈ originalCoherentOriginIdeal (vanishingIdeal (n := n) A)) :
    ∃ (f : ComplexModel n → ℂ) (hf : HolAt f 0),
      g=HolGerm.mk f hf ∧ ∀ᶠ z in 𝓝 (0 : ComplexModel n), z ∈ A → f z=0 := by
  change g ∈ Ideal.span {g | ∃ (f : ComplexModel n → ℂ) (hf : HolAt f 0),
    (vanishingIdeal (n := n) A).mem 0 f ∧ g=HolGerm.mk f hf} at hg
  induction hg using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨f,hf,hAf,rfl⟩ := hg
      exact ⟨f,hf,rfl,hAf.2⟩
  | zero =>
      exact ⟨0,eventually_differentiableAt_zero,HolGerm.mk_zero.symm,Eventually.of_forall fun _ _ => rfl⟩
  | add g h _ _ hg hh =>
      obtain ⟨f,hf,rfl,hfA⟩ := hg
      obtain ⟨q,hq,rfl,hqA⟩ := hh
      refine ⟨fun z => f z+q z,eventually_differentiableAt_add hf hq,(HolGerm.mk_add _ _ hf hq).symm,?_⟩
      filter_upwards [hfA,hqA] with z hfz hqz hz
      rw [hfz hz,hqz hz,add_zero]
  | smul c g _ hg =>
      obtain ⟨f,hf,rfl,hfA⟩ := hg
      obtain ⟨q,hq,rfl⟩ := HolGerm.exists_eq_mk c
      refine ⟨fun z => q z*f z,eventually_differentiableAt_mul hq hf,?_,?_⟩
      · exact (HolGerm.mk_mul _ _ hq hf).symm
      · filter_upwards [hfA] with z hfz hz
        rw [hfz hz,mul_zero]

/-- The unchanged actual whole origin ideal has its genuine vanishing germ meaning without coherence. -/
theorem mk_mem_original_vanishing_origin_ideal_iff (A : Set (ComplexModel n))
    (f : ComplexModel n → ℂ) (hf : HolAt f 0) :
    HolGerm.mk f hf ∈ originalCoherentOriginIdeal (vanishingIdeal (n := n) A) ↔
      ∀ᶠ z in 𝓝 (0 : ComplexModel n), z ∈ A → f z=0 := by
  constructor
  · intro hg
    obtain ⟨q,hq,he,hqA⟩ := originalVanishingOriginIdeal_representative A _ hg
    filter_upwards [HolGerm.mk_eq_mk_iff.mp he,hqA] with z hez hqz hz
    exact hez.trans (hqz hz)
  · intro hfA
    exact Ideal.subset_span ⟨f,hf,⟨hf.mono fun _ h => h.mdifferentiableAt,hfA⟩,rfl⟩

/-- Actual local continuity identifies the ENTIRE original vanishing origin ideals of a set and its closure. -/
theorem originalVanishingOriginIdeal_closure (A : Set (ComplexModel n)) :
    originalCoherentOriginIdeal (vanishingIdeal (n := n) (closure A))=
      originalCoherentOriginIdeal (vanishingIdeal (n := n) A) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨f,hf,rfl⟩ := HolGerm.exists_eq_mk g
    apply (mk_mem_original_vanishing_origin_ideal_iff A f hf).mpr
    have h := (mk_mem_original_vanishing_origin_ideal_iff (closure A) f hf).mp hg
    exact h.mono fun _ hz hA => hz (subset_closure hA)
  · intro g hg
    obtain ⟨f,hf,rfl⟩ := HolGerm.exists_eq_mk g
    apply (mk_mem_original_vanishing_origin_ideal_iff (closure A) f hf).mpr
    exact eventually_zero_on_closure_of_eventually_continuous f A
      (hf.mono fun _ h => h.continuousAt) ((mk_mem_original_vanishing_origin_ideal_iff A f hf).mp hg)

private theorem chartTranslatedGerm_model_zero (f : ComplexModel n → ℂ) (hf : HolomorphicAt n f 0) :
    chartTranslatedGerm (0 : ComplexModel n) 0 (mem_chart_source (ComplexModel n) 0) f hf=
      HolGerm.mk f (hf.mono fun _ h => mdifferentiableAt_iff_differentiableAt.mp h) := by
  unfold chartTranslatedGerm translatedGerm
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun z => by simp [chartAt_self_eq]

/-- The original model chart at the original zero gives exactly the unchanged whole origin ideal. -/
theorem wholeChartStalkIdeal_model_zero (A : GermIdeal n (ComplexModel n)) :
    wholeChartStalkIdeal A 0 0 (mem_chart_source (ComplexModel n) 0)=originalCoherentOriginIdeal A := by
  unfold wholeChartStalkIdeal originalCoherentOriginIdeal
  apply congrArg Ideal.span
  ext g
  constructor
  · rintro ⟨f,hf,hAf,rfl⟩
    exact ⟨f,hf.mono fun _ h => mdifferentiableAt_iff_differentiableAt.mp h,hAf,
      chartTranslatedGerm_model_zero f hf⟩
  · rintro ⟨f,hf,hAf,rfl⟩
    have hfm : HolomorphicAt n f 0 := hf.mono fun _ h => h.mdifferentiableAt
    exact ⟨f,hfm,hAf,(chartTranslatedGerm_model_zero f hfm).symm⟩

/-- The SAME original intrinsic point function is the unchanged whole origin-ideal value at every order. -/
theorem hilbertSamuelAt_model_zero (A : GermIdeal n (ComplexModel n)) (ℓ : ℕ) :
    hilbertSamuelAt A 0 ℓ=hilbertSamuelValue (originalCoherentOriginIdeal A) ℓ := by
  unfold hilbertSamuelAt
  rw [wholeChartStalkIdeal_model_zero]

/-- The actual geometric strict vanishing ideal contains every genuine normalized point member for n>=2. -/
theorem actual_point_normalized_ideal_le_geometric_strict_vanishing
    (A : Set (ComplexModel n)) (hn : 2 ≤ n) (e : Fin n) (b : Fin n → ℂ) :
    actualAnalyticNormalizedMemberIdeal (originalCoherentOriginIdeal (vanishingIdeal (n := n) A)) Set.univ e b ≤
      originalCoherentOriginIdeal (vanishingIdeal (n := n)
        (strictTransform n (actualAnalyticBlowupMap Set.univ e b) A)) := by
  apply Ideal.span_le.mpr
  rintro h ⟨d,g,hgI,_hgp,hprod⟩
  obtain ⟨G,hG,rfl⟩ := HolGerm.exists_eq_mk g
  obtain ⟨H,hH,rfl⟩ := HolGerm.exists_eq_mk h
  apply (mk_mem_original_vanishing_origin_ideal_iff _ H hH).mpr
  have hz := actual_point_quotient_zero_on_exceptional_complement_closure A e b d G H hG hH
    ((mk_mem_original_vanishing_origin_ideal_iff A G hG).mp hgI) hprod
  have hsets : ((actualAnalyticBlowupMap Set.univ e b) ⁻¹' A \ exceptionalLocus n (actualAnalyticBlowupMap Set.univ e b)) ⊆
      ((actualAnalyticBlowupMap Set.univ e b) ⁻¹' A \ {z | z e=0}) := by
    intro y hy
    exact ⟨hy.1,fun hye => hy.2 (mem_exceptionalLocus_actual_point_blowup_of_coordinate_eq_zero hn e b y hye)⟩
  filter_upwards [hz] with z hzero hstrict
  exact hzero (closure_mono hsets hstrict)

/-- Actual geometric point-chart strict transforms do not increase ANY original whole origin-ideal HS value. -/
theorem hilbertSamuelValue_actual_geometric_point_strict_le
    (A : Set (ComplexModel n)) (e : Fin n) (b : Fin n → ℂ) (ℓ : ℕ) :
    hilbertSamuelValue (originalCoherentOriginIdeal (vanishingIdeal (n := n)
        (strictTransform n (actualAnalyticBlowupMap Set.univ e b) A))) ℓ ≤
      hilbertSamuelValue (originalCoherentOriginIdeal (vanishingIdeal (n := n) A)) ℓ := by
  have hnpos : 0<n := lt_of_le_of_lt (Nat.zero_le e.val) e.isLt
  by_cases hn : n=1
  · subst n
    have hs : strictTransform 1 (actualAnalyticBlowupMap Set.univ e b) A=closure A := by
      rw [strictTransform,exceptionalLocus_actual_point_blowup_one,actual_point_blowup_one_eq_id,sdiff_empty,preimage_id]
    simpa only [hs,originalVanishingOriginIdeal_closure] using
      (Nat.le_refl (hilbertSamuelValue (originalCoherentOriginIdeal (vanishingIdeal (n := 1) A)) ℓ))
  · have htwo : 2 ≤ n := by omega
    exact (hilbertSamuelValue_antitone_original_ideal _ _
      (actual_point_normalized_ideal_le_geometric_strict_vanishing A htwo e b) ℓ).trans
        (hilbertSamuelValue_actual_point_normalized_le_original n _ e b ℓ)

/-- The unchanged intrinsic geometric point function satisfies the actual point-chart inequality at every order. -/
theorem hilbertSamuelAt_actual_geometric_point_strict_le
    (A : Set (ComplexModel n)) (e : Fin n) (b : Fin n → ℂ) (ℓ : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n (actualAnalyticBlowupMap Set.univ e b) A)) 0 ℓ ≤
      hilbertSamuelAt (vanishingIdeal (n := n) A) 0 ℓ := by
  simp only [hilbertSamuelAt_model_zero]
  exact hilbertSamuelValue_actual_geometric_point_strict_le A e b ℓ

end
end Hironaka.HironakaActualPointGeometricBennett
