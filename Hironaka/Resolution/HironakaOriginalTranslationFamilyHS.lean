/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalCurveTranslationFamily
import Hironaka.Resolution.HironakaActualBlockProjectionIntrinsicHS

/-! Genuine zero-section geometry before existing all-order HS family comparison. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaOriginalTranslationFamilyHS
noncomputable section
open Hironaka.HolomorphicIdealSheaves
  HironakaOriginalCurveTranslationFamily HironakaSmoothSubmersionMonomialChartPullback
  HironakaActualBlockProjectionIntrinsicHS HironakaActualProjectionIntrinsicHS
  HironakaSmoothCentreRealDomainActualAmbientHS HironakaRelativeNormalMonomialBasis
  HironakaHolomorphicJetChartInvariance

def actualTranslationZeroSection {d n : ℕ} (U : Opens (ComplexModel d))
    (a : U) : actualParameterProductOpen d n U :=
  ⟨joinCoordinates d n a 0,by
    change fibreProjection d n (joinCoordinates d n a 0) ∈ U
    rw [fibreProjection_join]
    exact a.property⟩

def actualTranslationZeroTrace {d n : ℕ} (U : Opens (ComplexModel d)) : Set (actualParameterProductOpen d n U) :=
  {p | blockProjection d n p=0}

theorem actualTranslationZeroSection_continuous {d n : ℕ} (U : Opens (ComplexModel d)) :
    Continuous (actualTranslationZeroSection (n := n) U) := by
  have hraw : Continuous (fun a : U => joinCoordinates d n a 0) :=
    (splitCoordinates d n).symm.continuous.comp (continuous_subtype_val.prodMk continuous_const)
  exact hraw.subtype_mk _

@[simp] theorem actualParameter_zeroSection {d n : ℕ} (U : Opens (ComplexModel d)) (a : U) :
    actualProductParameter U (actualTranslationZeroSection (n := n) U a)=a := by
  apply Subtype.ext
  exact fibreProjection_join d n a 0

@[simp] theorem actualZeroSection_mem {d n : ℕ} (U : Opens (ComplexModel d)) (a : U) :
    actualTranslationZeroSection (n := n) U a ∈ actualTranslationZeroTrace U :=
  blockProjection_join d n a 0

theorem actualZeroSection_parameter {d n : ℕ} (U : Opens (ComplexModel d))
    (p : actualParameterProductOpen d n U) (hp : p ∈ actualTranslationZeroTrace U) :
    actualTranslationZeroSection U (actualProductParameter U p)=p := by
  apply Subtype.ext
  change joinCoordinates d n (fibreProjection d n p) 0=(p : ComplexModel (d+n))
  rw [←hp]
  exact joinCoordinates_projections d n p

theorem actualZeroSection_range {d n : ℕ} (U : Opens (ComplexModel d)) :
    Set.range (actualTranslationZeroSection (n := n) U)=actualTranslationZeroTrace U := by
  ext p
  constructor
  · rintro ⟨a,rfl⟩
    exact actualZeroSection_mem U a
  · intro hp
    exact ⟨actualProductParameter U p,actualZeroSection_parameter U p hp⟩

@[simp] theorem actualFamily_zeroSection {d n : ℕ} (U : Opens (ComplexModel d))
    (γ : U → ComplexModel n) (a : U) :
    actualTranslationFamily U γ (actualTranslationZeroSection U a)=γ a := by
  change γ (actualProductParameter U (actualTranslationZeroSection U a))+
    blockProjection d n (joinCoordinates d n a 0)=γ a
  rw [actualParameter_zeroSection,blockProjection_join,add_zero]

theorem actualFamily_onZero {d n : ℕ} (U : Opens (ComplexModel d))
    (γ : U → ComplexModel n) (p : actualParameterProductOpen d n U)
    (hp : p ∈ actualTranslationZeroTrace U) :
    actualTranslationFamily U γ p=γ (actualProductParameter U p) := by
  change γ (actualProductParameter U p)+blockProjection d n p=γ (actualProductParameter U p)
  rw [hp,add_zero]

/-- ANY actual parameter function has the same genuine local constancy after
its true parameter-map composite on the actual zero section. -/
theorem actualZeroTrace_parameter_localConst_iff {d n : ℕ} (U : Opens (ComplexModel d))
    {Λ : Type*} (g : U → Λ) (a : U) :
    (∃ W : Set (actualParameterProductOpen d n U),IsOpen W ∧
      actualTranslationZeroSection U a ∈ W ∧
      ∀ p ∈ actualTranslationZeroTrace U ∩ W,g (actualProductParameter U p)=g a) ↔
    ∃ V : Set U,IsOpen V ∧ a ∈ V ∧ ∀ b ∈ V,g b=g a := by
  constructor
  · rintro ⟨W,hWo,haW,hvalue⟩
    refine ⟨(actualTranslationZeroSection (n := n) U) ⁻¹' W,
      hWo.preimage (actualTranslationZeroSection_continuous U),haW,?_⟩
    intro b hb
    simpa only [actualParameter_zeroSection] using hvalue (actualTranslationZeroSection U b)
      ⟨actualZeroSection_mem U b,hb⟩
  · rintro ⟨V,hVo,haV,hvalue⟩
    refine ⟨(actualProductParameter U) ⁻¹' V,
      hVo.preimage (actualProductParameter_contMDiff U).continuous,?_,?_⟩
    · simpa only [mem_preimage,actualParameter_zeroSection] using haV
    · intro p hp
      exact hvalue (actualProductParameter U p) hp.2

private theorem actualFamily_hs_projection {d n : ℕ} (U : Opens (ComplexModel d))
    (γ : U → ComplexModel n) (hγ : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel n) ∞ γ)
    (A : GermIdeal n (ComplexModel n)) (hA : A.IsCoherent)
    (p : actualParameterProductOpen d n U) (ℓ : ℕ) :
    hilbertSamuelAt (GermIdeal.pullback (m := d+n) (actualTranslationFamily U γ) A) p ℓ=
      hilbertSamuelAt (GermIdeal.pullback (m := d+n)
        (fun q : actualParameterProductOpen d n U => blockProjection d n q) A)
        (actualTranslationShear U γ hγ p) ℓ := by
  rw [(actualTranslationFamily_entire_pullback U γ hγ A hA).2.1]
  exact hilbertSamuelAt_actual_biholomorphic_models (actualTranslationShear U γ hγ) _
    (GermIdealPullbackCalculus.isCoherent_pullback
      ((contMDiff_blockProjection d n).comp contMDiff_subtype_val) hA) p ℓ

/-- EVERY original actual family HS order is the true free-parameter convolution. -/
theorem actualTranslationFamily_hs_convolution {d n : ℕ} (U : Opens (ComplexModel d))
    (γ : U → ComplexModel n) (hγ : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel n) ∞ γ)
    (A : GermIdeal n (ComplexModel n)) (hA : A.IsCoherent)
    (p : actualParameterProductOpen d n U) (ℓ : ℕ) :
    let := normalExponentFintype d (ℓ+1)
    hilbertSamuelAt (GermIdeal.pullback (m := d+n) (actualTranslationFamily U γ) A) p ℓ=
      ∑ α : normalExponentIndex d (ℓ+1),hilbertSamuelAt A (actualTranslationFamily U γ p)
        (ℓ-normalExponentDegree α.val) := by
  rw [actualFamily_hs_projection U γ hγ A hA p ℓ]
  have hp : blockProjection d n (actualTranslationShear U γ hγ p)=actualTranslationFamily U γ p :=
    (congrFun (actualTranslationFamily_eq_projection_shear U γ hγ) p).symm
  simpa only [hp] using hilbertSamuelAt_actual_open_block_projection_convolution d n A hA
    (actualParameterProductOpen d n U) (actualTranslationShear U γ hγ p) ℓ

/-- BOTH ENTIRE family-profile equality directions reflect the SAME original
profiles at the TWO actual original family images, with no finite cutoff. -/
theorem actualTranslationFamily_entire_profile_eq_iff {d n : ℕ} (U : Opens (ComplexModel d))
    (γ : U → ComplexModel n) (hγ : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel n) ∞ γ)
    (A : GermIdeal n (ComplexModel n)) (hA : A.IsCoherent)
    (p q : actualParameterProductOpen d n U) :
    (∀ ℓ,hilbertSamuelAt (GermIdeal.pullback (m := d+n) (actualTranslationFamily U γ) A) p ℓ=
      hilbertSamuelAt (GermIdeal.pullback (m := d+n) (actualTranslationFamily U γ) A) q ℓ) ↔
      ∀ ℓ,hilbertSamuelAt A (actualTranslationFamily U γ p) ℓ=hilbertSamuelAt A (actualTranslationFamily U γ q) ℓ := by
  simp only [actualFamily_hs_projection U γ hγ A hA]
  have hp : blockProjection d n (actualTranslationShear U γ hγ p)=actualTranslationFamily U γ p :=
    (congrFun (actualTranslationFamily_eq_projection_shear U γ hγ) p).symm
  have hq : blockProjection d n (actualTranslationShear U γ hγ q)=actualTranslationFamily U γ q :=
    (congrFun (actualTranslationFamily_eq_projection_shear U γ hγ) q).symm
  simpa only [hp,hq] using hilbertSamuelAt_actual_open_block_projection_entire_profile_eq_iff d n A hA
    (actualParameterProductOpen d n U) (actualTranslationShear U γ hγ p) (actualTranslationShear U γ hγ q)

/-- Actual zero-section original images are gamma itself, retaining ALL orders. -/
theorem actualTranslationZeroSection_entire_profile_eq_iff {d n : ℕ} (U : Opens (ComplexModel d))
    (γ : U → ComplexModel n) (hγ : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel n) ∞ γ)
    (A : GermIdeal n (ComplexModel n)) (hA : A.IsCoherent) (a b : U) :
    (∀ ℓ,hilbertSamuelAt (GermIdeal.pullback (m := d+n) (actualTranslationFamily U γ) A) (actualTranslationZeroSection U a) ℓ=
      hilbertSamuelAt (GermIdeal.pullback (m := d+n) (actualTranslationFamily U γ) A) (actualTranslationZeroSection U b) ℓ) ↔
      ∀ ℓ,hilbertSamuelAt A (γ a) ℓ=hilbertSamuelAt A (γ b) ℓ := by
  simpa only [actualFamily_zeroSection] using actualTranslationFamily_entire_profile_eq_iff U γ hγ A hA
    (actualTranslationZeroSection U a) (actualTranslationZeroSection U b)

private theorem actualFamily_onZero_profile_iff {d n : ℕ} (U : Opens (ComplexModel d))
    (γ : U → ComplexModel n) (hγ : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel n) ∞ γ)
    (A : GermIdeal n (ComplexModel n)) (hA : A.IsCoherent)
    (p : actualParameterProductOpen d n U) (hp : p ∈ actualTranslationZeroTrace U) (a : U) :
    (∀ ℓ,hilbertSamuelAt (GermIdeal.pullback (m := d+n) (actualTranslationFamily U γ) A) p ℓ=
      hilbertSamuelAt (GermIdeal.pullback (m := d+n) (actualTranslationFamily U γ) A) (actualTranslationZeroSection U a) ℓ) ↔
      ∀ ℓ,hilbertSamuelAt A (γ (actualProductParameter U p)) ℓ=hilbertSamuelAt A (γ a) ℓ := by
  simpa only [actualFamily_onZero U γ p hp,actualFamily_zeroSection] using
    actualTranslationFamily_entire_profile_eq_iff U γ hγ A hA p (actualTranslationZeroSection U a)

/-- True actual neighborhood local constancy of the ENTIRE family profile on
its literal zero section is equivalent to ALL-order ORIGINAL parameter constancy. -/
theorem actualTranslationZeroTrace_hs_localConst_iff {d n : ℕ} (U : Opens (ComplexModel d))
    (γ : U → ComplexModel n) (hγ : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel n) ∞ γ)
    (A : GermIdeal n (ComplexModel n)) (hA : A.IsCoherent) (a : U) :
    (∃ W : Set (actualParameterProductOpen d n U),IsOpen W ∧ actualTranslationZeroSection U a ∈ W ∧
      ∀ p ∈ actualTranslationZeroTrace U ∩ W,∀ ℓ,
        hilbertSamuelAt (GermIdeal.pullback (m := d+n) (actualTranslationFamily U γ) A) p ℓ=
          hilbertSamuelAt (GermIdeal.pullback (m := d+n) (actualTranslationFamily U γ) A) (actualTranslationZeroSection U a) ℓ) ↔
    ∃ V : Set U,IsOpen V ∧ a ∈ V ∧ ∀ b ∈ V,∀ ℓ,hilbertSamuelAt A (γ b) ℓ=hilbertSamuelAt A (γ a) ℓ := by
  let g : U → (ℕ → ℕ) := fun b ℓ => hilbertSamuelAt A (γ b) ℓ
  constructor
  · rintro ⟨W,hW,haW,hvalue⟩
    have hgen : ∃ W : Set (actualParameterProductOpen d n U),IsOpen W ∧
        actualTranslationZeroSection U a ∈ W ∧
        ∀ p ∈ actualTranslationZeroTrace U ∩ W,g (actualProductParameter U p)=g a := by
      refine ⟨W,hW,haW,?_⟩
      intro p hp
      exact funext ((actualFamily_onZero_profile_iff U γ hγ A hA p hp.1 a).mp (hvalue p hp))
    obtain ⟨V,hV,haV,hg⟩ := (actualZeroTrace_parameter_localConst_iff U g a).mp hgen
    exact ⟨V,hV,haV,fun b hb ℓ => congrFun (hg b hb) ℓ⟩
  · rintro ⟨V,hV,haV,hvalue⟩
    have hgen : ∃ V : Set U,IsOpen V ∧ a ∈ V ∧ ∀ b ∈ V,g b=g a :=
      ⟨V,hV,haV,fun b hb => funext (hvalue b hb)⟩
    obtain ⟨W,hW,haW,hg⟩ := (actualZeroTrace_parameter_localConst_iff (n := n) U g a).mpr hgen
    refine ⟨W,hW,haW,?_⟩
    intro p hp
    exact (actualFamily_onZero_profile_iff U γ hγ A hA p hp.1 a).mpr (fun ℓ => congrFun (hg p hp) ℓ)

/-- ONLY true ORIGINAL curve regularity and ORIGINAL ideal coherence supply
ONE actual parameter and the genuine ENTIRE family/original localconst equivalence. -/
theorem exists_original_curve_translation_hs_localConst {t : ℕ}
    (C : Set (ComplexModel (1+t))) (x : ComplexModel (1+t)) (hreg : RegularAtDim (n := 1+t) C x 1)
    (A : GermIdeal (1+t) (ComplexModel (1+t))) (hA : A.IsCoherent) :
    ∃ (U : Opens (ComplexModel 1)) (h0U : (0 : ComplexModel 1) ∈ U)
      (γ : U → ComplexModel (1+t)) (_hγ : ContMDiff 𝓘(ℂ,ComplexModel 1) 𝓘(ℂ,ComplexModel (1+t)) ∞ γ)
      (D : Opens (ComplexModel (1+t))),
      x ∈ D ∧ γ ⟨0,h0U⟩=x ∧ Function.Injective γ ∧ C ∩ (D : Set (ComplexModel (1+t)))=Set.range γ ∧
      ∀ a : U,
        (∃ W : Set (actualParameterProductOpen 1 (1+t) U),IsOpen W ∧ actualTranslationZeroSection U a ∈ W ∧
          ∀ p ∈ actualTranslationZeroTrace U ∩ W,∀ ℓ,
            hilbertSamuelAt (GermIdeal.pullback (m := 1+(1+t)) (actualTranslationFamily U γ) A) p ℓ=
              hilbertSamuelAt (GermIdeal.pullback (m := 1+(1+t)) (actualTranslationFamily U γ) A) (actualTranslationZeroSection U a) ℓ) ↔
        ∃ V : Set U,IsOpen V ∧ a ∈ V ∧ ∀ b ∈ V,∀ ℓ,hilbertSamuelAt A (γ b) ℓ=hilbertSamuelAt A (γ a) ℓ := by
  obtain ⟨U,h0U,γ,D,hxD,hγ,hγ0,hinj,htrace⟩ := exists_original_regular_curve_parameter C x hreg
  exact ⟨U,h0U,γ,hγ,D,hxD,hγ0,hinj,htrace,fun a => actualTranslationZeroTrace_hs_localConst_iff U γ hγ A hA a⟩

end
end Hironaka.HironakaOriginalTranslationFamilyHS
