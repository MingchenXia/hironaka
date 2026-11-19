/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalCentreAnalyticHSException
import Hironaka.Resolution.HironakaActualWholeStalkHolomorphicPullback
import Hironaka.Resolution.HironakaSmoothSubmersionMonomialChartPullback

/-! Real original curve parametrizations, actual translation shears and ENTIRE
original pullback ideals. No product-HS or higher-history comparison is assumed. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaOriginalCurveTranslationFamily
noncomputable section
open Hironaka.HolomorphicIdealSheaves
  HironakaSmoothSubmersionMonomialChartPullback HironakaRelativeNormalIdeal
  HironakaSmoothCentreCoherentDomain HironakaSmoothCentreRealDomainOriginalCentreOpen
  HironakaSmoothCentreNearbyStalks BlowupFlatCoordinates
  HironakaActualWholeStalkHolomorphicPullback HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetRankLoci RelativePrincipalizationSpan

/-- The TRUE full product window, using the actual original parameter open. -/
def actualParameterProductOpen (d n : ℕ) (U : Opens (ComplexModel d)) : Opens (ComplexModel (d+n)) :=
  ⟨fibreProjection d n ⁻¹' (U : Set (ComplexModel d)),
    U.isOpen.preimage (contMDiff_fibreProjection d n).continuous⟩

def actualProductParameter {d n : ℕ} (U : Opens (ComplexModel d))
    (p : actualParameterProductOpen d n U) : U := ⟨fibreProjection d n p,p.property⟩

/-- The literal genuine curve family F(u,z)=gamma(u)+z. -/
def actualTranslationFamily {d n : ℕ} (U : Opens (ComplexModel d))
    (γ : U → ComplexModel n) (p : actualParameterProductOpen d n U) : ComplexModel n :=
  γ (actualProductParameter U p)+blockProjection d n p

theorem actualProductParameter_contMDiff {d n : ℕ} (U : Opens (ComplexModel d)) :
    ContMDiff 𝓘(ℂ,ComplexModel (d+n)) 𝓘(ℂ,ComplexModel d) ∞ (actualProductParameter (n := n) U) := by
  apply (ContMDiff.subtypeVal_comp_iff U _).mp
  exact (contMDiff_fibreProjection d n).comp contMDiff_subtype_val

theorem actualTranslationFamily_contMDiff {d n : ℕ} (U : Opens (ComplexModel d))
    (γ : U → ComplexModel n) (hγ : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel n) ∞ γ) :
    ContMDiff 𝓘(ℂ,ComplexModel (d+n)) 𝓘(ℂ,ComplexModel n) ∞ (actualTranslationFamily U γ) :=
  (hγ.comp (actualProductParameter_contMDiff U)).add
    ((contMDiff_blockProjection d n).comp contMDiff_subtype_val)

private theorem actual_join_contMDiff {r d n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel r) M] [IsComplexManifold r M]
    {a : M → ComplexModel d} {b : M → ComplexModel n}
    (ha : ContMDiff 𝓘(ℂ,ComplexModel r) 𝓘(ℂ,ComplexModel d) ∞ a)
    (hb : ContMDiff 𝓘(ℂ,ComplexModel r) 𝓘(ℂ,ComplexModel n) ∞ b) :
    ContMDiff 𝓘(ℂ,ComplexModel r) 𝓘(ℂ,ComplexModel (d+n)) ∞ (fun p => joinCoordinates d n (a p) (b p)) := by
  have hleft : ContMDiff 𝓘(ℂ,ComplexModel r) 𝓘(ℂ,ComplexModel (d+n)) ∞
      (fun p => fibreInclusion d n (a p)) := (fibreInclusion d n).contDiff.contMDiff.comp ha
  have hright : ContMDiff 𝓘(ℂ,ComplexModel r) 𝓘(ℂ,ComplexModel (d+n)) ∞
      (fun p => blockInclusion d n (b p)) := (blockInclusion d n).contDiff.contMDiff.comp hb
  exact (hleft.add hright).congr (fun p => joinCoordinates_eq_add d n (a p) (b p))

/-- The actual shear and inverse live on the SAME real product-open manifold. -/
def actualTranslationShear {d n : ℕ} (U : Opens (ComplexModel d))
    (γ : U → ComplexModel n) (hγ : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel n) ∞ γ) :
    actualParameterProductOpen d n U ≃ₘ⟮𝓘(ℂ,ComplexModel (d+n)),𝓘(ℂ,ComplexModel (d+n))⟯
      actualParameterProductOpen d n U where
  toEquiv :=
    { toFun := fun p => ⟨joinCoordinates d n (fibreProjection d n p) (actualTranslationFamily U γ p),
        by
          change fibreProjection d n (joinCoordinates d n _ _) ∈ U
          rw [fibreProjection_join]
          exact p.property⟩
      invFun := fun p => ⟨joinCoordinates d n (fibreProjection d n p)
        (blockProjection d n p-γ (actualProductParameter U p)),
        by
          change fibreProjection d n (joinCoordinates d n _ _) ∈ U
          rw [fibreProjection_join]
          exact p.property⟩
      left_inv := by
        intro p
        apply Subtype.ext
        change joinCoordinates d n _ (_-γ _)=(p : ComplexModel (d+n))
        simp only [fibreProjection_join,blockProjection_join,actualProductParameter,actualTranslationFamily]
        rw [add_sub_cancel_left,joinCoordinates_projections]
      right_inv := by
        intro p
        apply Subtype.ext
        change joinCoordinates d n _ (γ _+_)=(p : ComplexModel (d+n))
        simp only [fibreProjection_join,blockProjection_join,actualProductParameter]
        rw [←add_sub_assoc,add_sub_cancel_left,joinCoordinates_projections] }
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (actualParameterProductOpen d n U) _).mp
    change ContMDiff 𝓘(ℂ,ComplexModel (d+n)) 𝓘(ℂ,ComplexModel (d+n)) ∞
      (fun p : actualParameterProductOpen d n U => joinCoordinates d n (fibreProjection d n p) (actualTranslationFamily U γ p))
    exact actual_join_contMDiff ((contMDiff_fibreProjection d n).comp contMDiff_subtype_val)
      (actualTranslationFamily_contMDiff U γ hγ)
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff (actualParameterProductOpen d n U) _).mp
    change ContMDiff 𝓘(ℂ,ComplexModel (d+n)) 𝓘(ℂ,ComplexModel (d+n)) ∞
      (fun p : actualParameterProductOpen d n U => joinCoordinates d n (fibreProjection d n p)
        (blockProjection d n p-γ (actualProductParameter U p)))
    exact actual_join_contMDiff ((contMDiff_fibreProjection d n).comp contMDiff_subtype_val)
      (((contMDiff_blockProjection d n).comp contMDiff_subtype_val).sub (hγ.comp (actualProductParameter_contMDiff U)))

theorem actualTranslationFamily_eq_projection_shear {d n : ℕ} (U : Opens (ComplexModel d))
    (γ : U → ComplexModel n) (hγ : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel n) ∞ γ) :
    actualTranslationFamily U γ=(fun p : actualParameterProductOpen d n U => blockProjection d n p) ∘
      actualTranslationShear U γ hγ := by
  funext p
  exact (blockProjection_join d n _ _).symm

/-- ONLY original regularity supplies the actual curve, its entire window,
BOTH true original image directions, basepoint and parameter injectivity. -/
theorem exists_original_regular_curve_parameter {t : ℕ} (C : Set (ComplexModel (1+t)))
    (x : ComplexModel (1+t)) (hreg : RegularAtDim (n := 1+t) C x 1) :
    ∃ (U : Opens (ComplexModel 1)) (h0U : (0 : ComplexModel 1) ∈ U)
      (γ : U → ComplexModel (1+t)) (D : Opens (ComplexModel (1+t))),
      x ∈ D ∧ ContMDiff 𝓘(ℂ,ComplexModel 1) 𝓘(ℂ,ComplexModel (1+t)) ∞ γ ∧
      γ ⟨0,h0U⟩=x ∧ Function.Injective γ ∧ C ∩ (D : Set (ComplexModel (1+t)))=Set.range γ := by
  obtain ⟨_,_,Φ,hsrc,h0,hflat⟩ := hreg
  let U : Opens (ComplexModel 1) := ⟨(tangentInclusion 1 t) ⁻¹' Φ.target,
    Φ.isOpen_target.preimage (tangentInclusion 1 t).continuous⟩
  have h0U : (0 : ComplexModel 1) ∈ U := by
    change tangentInclusion 1 t 0 ∈ Φ.target
    rw [map_zero]
    exact actualFlattening_target_zero_mem x Φ h0
  let γ : U → ComplexModel (1+t) := fun a => actualFlatteningInverseMap x Φ (tangentInclusion 1 t a)
  let D : Opens (ComplexModel (1+t)) := ⟨originalCentreBaseOpen x Φ (U : Set (ComplexModel 1)),
    isOpen_originalCentreBaseOpen x Φ _ U.isOpen⟩
  have hinc : ContMDiff 𝓘(ℂ,ComplexModel 1) 𝓘(ℂ,ComplexModel (1+t)) ∞
      (fun a : U => tangentInclusion 1 t a) :=
    (tangentInclusion 1 t).contDiff.contMDiff.comp contMDiff_subtype_val
  have hγmd : MDifferentiable 𝓘(ℂ,ComplexModel 1) 𝓘(ℂ,ComplexModel (1+t)) γ := by
    intro a
    change MDifferentiableAt 𝓘(ℂ,ComplexModel 1) 𝓘(ℂ,ComplexModel (1+t))
      (actualFlatteningInverseMap x Φ ∘ (fun a : U => tangentInclusion 1 t a)) a
    exact (actualFlatteningInverseMap_mdifferentiable x Φ hsrc _ a.property).comp a
      (hinc.mdifferentiableAt (x := a) (by simp))
  have hγ : ContMDiff 𝓘(ℂ,ComplexModel 1) 𝓘(ℂ,ComplexModel (1+t)) ∞ γ := by
    intro a
    exact contMDiffAt_of_eventually_mdifferentiableAt (Eventually.of_forall hγmd)
  have hγ0 : γ ⟨0,h0U⟩=x := by
    change actualFlatteningInverseMap x Φ (tangentInclusion 1 t 0)=x
    rw [map_zero,actualFlatteningInverseMap_zero x Φ h0]
  have hleft : ∀ a : U,tangentProjection 1 t (Φ.toFun (chartAt (ComplexModel (1+t)) x (γ a)))=(a : ComplexModel 1) := by
    intro a
    obtain ⟨_,hF⟩ := flatInverse_mem Φ a.property hsrc
    change tangentProjection 1 t (Φ.toFun (chartAt (ComplexModel (1+t)) x
      (actualFlatteningInverseMap x Φ (tangentInclusion 1 t a))))=a
    simp only [actualFlatteningInverseMap]
    rw [hF,tangentProjection_tangentInclusion]
  have hinj : Function.Injective γ := by
    intro a b hab
    apply Subtype.ext
    rw [←hleft a,←hleft b,hab]
  have htrace : C ∩ (D : Set (ComplexModel (1+t)))=Set.range γ := by
    change C ∩ originalCentreBaseOpen x Φ (U : Set (ComplexModel 1))=Set.range γ
    rw [originalCentreBaseOpen_centre_eq_image C x Φ hsrc hflat (U : Set (ComplexModel 1)) (fun a ha => ha)]
    ext y
    constructor
    · rintro ⟨a,ha,hya⟩
      exact ⟨⟨a,ha⟩,hya⟩
    · rintro ⟨a,hya⟩
      exact ⟨a,a.property,hya⟩
  have hxD : x ∈ D := by
    rw [←hγ0]
    exact (htrace.symm ▸ (show γ ⟨0,h0U⟩ ∈ Set.range γ from ⟨_,rfl⟩)).2
  exact ⟨U,h0U,γ,D,hxD,hγ,hγ0,hinj,htrace⟩

private theorem actual_mixed_pullback_comp {n m l : ℕ} {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]
    [ChartedSpace (ComplexModel l) Z] [IsComplexManifold l Z]
    {f : Y → X} {g : Z → Y}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hg : ContMDiff 𝓘(ℂ,ComplexModel l) 𝓘(ℂ,ComplexModel m) ∞ g)
    (A : GermIdeal n X) (hA : A.IsCoherent) :
    GermIdeal.pullback (m := l) (f ∘ g) A=
      GermIdeal.pullback (m := l) g (GermIdeal.pullback (m := m) f A) := by
  apply GermIdeal.ext
  funext z v
  apply propext
  constructor
  · intro hv
    refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.mono ?_
      (GermIdeal.mem_pullback_iff.mp hv))
    rintro u ⟨c,hc,rfl⟩
    have hchol : HolomorphicAt n c (f (g z)) :=
      RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hA hc
    have hfat : ∀ᶠ y in 𝓝 (g z), ContMDiffAt 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f y :=
      Eventually.of_forall fun _ => hf.contMDiffAt
    have hcfhol : HolomorphicAt m (c ∘ f) (g z) := hchol.comp_contMDiff hfat
    have hcf : (GermIdeal.pullback (m := m) f A).mem (g z) (c ∘ f) :=
      GermIdeal.mem_pullback_iff.mpr (InvertibleIdealQuotient.isInSpanAt_self ⟨c,hc,rfl⟩ hcfhol)
    exact ⟨c ∘ f,hcf,rfl⟩
  · intro hv
    refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.trans ?_
      (GermIdeal.mem_pullback_iff.mp hv))
    rintro u ⟨c,hc,rfl⟩
    have hgat : ∀ᶠ y in 𝓝 z,MDifferentiableAt 𝓘(ℂ,ComplexModel l) 𝓘(ℂ,ComplexModel m) g y :=
      Eventually.of_forall fun _ => hg.mdifferentiableAt (by simp)
    refine IsInSpanAt.mono ?_
      (isInSpanAt_comp_eventually_mdifferentiable hgat (GermIdeal.mem_pullback_iff.mp hc))
    rintro u' ⟨σ,⟨a,ha,rfl⟩,rfl⟩
    exact ⟨a,ha,rfl⟩

/-- Actual coherent family, whole projection/shear pullback equality and true
ENTIRE original chart-stalk ideal image, using the same actual family map. -/
theorem actualTranslationFamily_entire_pullback {d n : ℕ} (U : Opens (ComplexModel d))
    (γ : U → ComplexModel n) (hγ : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel n) ∞ γ)
    (A : GermIdeal n (ComplexModel n)) (hA : A.IsCoherent) :
    (GermIdeal.pullback (m := d+n) (actualTranslationFamily U γ) A).IsCoherent ∧
      GermIdeal.pullback (m := d+n) (actualTranslationFamily U γ) A=
        GermIdeal.pullback (m := d+n) (actualTranslationShear U γ hγ)
          (GermIdeal.pullback (m := d+n)
            (fun p : actualParameterProductOpen d n U => blockProjection d n p) A) ∧
      ∀ p : actualParameterProductOpen d n U,
        Ideal.map (actualHolomorphicGermPullback (actualTranslationFamily_contMDiff U γ hγ) p).toRingHom
          (wholeChartStalkIdeal A (actualTranslationFamily U γ p) (actualTranslationFamily U γ p)
            (mem_chart_source _ (actualTranslationFamily U γ p)))=
          wholeChartStalkIdeal (GermIdeal.pullback (m := d+n) (actualTranslationFamily U γ) A)
            p p (mem_chart_source _ p) := by
  have hF := actualTranslationFamily_contMDiff U γ hγ
  refine ⟨GermIdealPullbackCalculus.isCoherent_pullback hF hA,?_,?_⟩
  · rw [actualTranslationFamily_eq_projection_shear U γ hγ]
    exact actual_mixed_pullback_comp
      ((contMDiff_blockProjection d n).comp contMDiff_subtype_val)
      (actualTranslationShear U γ hγ).contMDiff A hA
  · exact map_wholeChartStalkIdeal_actual_pullback hF A hA

/-- ONLY original regular curve geometry and original coherence internally
supply ONE true parameter/window and the ENTIRE actual translation-family ideal. -/
theorem exists_original_regular_curve_entire_translation_family {t : ℕ}
    (C : Set (ComplexModel (1+t))) (x : ComplexModel (1+t))
    (hreg : RegularAtDim (n := 1+t) C x 1)
    (A : GermIdeal (1+t) (ComplexModel (1+t))) (hA : A.IsCoherent) :
    ∃ (U : Opens (ComplexModel 1)) (h0U : (0 : ComplexModel 1) ∈ U)
      (γ : U → ComplexModel (1+t)) (hγ : ContMDiff 𝓘(ℂ,ComplexModel 1) 𝓘(ℂ,ComplexModel (1+t)) ∞ γ)
      (D : Opens (ComplexModel (1+t))),
      x ∈ D ∧ γ ⟨0,h0U⟩=x ∧ Function.Injective γ ∧
      C ∩ (D : Set (ComplexModel (1+t)))=Set.range γ ∧
      (GermIdeal.pullback (m := 1+(1+t)) (actualTranslationFamily U γ) A).IsCoherent ∧
      GermIdeal.pullback (m := 1+(1+t)) (actualTranslationFamily U γ) A=
        GermIdeal.pullback (m := 1+(1+t)) (actualTranslationShear U γ hγ)
          (GermIdeal.pullback (m := 1+(1+t))
            (fun p : actualParameterProductOpen 1 (1+t) U => blockProjection 1 (1+t) p) A) ∧
      ∀ p : actualParameterProductOpen 1 (1+t) U,
        Ideal.map (actualHolomorphicGermPullback (actualTranslationFamily_contMDiff U γ hγ) p).toRingHom
          (wholeChartStalkIdeal A (actualTranslationFamily U γ p) (actualTranslationFamily U γ p)
            (mem_chart_source _ (actualTranslationFamily U γ p)))=
          wholeChartStalkIdeal (GermIdeal.pullback (m := 1+(1+t)) (actualTranslationFamily U γ) A)
            p p (mem_chart_source _ p) := by
  obtain ⟨U,h0U,γ,D,hxD,hγ,hγ0,hinj,htrace⟩ := exists_original_regular_curve_parameter C x hreg
  obtain ⟨hc,hwhole,hstalk⟩ := actualTranslationFamily_entire_pullback U γ hγ A hA
  exact ⟨U,h0U,γ,hγ,D,hxD,hγ0,hinj,htrace,hc,hwhole,hstalk⟩

end
end Hironaka.HironakaOriginalCurveTranslationFamily
