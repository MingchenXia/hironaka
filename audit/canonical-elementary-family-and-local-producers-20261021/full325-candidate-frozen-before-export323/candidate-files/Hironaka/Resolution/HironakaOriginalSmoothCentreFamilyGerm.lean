/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalTranslationFamilyHS

/-! Actual ORIGINAL ambient centre neighborhoods, actual inverse parameters,
and the ENTIRE existing ambient-HS family germ. No higher-history comparison. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaOriginalSmoothCentreFamilyGerm
noncomputable section
open Hironaka.HolomorphicIdealSheaves
  HironakaOriginalTranslationFamilyHS HironakaOriginalCurveTranslationFamily
  HironakaSmoothCentreCoherentDomain HironakaSmoothCentreRealDomainOriginalCentreOpen
  HironakaSmoothCentreNearbyStalks HironakaRelativeNormalIdeal BlowupFlatCoordinates
  HironakaHolomorphicJetChartInvariance

/-- ONLY original regularity internally constructs the true parameter AND its
actual continuous inverse on the SAME ORIGINAL ambient open, in every dimension. -/
theorem exists_original_regular_centre_parameter_retraction {d t : ℕ}
    (C : Set (ComplexModel (d+t))) (x : ComplexModel (d+t))
    (hreg : RegularAtDim (n := d+t) C x d) :
    ∃ (U : Opens (ComplexModel d)) (h0U : (0 : ComplexModel d) ∈ U)
      (D : Opens (ComplexModel (d+t))) (γ : U → D) (ρ : D → U),
      x ∈ D ∧ ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel (d+t)) ∞ (fun a => (γ a : ComplexModel (d+t))) ∧
      (γ ⟨0,h0U⟩ : ComplexModel (d+t))=x ∧ Function.Injective (fun a => (γ a : ComplexModel (d+t))) ∧
      (∀ a,(γ a : ComplexModel (d+t)) ∈ C) ∧ Continuous ρ ∧
      (∀ a,ρ (γ a)=a) ∧ (∀ p : D,(p : ComplexModel (d+t)) ∈ C → γ (ρ p)=p) ∧
      C ∩ (D : Set (ComplexModel (d+t)))=Set.range (fun a => (γ a : ComplexModel (d+t))) := by
  obtain ⟨_,_,Φ,hsrc,h0,hflat⟩ := hreg
  let U : Opens (ComplexModel d) := ⟨(tangentInclusion d t) ⁻¹' Φ.target,
    Φ.isOpen_target.preimage (tangentInclusion d t).continuous⟩
  have h0U : (0 : ComplexModel d) ∈ U := by
    change tangentInclusion d t 0 ∈ Φ.target
    rw [map_zero]
    exact actualFlattening_target_zero_mem x Φ h0
  let g : U → ComplexModel (d+t) := fun a => actualFlatteningInverseMap x Φ (tangentInclusion d t a)
  let D : Opens (ComplexModel (d+t)) := ⟨originalCentreBaseOpen x Φ (U : Set (ComplexModel d)),
    isOpen_originalCentreBaseOpen x Φ _ U.isOpen⟩
  have hinc : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel (d+t)) ∞
      (fun a : U => tangentInclusion d t a) :=
    (tangentInclusion d t).contDiff.contMDiff.comp contMDiff_subtype_val
  have hgmd : MDifferentiable 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel (d+t)) g := by
    intro a
    change MDifferentiableAt 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel (d+t))
      (actualFlatteningInverseMap x Φ ∘ (fun a : U => tangentInclusion d t a)) a
    exact (actualFlatteningInverseMap_mdifferentiable x Φ hsrc _ a.property).comp a
      (hinc.mdifferentiableAt (x := a) (by simp))
  have hg : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel (d+t)) ∞ g := by
    intro a
    exact contMDiffAt_of_eventually_mdifferentiableAt (Eventually.of_forall hgmd)
  have hg0 : g ⟨0,h0U⟩=x := by
    change actualFlatteningInverseMap x Φ (tangentInclusion d t 0)=x
    rw [map_zero,actualFlatteningInverseMap_zero x Φ h0]
  have htrace : C ∩ (D : Set (ComplexModel (d+t)))=Set.range g := by
    change C ∩ originalCentreBaseOpen x Φ (U : Set (ComplexModel d))=Set.range g
    rw [originalCentreBaseOpen_centre_eq_image C x Φ hsrc hflat (U : Set (ComplexModel d)) (fun a ha => ha)]
    ext y
    exact ⟨fun ⟨a,ha,hya⟩ => ⟨⟨a,ha⟩,hya⟩,fun ⟨a,hya⟩ => ⟨a,a.property,hya⟩⟩
  have hgC : ∀ a,g a ∈ C ∩ (D : Set (ComplexModel (d+t))) :=
    fun a => htrace.symm ▸ (show g a ∈ Set.range g from ⟨a,rfl⟩)
  let γ : U → D := fun a => ⟨g a,(hgC a).2⟩
  let ρ : D → U := fun p => ⟨tangentProjection d t (Φ.toFun (chartAt (ComplexModel (d+t)) x p)),p.property.2⟩
  have hρraw : Continuous (fun p : D => tangentProjection d t (Φ.toFun (chartAt (ComplexModel (d+t)) x p))) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hφ : ContinuousAt Φ.toFun (chartAt (ComplexModel (d+t)) x (p : ComplexModel (d+t))) :=
      (Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds p.property.1.2)).continuousAt
    have he : ContinuousAt (chartAt (ComplexModel (d+t)) x : ComplexModel (d+t) → ComplexModel (d+t)) (p : ComplexModel (d+t)) :=
      (chartAt (ComplexModel (d+t)) x).continuousAt p.property.1.1
    have hF : ContinuousAt (fun y : ComplexModel (d+t) => Φ.toFun (chartAt (ComplexModel (d+t)) x y)) (p : ComplexModel (d+t)) :=
      ContinuousAt.comp (g := Φ.toFun) (f := (chartAt (ComplexModel (d+t)) x : ComplexModel (d+t) → ComplexModel (d+t))) hφ he
    exact ((tangentProjection d t).continuous.continuousAt.comp hF).comp continuous_subtype_val.continuousAt
  have hρ : Continuous ρ := hρraw.subtype_mk _
  have hleft : ∀ a,ρ (γ a)=a := by
    intro a
    apply Subtype.ext
    obtain ⟨_,hF⟩ := flatInverse_mem Φ a.property hsrc
    change tangentProjection d t (Φ.toFun (chartAt (ComplexModel (d+t)) x
      (actualFlatteningInverseMap x Φ (tangentInclusion d t a))))=a
    simp only [actualFlatteningInverseMap]
    rw [hF,tangentProjection_tangentInclusion]
  have hright : ∀ p : D,(p : ComplexModel (d+t)) ∈ C → γ (ρ p)=p := by
    intro p hp
    apply Subtype.ext
    change actualFlatteningInverseMap x Φ
      (tangentInclusion d t (tangentProjection d t (Φ.toFun (chartAt (ComplexModel (d+t)) x p))))=p
    have hplane : Φ.toFun (chartAt (ComplexModel (d+t)) x (p : ComplexModel (d+t))) ∈ complexCoordinatePlane (d+t) d :=
      (hflat p.property.1.1 p.property.1.2).mp hp
    exact (congrArg (actualFlatteningInverseMap x Φ)
      (tangentInclusion_projection_eq_of_mem_plane d t hplane)).trans (flatInverse_flat Φ p.property.1)
  have hinj : Function.Injective (fun a => (γ a : ComplexModel (d+t))) := by
    intro a b hab
    have hs : γ a=γ b := Subtype.ext hab
    have h := congrArg ρ hs
    simpa only [hleft] using h
  exact ⟨U,h0U,D,γ,ρ,by rw [←hg0]; exact (hgC _).2,hg,hg0,hinj,
    fun a => (hgC a).1,hρ,hleft,hright,htrace⟩

/-- Genuine real neighbourhood transport uses explicit actual maps/inverse
laws, not a supplied localconst certificate. The original consumer supplies
all these actual geometric data internally from original regularity. -/
theorem actual_original_centre_parameter_localConst_iff
    {M P Λ : Type*} [TopologicalSpace M] [TopologicalSpace P]
    (D : Opens M) (γ : P → D) (ρ : D → P)
    (hγ : Continuous (fun a => (γ a : M))) (hρ : Continuous ρ)
    (C : Set M) (hγC : ∀ a,(γ a : M) ∈ C)
    (hleft : ∀ a,ρ (γ a)=a) (hright : ∀ p : D,(p : M) ∈ C → γ (ρ p)=p)
    (f : M → Λ) (a : P) :
    (∃ W : Set M,IsOpen W ∧ (γ a : M) ∈ W ∧ ∀ y ∈ C ∩ W,f y=f (γ a)) ↔
      ∃ V : Set P,IsOpen V ∧ a ∈ V ∧ ∀ b ∈ V,f (γ b)=f (γ a) := by
  constructor
  · rintro ⟨W,hWo,haW,hvalue⟩
    refine ⟨(fun b => (γ b : M)) ⁻¹' W,hWo.preimage hγ,haW,?_⟩
    intro b hb
    exact hvalue (γ b) ⟨hγC b,hb⟩
  · rintro ⟨V,hVo,haV,hvalue⟩
    let W : Set M := Subtype.val '' (ρ ⁻¹' V)
    have hWo : IsOpen W := D.isOpen.isOpenMap_subtype_val _ (hVo.preimage hρ)
    have haW : (γ a : M) ∈ W := by
      refine ⟨γ a,?_,rfl⟩
      change ρ (γ a) ∈ V
      rw [hleft]
      exact haV
    refine ⟨W,hWo,haW,?_⟩
    intro y hy
    obtain ⟨p,hp,hpy⟩ := hy.2
    have hpC : (p : M) ∈ C := hpy.symm ▸ hy.1
    have hpEq : (γ (ρ p) : M)=y := (congrArg Subtype.val (hright p hpC)).trans hpy
    simpa only [hpEq] using hvalue (ρ p) hp

/-- ONLY ORIGINAL regular centre geometry and ORIGINAL coherence produce the
true ORIGINAL AMBIENT C-neighborhood versus ENTIRE family-zero-section HS germ,
for EVERY actual parameter and every centre dimension, including zero. -/
theorem exists_original_regular_centre_entire_hs_family_germ {d t : ℕ}
    (C : Set (ComplexModel (d+t))) (x : ComplexModel (d+t)) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) (ComplexModel (d+t))) (hA : A.IsCoherent) :
    ∃ (U : Opens (ComplexModel d)) (h0U : (0 : ComplexModel d) ∈ U)
      (D : Opens (ComplexModel (d+t))) (γ : U → D),
      x ∈ D ∧ ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel (d+t)) ∞ (fun a => (γ a : ComplexModel (d+t))) ∧
      (γ ⟨0,h0U⟩ : ComplexModel (d+t))=x ∧ Function.Injective (fun a => (γ a : ComplexModel (d+t))) ∧
      C ∩ (D : Set (ComplexModel (d+t)))=Set.range (fun a => (γ a : ComplexModel (d+t))) ∧
      ∀ a : U,
        (∃ W : Set (ComplexModel (d+t)),IsOpen W ∧ (γ a : ComplexModel (d+t)) ∈ W ∧
          ∀ y ∈ C ∩ W,∀ ℓ,hilbertSamuelAt A y ℓ=hilbertSamuelAt A (γ a) ℓ) ↔
        ∃ V : Set (actualParameterProductOpen d (d+t) U),IsOpen V ∧ actualTranslationZeroSection U a ∈ V ∧
          ∀ p ∈ actualTranslationZeroTrace U ∩ V,∀ ℓ,
            hilbertSamuelAt (GermIdeal.pullback (m := d+(d+t))
              (actualTranslationFamily U (fun a => (γ a : ComplexModel (d+t)))) A) p ℓ=
            hilbertSamuelAt (GermIdeal.pullback (m := d+(d+t))
              (actualTranslationFamily U (fun a => (γ a : ComplexModel (d+t)))) A) (actualTranslationZeroSection U a) ℓ := by
  obtain ⟨U,h0U,D,γ,ρ,hxD,hγ,hγ0,hinj,hγC,hρ,hleft,hright,htrace⟩ :=
    exists_original_regular_centre_parameter_retraction C x hreg
  refine ⟨U,h0U,D,γ,hxD,hγ,hγ0,hinj,htrace,?_⟩
  intro a
  have hparam := actual_original_centre_parameter_localConst_iff D γ ρ hγ.continuous hρ C hγC hleft hright
    (fun y ℓ => hilbertSamuelAt A y ℓ) a
  have hparam' :
      (∃ W : Set (ComplexModel (d+t)),IsOpen W ∧ (γ a : ComplexModel (d+t)) ∈ W ∧
        ∀ y ∈ C ∩ W,∀ ℓ,hilbertSamuelAt A y ℓ=hilbertSamuelAt A (γ a) ℓ) ↔
      ∃ V : Set U,IsOpen V ∧ a ∈ V ∧ ∀ b ∈ V,∀ ℓ,hilbertSamuelAt A (γ b) ℓ=hilbertSamuelAt A (γ a) ℓ := by
    constructor
    · rintro ⟨W,hW,haW,hvalue⟩
      obtain ⟨V,hV,haV,hv⟩ := hparam.mp ⟨W,hW,haW,fun y hy => funext (hvalue y hy)⟩
      exact ⟨V,hV,haV,fun b hb ℓ => congrFun (hv b hb) ℓ⟩
    · rintro ⟨V,hV,haV,hvalue⟩
      obtain ⟨W,hW,haW,hw⟩ := hparam.mpr ⟨V,hV,haV,fun b hb => funext (hvalue b hb)⟩
      exact ⟨W,hW,haW,fun y hy ℓ => congrFun (hw y hy) ℓ⟩
  exact hparam'.trans (actualTranslationZeroTrace_hs_localConst_iff U (fun a => (γ a : ComplexModel (d+t))) hγ A hA a).symm

end
end Hironaka.HironakaOriginalSmoothCentreFamilyGerm
