/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalSmoothSubmersionIntrinsicHS

/-! Genuine ORIGINAL holomorphic sections and BOTH actual ambient
neighborhood directions for ANY carrier and the ENTIRE original HS. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalSubmersionHSNeighborhoods
noncomputable section
open Hironaka.HolomorphicIdealSheaves BlowupFlatCoordinates
  HironakaOriginalSmoothSubmersionIntrinsicHS HironakaSmoothSubmersionAdaptedProductCoordinates
  HironakaHolomorphicJetChartInvariance

/-- ONLY original submersion geometry constructs a genuine local holomorphic
section through the chosen ORIGINAL source point, including zero dimensions. -/
theorem exists_original_submersion_local_holomorphic_section {n r : ℕ} {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [ChartedSpace (ComplexModel (n+r)) Y] [IsComplexManifold (n+r) Y]
    {f : Y → X} (y : Y)
    (hsub : Manifold.IsSubmersionAt 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel n) ∞ f y) :
    ∃ (D : Opens X) (hfyD : f y ∈ D) (σ : D → Y),
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (n+r)) ∞ σ ∧
      σ ⟨f y,hfyD⟩=y ∧ ∀ x : D,f (σ x)=(x : X) := by
  obtain ⟨_,_,Φ,hsrcΦ,h0Φ,_⟩ := AnalyticIrreducibleComponents.regularAtDim_univ (n := n) (f y)
  change Φ.toFun (chartAt (ComplexModel n) (f y) (f y))=0 at h0Φ
  obtain ⟨R,S,Ψ,hR0,hS0,hSΦ,hsrcΨ,h0Ψ,hTarget,_hΨ,hd⟩ :=
    HironakaSmoothSubmersionAdaptedProductCoordinates.exists_adapted_product_coordinates
      (n := n) (r := r) (X := X) (Y := Y) (f := f) (y := y) hsub Φ h0Φ
  have hΦS : Φ.toFun (chartAt (ComplexModel n) (f y) (f y)) ∈ S := by
    rw [h0Φ]
    exact hS0
  let Θ := restrictTarget Φ S hSΦ hΦS
  have hsrcΘ : Θ.source ⊆ (chartAt (ComplexModel n) (f y)).target := fun _ hz => hsrcΦ hz.1
  let D : Opens X := ⟨flatDomain Θ,isOpen_flatDomain Θ⟩
  let O : Opens Y := ⟨flatDomain Ψ,isOpen_flatDomain Ψ⟩
  let e := actualFlatLinearDiffeomorph Θ hsrcΘ (ContinuousLinearEquiv.refl ℂ (ComplexModel n))
  let χ := actualFlatLinearDiffeomorph Ψ hsrcΨ (ContinuousLinearEquiv.refl ℂ (ComplexModel (n+r)))
  let V := actualFlatLinearTarget Ψ (ContinuousLinearEquiv.refl ℂ (ComplexModel (n+r)))
  let ι : D → V := fun p => ⟨(fibreFirstSplit n r).symm (0,(e p : ComplexModel n)),by
    change (fibreFirstSplit n r).symm (0,(e p : ComplexModel n)) ∈ Ψ.target
    rw [hTarget]
    change fibreFirstSplit n r ((fibreFirstSplit n r).symm (0,(e p : ComplexModel n))) ∈
      (R : Set (ComplexModel r)) ×ˢ (S : Set (ComplexModel n))
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact ⟨hR0,(e p).property⟩⟩
  have hι : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (n+r)) ∞ ι := by
    apply (ContMDiff.subtypeVal_comp_iff V _).mp
    exact (fibreFirstSplit n r).symm.contDiff.contMDiff.comp
      (contMDiff_const.prodMk_space (contMDiff_subtype_val.comp e.contMDiff))
  let σ : D → Y := fun p => (χ.symm (ι p) : Y)
  have hσ : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (n+r)) ∞ σ :=
    contMDiff_subtype_val.comp (χ.symm.contMDiff.comp hι)
  have hσO : ∀ p,σ p ∈ flatDomain Ψ := fun p => (χ.symm (ι p)).property
  have hsection : ∀ p : D,f (σ p)=(p : X) := by
    intro p
    have hc := congrArg Subtype.val (χ.apply_symm_apply (ι p))
    change Ψ.toFun (chartAt (ComplexModel (n+r)) y (σ p))=
      (fibreFirstSplit n r).symm (0,(e p : ComplexModel n)) at hc
    have hcoord := (hd (σ p) (hσO p)).2
    rw [hc] at hcoord
    change (fibreFirstSplit n r ((fibreFirstSplit n r).symm (0,(e p : ComplexModel n)))).2=_ at hcoord
    rw [ContinuousLinearEquiv.apply_symm_apply] at hcoord
    have hpΦ : (p : X) ∈ flatDomain Φ := ⟨p.property.1,p.property.2.1⟩
    have hEq : Φ.toFun (chartAt (ComplexModel n) (f y) (f (σ p)))=
        Φ.toFun (chartAt (ComplexModel n) (f y) (p : X)) := hcoord.symm
    calc
      f (σ p)=(chartAt (ComplexModel n) (f y)).symm
        (Φ.invFun (Φ.toFun (chartAt (ComplexModel n) (f y) (f (σ p))))) :=
          (flatInverse_flat Φ (hd (σ p) (hσO p)).1).symm
      _=(chartAt (ComplexModel n) (f y)).symm
        (Φ.invFun (Φ.toFun (chartAt (ComplexModel n) (f y) (p : X)))) := by rw [hEq]
      _=(p : X) := flatInverse_flat Φ hpΦ
  have hfyD : f y ∈ D := ⟨mem_chart_source _ _,Θ.center_mem_source⟩
  let p0 : D := ⟨f y,hfyD⟩
  let q0 : O := ⟨y,mem_chart_source _ _,Ψ.center_mem_source⟩
  have he0 : (e p0 : ComplexModel n)=0 := h0Φ
  have hχ0 : (χ q0 : ComplexModel (n+r))=0 := h0Ψ
  have hi0 : ι p0=χ q0 := by
    apply Subtype.ext
    change (fibreFirstSplit n r).symm (0,(e p0 : ComplexModel n))=(χ q0 : ComplexModel (n+r))
    rw [he0,hχ0]
    exact map_zero _
  have hσ0 : σ p0=y := by
    change (χ.symm (ι p0) : Y)=y
    rw [hi0,χ.symm_apply_apply]
  exact ⟨D,hfyD,σ,hσ,hσ0,hsection⟩

/-- ANY function and ANY actual carrier have BOTH original ambient
neighborhood directions, via an internally produced true section. -/
theorem original_submersion_carrier_function_localConst_iff {n r : ℕ} {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [ChartedSpace (ComplexModel (n+r)) Y] [IsComplexManifold (n+r) Y]
    {f : Y → X} (hf : ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel n) ∞ f)
    (y : Y) (hsub : Manifold.IsSubmersionAt 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel n) ∞ f y)
    {Λ : Type*} (g : X → Λ) (S : Set X) :
    (∃ W : Set X,IsOpen W ∧ f y ∈ W ∧ ∀ x ∈ S ∩ W,g x=g (f y)) ↔
      ∃ V : Set Y,IsOpen V ∧ y ∈ V ∧ ∀ z ∈ (f ⁻¹' S) ∩ V,g (f z)=g (f y) := by
  constructor
  · rintro ⟨W,hWo,hyW,hvalue⟩
    exact ⟨f ⁻¹' W,hWo.preimage hf.continuous,hyW,fun z hz => hvalue (f z) hz⟩
  · rintro ⟨V,hVo,hyV,hvalue⟩
    obtain ⟨D,hfyD,σ,hσ,hσ0,hsection⟩ :=
      exists_original_submersion_local_holomorphic_section y hsub
    let W : Set X := Subtype.val '' (σ ⁻¹' V)
    have hWo : IsOpen W := D.isOpen.isOpenMap_subtype_val _ (hVo.preimage hσ.continuous)
    have hfyW : f y ∈ W := by
      refine ⟨⟨f y,hfyD⟩,?_,rfl⟩
      change σ ⟨f y,hfyD⟩ ∈ V
      rw [hσ0]
      exact hyV
    refine ⟨W,hWo,hfyW,?_⟩
    intro x hx
    obtain ⟨p,hp,hpx⟩ := hx.2
    have hpS : f (σ p) ∈ S := by
      rw [hsection,hpx]
      exact hx.1
    have hh := hvalue (σ p) ⟨hpS,hp⟩
    simpa only [hsection,hpx] using hh

/-- Literal ENTIRE original ambient-HS neighborhood constancy on an actual carrier. -/
def actualEntireHSLocallyConstantAlong {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (A : GermIdeal n M) (S : Set M) (x : M) : Prop :=
  ∃ W : Set M,IsOpen W ∧ x ∈ W ∧ ∀ y ∈ S ∩ W,∀ ℓ,hilbertSamuelAt A y ℓ=hilbertSamuelAt A x ℓ

/-- The literal original ambient-HS neighborhood variation set, without an
assumed analytic structure or chosen local presentation. -/
def actualEntireHSNeighborhoodVariation {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (A : GermIdeal n M) (S : Set M) : Set M :=
  {x | ¬actualEntireHSLocallyConstantAlong A S x}

/-- ONLY the genuine original submersion and original coherence transport
ENTIRE existing ambient HS neighborhoods on ANY actual carrier BOTH ways. -/
theorem original_submersion_entire_hs_carrier_localConst_iff {n r : ℕ} {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [ChartedSpace (ComplexModel (n+r)) Y] [IsComplexManifold (n+r) Y]
    {f : Y → X} (hsub : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel n) ∞ f)
    (A : GermIdeal n X) (hA : A.IsCoherent) (S : Set X) (y : Y) :
    actualEntireHSLocallyConstantAlong A S (f y) ↔
      actualEntireHSLocallyConstantAlong (GermIdeal.pullback (m := n+r) f A) (f ⁻¹' S) y := by
  have hG := original_submersion_carrier_function_localConst_iff hsub.contMDiff y (hsub.isSubmersionAt y)
    (fun x ℓ => hilbertSamuelAt A x ℓ) S
  constructor
  · rintro ⟨W,hWo,hyW,hvalue⟩
    obtain ⟨V,hVo,hyV,hv⟩ := hG.mp ⟨W,hWo,hyW,fun x hx => funext (hvalue x hx)⟩
    refine ⟨V,hVo,hyV,?_⟩
    intro z hz
    exact (hilbertSamuelAt_original_submersion_entire_profile_eq_iff hsub A hA z y).mpr
      (fun ℓ => congrFun (hv z hz) ℓ)
  · rintro ⟨V,hVo,hyV,hvalue⟩
    obtain ⟨W,hWo,hyW,hw⟩ := hG.mpr ⟨V,hVo,hyV,fun z hz => funext
      ((hilbertSamuelAt_original_submersion_entire_profile_eq_iff hsub A hA z y).mp (hvalue z hz))⟩
    exact ⟨W,hWo,hyW,fun x hx ℓ => congrFun (hw x hx) ℓ⟩

/-- EXACT literal whole-profile neighborhood-variation preimage equality;
no generic bad-locus analyticity or blowup stability is inferred. -/
theorem original_submersion_entire_hs_neighborhood_variation_eq_preimage {n r : ℕ} {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [ChartedSpace (ComplexModel (n+r)) Y] [IsComplexManifold (n+r) Y]
    {f : Y → X} (hsub : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel n) ∞ f)
    (A : GermIdeal n X) (hA : A.IsCoherent) (S : Set X) :
    actualEntireHSNeighborhoodVariation (GermIdeal.pullback (m := n+r) f A) (f ⁻¹' S)=
      f ⁻¹' actualEntireHSNeighborhoodVariation A S := by
  ext y
  exact (not_congr (original_submersion_entire_hs_carrier_localConst_iff hsub A hA S y)).symm

end
end Hironaka.HironakaOriginalSubmersionHSNeighborhoods
