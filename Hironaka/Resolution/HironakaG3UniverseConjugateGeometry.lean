import Hironaka.Resolution.HironakaG3UniverseDiffeoDerivative
import Hironaka.Resolution.HironakaG3UniverseComplexTransport
import Mathlib.Geometry.Manifold.Diffeomorph
set_option autoImplicit false
open Function
open scoped Manifold ContDiff
universe u v
namespace Hironaka.HironakaG3UniverseDiffeoDerivative
noncomputable section


/-- A holomorphic map and its conjugate have the same criticality. -/
theorem conjugate_mfderiv_bijective_iff {n : ℕ} {X : Type u} {Y : Type u}
    {X₀ : Type v} {Y₀ : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X₀] [TopologicalSpace Y₀]
    [ChartedSpace (ComplexModel n) X] [ChartedSpace (ComplexModel n) Y]
    [ChartedSpace (ComplexModel n) X₀] [ChartedSpace (ComplexModel n) Y₀]
    [IsComplexManifold n X] [IsComplexManifold n Y]
    [IsComplexManifold n X₀] [IsComplexManifold n Y₀]
    (e : Y₀ ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ Y)
    (f : X₀ ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ X)
    (P : Y₀ → X₀) (hP : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ P)
    (y : Y) :
    Bijective (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (f ∘ P ∘ e.symm) y) ↔
      Bijective (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) P (e.symm y)) := by
  have hd : mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (f ∘ P ∘ e.symm) y =
      (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) f (P (e.symm y))).comp
        ((mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) P (e.symm y)).comp
          (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) e.symm y)) := by
    rw [mfderiv_comp y (f.contMDiff.mdifferentiableAt (by simp))
      ((hP.comp e.symm.contMDiff).mdifferentiableAt (by simp)),
      mfderiv_comp y (hP.mdifferentiableAt (by simp)) (e.symm.contMDiff.mdifferentiableAt (by simp))]
    rfl
  rw [hd]
  simp only [ContinuousLinearMap.coe_comp]
  rw [(diffeo_mfderiv_bijective f _).of_comp_iff',
    Function.Bijective.of_comp_iff _ (diffeo_mfderiv_bijective e.symm y)]


/-- Conjugation identifies the literal exceptional loci across universes. -/
theorem conjugate_exceptionalLocus {n : ℕ} {X : Type u} {Y : Type u}
    {X₀ : Type v} {Y₀ : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X₀] [TopologicalSpace Y₀]
    [ChartedSpace (ComplexModel n) X] [ChartedSpace (ComplexModel n) Y]
    [ChartedSpace (ComplexModel n) X₀] [ChartedSpace (ComplexModel n) Y₀]
    [IsComplexManifold n X] [IsComplexManifold n Y]
    [IsComplexManifold n X₀] [IsComplexManifold n Y₀]
    (e : Y₀ ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ Y)
    (f : X₀ ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ X)
    (P : Y₀ → X₀) (hP : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ P) :
    Hironaka.BlowupSequences.exceptionalLocus n (f ∘ P ∘ e.symm) =
      e.symm ⁻¹' Hironaka.BlowupSequences.exceptionalLocus n P := by
  ext y
  change (¬ Bijective (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (f ∘ P ∘ e.symm) y)) ↔
    ¬ Bijective (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) P (e.symm y))
  exact not_congr (conjugate_mfderiv_bijective_iff e f P hP y)

/-- The geometric strict transform is the literal pullback of the original. -/
theorem conjugate_strictTransform {n : ℕ} {X : Type u} {Y : Type u}
    {X₀ : Type v} {Y₀ : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X₀] [TopologicalSpace Y₀]
    [ChartedSpace (ComplexModel n) X] [ChartedSpace (ComplexModel n) Y]
    [ChartedSpace (ComplexModel n) X₀] [ChartedSpace (ComplexModel n) Y₀]
    [IsComplexManifold n X] [IsComplexManifold n Y]
    [IsComplexManifold n X₀] [IsComplexManifold n Y₀]
    (e : Y₀ ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ Y)
    (f : X₀ ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ X)
    (P : Y₀ → X₀) (hP : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ P)
    (A : Set X₀) :
    Hironaka.BlowupSequences.strictTransform n (f ∘ P ∘ e.symm) (f.symm ⁻¹' A) =
      e.symm ⁻¹' Hironaka.BlowupSequences.strictTransform n P A := by
  unfold Hironaka.BlowupSequences.strictTransform
  rw [conjugate_exceptionalLocus e f P hP]
  have hcl := e.symm.toHomeomorph.preimage_closure (P ⁻¹' A \ Hironaka.BlowupSequences.exceptionalLocus n P)
  simp only [Diffeomorph.coe_toHomeomorph] at hcl
  rw [hcl]
  congr 1
  ext y
  simp only [Set.mem_sdiff,Set.mem_preimage,Function.comp_apply, f.symm_apply_apply]


/-- Holomorphicity, properness and surjectivity survive conjugation. -/
theorem conjugate_map_properties {n : ℕ} {X : Type u} {Y : Type u}
    {X₀ : Type v} {Y₀ : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X₀] [TopologicalSpace Y₀]
    [ChartedSpace (ComplexModel n) X] [ChartedSpace (ComplexModel n) Y]
    [ChartedSpace (ComplexModel n) X₀] [ChartedSpace (ComplexModel n) Y₀]
    [IsComplexManifold n X] [IsComplexManifold n Y]
    [IsComplexManifold n X₀] [IsComplexManifold n Y₀]
    (e : Y₀ ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ Y)
    (f : X₀ ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ X)
    (P : Y₀ → X₀) (hP : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ P)
    (hProper : IsProperMap P) (hSurj : Surjective P) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (f ∘ P ∘ e.symm) ∧
      IsProperMap (f ∘ P ∘ e.symm) ∧ Surjective (f ∘ P ∘ e.symm) := by
  exact ⟨f.contMDiff.comp (hP.comp e.symm.contMDiff),
    f.toHomeomorph.isProperMap.comp (hProper.comp e.symm.toHomeomorph.isProperMap),
    f.surjective.comp (hSurj.comp e.symm.surjective)⟩

/-- An exact inherited-plus-exceptional boundary support transports literally. -/
theorem conjugate_boundary_support {n : ℕ} {X : Type u} {Y : Type u}
    {X₀ : Type v} {Y₀ : Type v} {ι κ : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X₀] [TopologicalSpace Y₀]
    [ChartedSpace (ComplexModel n) X] [ChartedSpace (ComplexModel n) Y]
    [ChartedSpace (ComplexModel n) X₀] [ChartedSpace (ComplexModel n) Y₀]
    [IsComplexManifold n X] [IsComplexManifold n Y]
    [IsComplexManifold n X₀] [IsComplexManifold n Y₀]
    (e : Y₀ ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ Y)
    (f : X₀ ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ X)
    (P : Y₀ → X₀) (hP : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ P)
    (D : κ → Set X₀) (B : ι → Set Y₀)
    (hSupport : (⋃ j, B j) = P ⁻¹' (⋃ i, D i) ∪ Hironaka.BlowupSequences.exceptionalLocus n P) :
    (⋃ j, e.symm ⁻¹' B j) = (f ∘ P ∘ e.symm) ⁻¹' (f.symm ⁻¹' (⋃ i, D i)) ∪
      Hironaka.BlowupSequences.exceptionalLocus n (f ∘ P ∘ e.symm) := by
  rw [conjugate_exceptionalLocus e f P hP]
  ext y
  have hh := Set.ext_iff.mp hSupport (e.symm y)
  simpa only [Set.mem_iUnion, Set.mem_preimage, Set.mem_union, Function.comp_apply,
    f.symm_apply_apply] using hh


/-- Nonerasure of the geometric strict transform transports under conjugation. -/
theorem conjugate_non_erasure {n : ℕ} {X : Type u} {Y : Type u}
    {X₀ : Type v} {Y₀ : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X₀] [TopologicalSpace Y₀]
    [ChartedSpace (ComplexModel n) X] [ChartedSpace (ComplexModel n) Y]
    [ChartedSpace (ComplexModel n) X₀] [ChartedSpace (ComplexModel n) Y₀]
    [IsComplexManifold n X] [IsComplexManifold n Y]
    [IsComplexManifold n X₀] [IsComplexManifold n Y₀]
    (e : Y₀ ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ Y)
    (f : X₀ ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ X)
    (P : Y₀ → X₀) (hP : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ P)
    (A : Set X₀)
    (hImage : P '' Hironaka.BlowupSequences.strictTransform n P A = A) :
    (f ∘ P ∘ e.symm) '' Hironaka.BlowupSequences.strictTransform n (f ∘ P ∘ e.symm) (f.symm ⁻¹' A) =
      f.symm ⁻¹' A := by
  rw [conjugate_strictTransform e f P hP]
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    change f.symm (f (P (e.symm y))) ∈ A
    rw [f.symm_apply_apply, ← hImage]
    exact ⟨e.symm y,hy,rfl⟩
  · intro hx
    change f.symm x ∈ A at hx
    rw [← hImage] at hx
    obtain ⟨z,hz,hzP⟩ := hx
    refine ⟨e z,?_,?_⟩
    · simpa using hz
    · change f (P (e.symm (e z))) = x
      rw [e.symm_apply_apply,hzP,f.apply_symm_apply]


/-- Isomorphism over a specified locus transports under conjugation. -/
theorem conjugate_isomorphismOver {n : ℕ} {X : Type u} {Y : Type u}
    {X₀ : Type v} {Y₀ : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X₀] [TopologicalSpace Y₀]
    [ChartedSpace (ComplexModel n) X] [ChartedSpace (ComplexModel n) Y]
    [ChartedSpace (ComplexModel n) X₀] [ChartedSpace (ComplexModel n) Y₀]
    [IsComplexManifold n X] [IsComplexManifold n Y]
    [IsComplexManifold n X₀] [IsComplexManifold n Y₀]
    (e : Y₀ ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ Y)
    (f : X₀ ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ X)
    (P : Y₀ → X₀) (hP : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ P)
    (S : Set X₀) (hIso : Hironaka.BlowupSequences.IsIsomorphismOver n P S) :
    Hironaka.BlowupSequences.IsIsomorphismOver n (f ∘ P ∘ e.symm) (f.symm ⁻¹' S) := by
  obtain ⟨⟨_,hinj,hsurj⟩,hdisj⟩ := hIso
  have hgPre : (f ∘ P ∘ e.symm) ⁻¹' (f.symm ⁻¹' S) = e.symm ⁻¹' (P ⁻¹' S) := by
    ext y
    simp only [Set.mem_preimage,Function.comp_apply,f.symm_apply_apply]
  unfold Hironaka.BlowupSequences.IsIsomorphismOver
  rw [hgPre,conjugate_exceptionalLocus e f P hP]
  refine ⟨⟨?_,?_,?_⟩,?_⟩
  · intro y hy
    change f.symm (f (P (e.symm y))) ∈ S
    simpa using hy
  · intro a ha b hb hab
    apply e.symm.injective
    apply hinj ha hb
    exact f.injective hab
  · intro x hx
    obtain ⟨z,hz,hzP⟩ := hsurj hx
    refine ⟨e z,?_,?_⟩
    · simpa using hz
    · change f (P (e.symm (e z))) = x
      rw [e.symm_apply_apply,hzP,f.apply_symm_apply]
  · exact Set.disjoint_left.mpr (fun y hy hz => Set.disjoint_left.mp hdisj hy hz)


/-- Any exact inverse-image boundary support transports under conjugation. -/
theorem conjugate_preimage_support {n : ℕ} {X : Type u} {Y : Type u}
    {X₀ : Type v} {Y₀ : Type v} {ι : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X₀] [TopologicalSpace Y₀]
    [ChartedSpace (ComplexModel n) X] [ChartedSpace (ComplexModel n) Y]
    [ChartedSpace (ComplexModel n) X₀] [ChartedSpace (ComplexModel n) Y₀]
    [IsComplexManifold n X] [IsComplexManifold n Y]
    [IsComplexManifold n X₀] [IsComplexManifold n Y₀]
    (e : Y₀ ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ Y)
    (f : X₀ ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ X)
    (P : Y₀ → X₀) (B : ι → Set Y₀) (R : Set X₀)
    (hSupport : (⋃ j, B j) = P ⁻¹' R) :
    (⋃ j, e.symm ⁻¹' B j) = (f ∘ P ∘ e.symm) ⁻¹' (f.symm ⁻¹' R) := by
  ext y
  have hh := Set.ext_iff.mp hSupport (e.symm y)
  simpa only [Set.mem_iUnion, Set.mem_preimage, Function.comp_apply,
    f.symm_apply_apply] using hh

/-- Containment of an inverse image in the exceptional locus is preserved. -/
theorem conjugate_preimage_exceptional {n : ℕ} {X : Type u} {Y : Type u}
    {X₀ : Type v} {Y₀ : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X₀] [TopologicalSpace Y₀]
    [ChartedSpace (ComplexModel n) X] [ChartedSpace (ComplexModel n) Y]
    [ChartedSpace (ComplexModel n) X₀] [ChartedSpace (ComplexModel n) Y₀]
    [IsComplexManifold n X] [IsComplexManifold n Y]
    [IsComplexManifold n X₀] [IsComplexManifold n Y₀]
    (e : Y₀ ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ Y)
    (f : X₀ ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ X)
    (P : Y₀ → X₀) (hP : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ P)
    (R : Set X₀) (hExc : P ⁻¹' R ⊆ Hironaka.BlowupSequences.exceptionalLocus n P) :
    (f ∘ P ∘ e.symm) ⁻¹' (f.symm ⁻¹' R) ⊆
      Hironaka.BlowupSequences.exceptionalLocus n (f ∘ P ∘ e.symm) := by
  rw [conjugate_exceptionalLocus e f P hP]
  intro y hy
  apply hExc
  simpa only [Set.mem_preimage,Function.comp_apply,f.symm_apply_apply] using hy

end
end Hironaka.HironakaG3UniverseDiffeoDerivative
