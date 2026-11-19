import Hironaka.Geometry.ProjectiveSecantIntegralOpenDescent
import Mathlib.AlgebraicGeometry.Properties

/-!
# Actual original scheme opens descend along integral morphisms
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.ProjectiveSecant

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Exact original affine spectrum triangles turn integral contraction into an actual original base open. -/
theorem exists_nonempty_base_open_of_affine_integral
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [IsIntegralHom f] (O : X.Opens) (hO : (O : Set X).Nonempty) :
    ∃ V : Y.Opens, (V : Set Y).Nonempty ∧ (f ⁻¹ᵁ V) ≤ O := by
  let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  let : Algebra.IsIntegral Γ(Y, ⊤) Γ(X, ⊤) := ⟨f.isIntegral_app ⊤ (isAffineOpen_top _)⟩
  let O' := X.isoSpec.inv ⁻¹ᵁ O
  have hO' : (O' : Set (Spec Γ(X, ⊤))).Nonempty := by
    obtain ⟨x, hx⟩ := hO
    refine ⟨X.isoSpec.hom x, ?_⟩
    change X.isoSpec.inv (X.isoSpec.hom x) ∈ O
    simpa [← Scheme.Hom.comp_apply] using hx
  obtain ⟨a, _, hDa, hpre⟩ :=
    exists_nonempty_base_principal_open_of_integral Γ(Y, ⊤) Γ(X, ⊤) O' hO'
  let V := Y.isoSpec.hom ⁻¹ᵁ PrimeSpectrum.basicOpen a
  refine ⟨V, ?_, ?_⟩
  · obtain ⟨y, hy⟩ := hDa
    refine ⟨Y.isoSpec.inv y, ?_⟩
    change Y.isoSpec.hom (Y.isoSpec.inv y) ∈ PrimeSpectrum.basicOpen a
    have hpoint : Y.isoSpec.hom (Y.isoSpec.inv y) = y := by
      change (Y.isoSpec.inv ≫ Y.isoSpec.hom) y = y
      rw [Y.isoSpec.inv_hom_id]
      rfl
    rw [hpoint]
    exact hy
  · intro x hx
    have hmap : (Spec.map f.appTop) (X.isoSpec.hom x) = Y.isoSpec.hom (f x) :=
      congrArg (fun g : X ⟶ Spec Γ(Y, ⊤) => g x) (Scheme.isoSpec_hom_naturality f)
    have hx' : X.isoSpec.hom x ∈
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) Γ(X, ⊤))) ⁻¹ᵁ PrimeSpectrum.basicOpen a) := by
      change (Spec.map f.appTop) (X.isoSpec.hom x) ∈ PrimeSpectrum.basicOpen a
      rw [hmap]
      exact hx
    have h := hpre hx'
    change X.isoSpec.inv (X.isoSpec.hom x) ∈ O at h
    simpa [← Scheme.Hom.comp_apply] using h

/-- The original target affine chart and its actual integral preimage internally descend any specified nonempty original source open. -/
theorem exists_nonempty_base_open_of_integral
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsIntegralHom f] (O : X.Opens) (hO : (O : Set X).Nonempty) :
    ∃ V : Y.Opens, (V : Set Y).Nonempty ∧ (f ⁻¹ᵁ V) ≤ O := by
  obtain ⟨x, hx⟩ := hO
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hyV, _⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (show f x ∈ (⊤ : Y.Opens) from trivial) (⊤ : Y.Opens).isOpen
  let V : Y.Opens := V₀
  have hV : IsAffineOpen V := hV₀
  let W := f ⁻¹ᵁ V
  let : Nonempty V := ⟨⟨f x, hyV⟩⟩
  let : Nonempty W := ⟨⟨x, hyV⟩⟩
  let : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  let : IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι
  let : IsAffine V.toScheme := hV
  let : IsAffine W.toScheme := hV.preimage f
  let g := f ∣_ V
  let O' := W.ι ⁻¹ᵁ O
  have hO' : (O' : Set W).Nonempty := ⟨⟨x, hyV⟩, hx⟩
  obtain ⟨B, hB, hpre⟩ := exists_nonempty_base_open_of_affine_integral g O' hO'
  let V' := V.ι ''ᵁ B
  refine ⟨V', ?_, ?_⟩
  · obtain ⟨y, hy⟩ := hB
    exact ⟨V.ι y, y, hy, rfl⟩
  · intro z hz
    obtain ⟨y, hyB, hy⟩ := hz
    have hzV : f z ∈ V := by
      rw [← hy]
      exact y.2
    let w : W := ⟨z, hzV⟩
    have hgy : g w = y := by
      apply V.ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, morphismRestrict_ι]
      exact hy.symm
    exact hpre (show g w ∈ B from hgy.symm ▸ hyB)

end Hironaka.Geometry.ProjectiveSecant
