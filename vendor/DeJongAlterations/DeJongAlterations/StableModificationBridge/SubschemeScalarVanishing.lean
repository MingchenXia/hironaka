import DeJongAlterations.StableModificationBridge.TwoSectionScalarVanishing
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-! The actual affine closed-subscheme maps internally transfer reduced scalar Serre vanishing. -/

noncomputable section

namespace DeJongAlterations.StableModificationBridge.SubschemeScalarVanishing

open CategoryTheory AlgebraicGeometry Opposite
open StableModification StableModification.Cohomology StableModification.Projectivity
open StableModification.CurvesField StableModification.CurvesField.Positive

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The WHOLE actual closed-subscheme section map, transported only across equal native opens. -/
def coverMap (U : X.Opens) (W : I.subscheme.Opens) (hW : W = I.subschemeι ⁻¹ᵁ U) :
    Γ(X, U) →+* Γ(I.subscheme, W) := by
  subst W
  exact (I.subschemeι.app U).hom

/-- Actual affine quotient surjectivity is internal; no coefficient-lift certificate is supplied. -/
theorem coverMap_surjective (U : X.Opens) (hU : IsAffineOpen U)
    (W : I.subscheme.Opens) (hW : W = I.subschemeι ⁻¹ᵁ U) :
    Function.Surjective (coverMap I U W hW) := by
  subst W
  exact I.subschemeι_app_surjective ⟨U, hU⟩

/-- The ENTIRE kernel is precisely the SAME actual original ideal on the affine open. -/
theorem coverMap_kernel (U : X.Opens) (hU : IsAffineOpen U)
    (W : I.subscheme.Opens) (hW : W = I.subschemeι ⁻¹ᵁ U) :
    RingHom.ker (coverMap I U W hW) = I.ideal ⟨U, hU⟩ := by
  subst W
  exact I.ker_subschemeι_app ⟨U, hU⟩

/-- EVERY native restriction follows its original closed-subscheme naturality square. -/
theorem coverMap_restrict {U V : X.Opens} (h : V ≤ U)
    {W Z : I.subscheme.Opens} (hW : W = I.subschemeι ⁻¹ᵁ U)
    (hZ : Z = I.subschemeι ⁻¹ᵁ V) (a : Γ(X, U)) :
    coverMap I V Z hZ (X.presheaf.map (homOfLE h).op a) =
      I.subscheme.presheaf.map
        (homOfLE (by rw [hZ, hW]; exact I.subschemeι.preimage_mono h)).op
        (coverMap I U W hW a) := by
  subst W
  subst Z
  exact Projectivity.LineBundleData.app_res I.subschemeι h a

/-- The SAME actual quotient-cover coefficient has exactly its original inverse-image basic open. -/
theorem coverMap_basicOpen (U : X.Opens) (W : I.subscheme.Opens)
    (hW : W = I.subschemeι ⁻¹ᵁ U) (a : Γ(X, U)) :
    I.subscheme.basicOpen (coverMap I U W hW a) = I.subschemeι ⁻¹ᵁ X.basicOpen a := by
  subst W
  exact (Scheme.preimage_basicOpen I.subschemeι a).symm

variable {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
  (hUV : IsAffineOpen (U ⊓ V))
  {M : LineBundleData I.subscheme} {N : ℤ} (s₀ s₁ : M.Sections N ⊤)
  (h₀ : s₀.nonvanishingLocus = I.subschemeι ⁻¹ᵁ U)
  (h₁ : s₁.nonvanishingLocus = I.subschemeι ⁻¹ᵁ V)

include h₀ h₁ in
private theorem overlap_eq :
    s₀.nonvanishingLocus ⊓ s₁.nonvanishingLocus = I.subschemeι ⁻¹ᵁ (U ⊓ V) := by
  rw [h₀, h₁]
  rfl

variable [CompactSpace I.subscheme]
  [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from I.subscheme))]
  {K : Type u} [Field K] (p : I.subscheme ⟶ Spec (.of K)) (hp : IsProjectiveOver p)

include hp hU hV hUV in
/-- Actual geometry on the same closed subscheme INTERNALLY supplies the modulo-ideal scalar engine input. -/
theorem exists_modulo_scalar_coboundaries
    (hcov : s₀.nonvanishingLocus ⊔ s₁.nonvanishingLocus = ⊤)
    (haff₀ : IsAffineOpen s₀.nonvanishingLocus) (haff₁ : IsAffineOpen s₁.nonvanishingLocus)
    (g : Γ(X, U ⊓ V)ˣ)
    (hg : coverMap I (U ⊓ V) _ (overlap_eq I s₀ s₁ h₀ h₁) g =
      (TwoSectionScalarVanishing.transition s₀ s₁ :
        Γ(I.subscheme, s₀.nonvanishingLocus ⊓ s₁.nonvanishingLocus))) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ w : Γ(X, U ⊓ V),
      ∃ a : Γ(X, U), ∃ b : Γ(X, V),
        w - (resR U V b + (g : Γ(X, U ⊓ V)) ^ k * resL U V a) ∈ I.ideal ⟨_, hUV⟩ := by
  obtain ⟨k₀, hk₀⟩ := TwoSectionScalarVanishing.exists_scalar_coboundaries
    s₀ s₁ p hp hcov haff₀ haff₁
  refine ⟨k₀, fun k hk w => ?_⟩
  obtain ⟨a, b, hab⟩ := hk₀ k hk
    (coverMap I (U ⊓ V) _ (overlap_eq I s₀ s₁ h₀ h₁) w)
  obtain ⟨a', rfl⟩ := coverMap_surjective I U hU _ h₀ a
  obtain ⟨b', rfl⟩ := coverMap_surjective I V hV _ h₁ b
  refine ⟨a', b', ?_⟩
  rw [← coverMap_kernel I (U ⊓ V) hUV _ (overlap_eq I s₀ s₁ h₀ h₁)]
  change coverMap I (U ⊓ V) _ (overlap_eq I s₀ s₁ h₀ h₁)
    (w - (resR U V b' + (g : Γ(X, U ⊓ V)) ^ k * resL U V a')) = 0
  rw [map_sub, map_add, map_mul, map_pow, hg]
  rw [coverMap_restrict I inf_le_right h₁ (overlap_eq I s₀ s₁ h₀ h₁),
    coverMap_restrict I inf_le_left h₀ (overlap_eq I s₀ s₁ h₀ h₁)]
  exact sub_eq_zero.mpr hab

end DeJongAlterations.StableModificationBridge.SubschemeScalarVanishing
