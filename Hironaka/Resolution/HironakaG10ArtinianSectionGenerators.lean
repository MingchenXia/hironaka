import Hironaka.Resolution.HironakaG10ArtinianTensorSection
set_option autoImplicit false
open scoped TensorProduct
namespace Hironaka.HironakaG10ArtinianSectionGenerators
open HironakaRelativeNormalIdeal HironakaActualJointBaseFibre
  HironakaG10ArtinianParameterPullback HironakaG10ArtinianTensorSection
noncomputable section

/-- Original base scalar images agree with the actual joint quotient. -/
theorem quotientBaseMap_phi {Q : Type} [CommRing Q] [Algebra ℂ Q]
    (d t : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Q) (hsurj : Function.Surjective φ)
    (a : HolGerm (ComplexModel d)) :
    quotientBaseMap d t φ hsurj (φ a) = Ideal.Quotient.mk _ (tangentPullback d t a) := by
  change (Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ ℂ _).comp (tangentPullback d t))
    (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ ha)))
    ((Ideal.quotientKerAlgEquivOfSurjective hsurj).symm (φ a)) = _
  rw [Ideal.quotientKerAlgEquivOfSurjective_symm_apply]
  rfl

/-- Substitution followed by the constructed section fixes every original
whole base germ in the joint quotient. -/
theorem section_substitution_base {Q : Type} [CommRing Q] [Algebra ℂ Q]
    (d t q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Q)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom) (hsurj : Function.Surjective φ)
    (a : HolGerm (ComplexModel d)) :
    tensorFibreToQuotient d t φ hsurj
      (actualArtinianParameterPullback d t q φ hφ (tangentPullback d t a)) =
      Ideal.Quotient.mk _ (tangentPullback d t a) := by
  rw [actualArtinianParameterPullback_base]
  change quotientBaseMap d t φ hsurj (φ a) *
      ((Ideal.Quotient.mkₐ ℂ _).comp (jointNormalPullback d t)) 1 = _
  rw [map_one, mul_one, quotientBaseMap_phi]

/-- The same composite fixes every original whole fibre germ. -/
theorem section_substitution_fibre {Q : Type} [CommRing Q] [Algebra ℂ Q]
    (d t q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Q)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom) (hsurj : Function.Surjective φ)
    (b : HolGerm (ComplexModel t)) :
    tensorFibreToQuotient d t φ hsurj
      (actualArtinianParameterPullback d t q φ hφ (jointNormalPullback d t b)) =
      Ideal.Quotient.mk _ (jointNormalPullback d t b) := by
  rw [actualArtinianParameterPullback_fibre]
  change quotientBaseMap d t φ hsurj 1 *
      ((Ideal.Quotient.mkₐ ℂ _).comp (jointNormalPullback d t)) b = _
  rw [map_one, one_mul]
  rfl
end
end Hironaka.HironakaG10ArtinianSectionGenerators
