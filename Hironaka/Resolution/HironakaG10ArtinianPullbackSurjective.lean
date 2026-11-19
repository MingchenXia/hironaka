import Hironaka.Resolution.HironakaG10ArtinianParameterPullback
set_option autoImplicit false
open scoped TensorProduct
namespace Hironaka.HironakaG10ArtinianPullbackSurjective
open HironakaRelativeNormalIdeal HironakaActualCentreJointJets HironakaActualJointBaseFibre
  HironakaG10ArtinianParameterPullback
noncomputable section

/-- If the actual parameter quotient is surjective, so is the full analytic
nilpotent substitution to the tensor fibre germ ring. -/
theorem actualArtinianParameterPullback_surjective {Q : Type} [CommRing Q] [Algebra ℂ Q]
    (d t q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Q)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom) (hsurj : Function.Surjective φ) :
    Function.Surjective (actualArtinianParameterPullback d t q φ hφ) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul a b =>
    obtain ⟨c,rfl⟩ := hsurj a
    refine ⟨tangentPullback d t c * jointNormalPullback d t b, ?_⟩
    rw [map_mul, actualArtinianParameterPullback_base, actualArtinianParameterPullback_fibre,
      Algebra.TensorProduct.tmul_mul_tmul]
    simp
  | add a b ha hb =>
    obtain ⟨u,hu⟩ := ha
    obtain ⟨v,hv⟩ := hb
    exact ⟨u+v, by rw [map_add,hu,hv]⟩
/-- The whole extension of the parameter kernel is killed by substitution. -/
theorem mapped_parameter_kernel_le {Q : Type} [CommRing Q] [Algebra ℂ Q]
    (d t q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Q)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom) :
    Ideal.map (tangentPullback d t).toRingHom (RingHom.ker φ.toRingHom) ≤
      RingHom.ker (actualArtinianParameterPullback d t q φ hφ).toRingHom := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  change actualArtinianParameterPullback d t q φ hφ (tangentPullback d t a) = 0
  rw [actualArtinianParameterPullback_base]
  change φ a = 0 at ha
  simp [ha]

/-- Substitution descends to the whole joint-germ quotient by the extended
parameter kernel, retaining its actual quotient operations. -/
def quotientToTensorFibre {Q : Type} [CommRing Q] [Algebra ℂ Q]
    (d t q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Q)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom) :
    (HolGerm (ComplexModel (d+t)) ⧸
      Ideal.map (tangentPullback d t).toRingHom (RingHom.ker φ.toRingHom)) →ₐ[ℂ]
      (Q ⊗[ℂ] HolGerm (ComplexModel t)) :=
  Ideal.Quotient.liftₐ _ (actualArtinianParameterPullback d t q φ hφ)
    (fun _ ha => mapped_parameter_kernel_le d t q φ hφ ha)

/-- It is onto when the original parameter map is onto. -/
theorem quotientToTensorFibre_surjective {Q : Type} [CommRing Q] [Algebra ℂ Q]
    (d t q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Q)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom) (hsurj : Function.Surjective φ) :
    Function.Surjective (quotientToTensorFibre d t q φ hφ) := by
  intro x
  obtain ⟨a,ha⟩ := actualArtinianParameterPullback_surjective d t q φ hφ hsurj x
  exact ⟨Ideal.Quotient.mk _ a,ha⟩
end
end Hironaka.HironakaG10ArtinianPullbackSurjective
