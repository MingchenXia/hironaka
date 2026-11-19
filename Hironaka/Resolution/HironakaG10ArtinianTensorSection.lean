import Hironaka.Resolution.HironakaG10ArtinianPullbackSurjective
import Mathlib.RingTheory.Ideal.Quotient.Operations
set_option autoImplicit false
open scoped TensorProduct
namespace Hironaka.HironakaG10ArtinianTensorSection
open HironakaRelativeNormalIdeal HironakaActualJointBaseFibre
  HironakaG10ArtinianParameterPullback HironakaG10ArtinianPullbackSurjective
noncomputable section

/-- The base quotient acts on the actual joint quotient through its original
parameter map. -/
def quotientBaseMap {Q : Type} [CommRing Q] [Algebra ℂ Q]
    (d t : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Q) (hsurj : Function.Surjective φ) :
    Q →ₐ[ℂ] (HolGerm (ComplexModel (d+t)) ⧸
      Ideal.map (tangentPullback d t).toRingHom (RingHom.ker φ.toRingHom)) :=
  (Ideal.Quotient.liftₐ (RingHom.ker φ.toRingHom)
    ((Ideal.Quotient.mkₐ ℂ _).comp (tangentPullback d t))
    (fun _ ha => Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ ha))).comp
      (Ideal.quotientKerAlgEquivOfSurjective hsurj).symm.toAlgHom

/-- Universal tensor section built from the actual base and fibre pullbacks. -/
def tensorFibreToQuotient {Q : Type} [CommRing Q] [Algebra ℂ Q]
    (d t : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Q) (hsurj : Function.Surjective φ) :
    (Q ⊗[ℂ] HolGerm (ComplexModel t)) →ₐ[ℂ]
      (HolGerm (ComplexModel (d+t)) ⧸
        Ideal.map (tangentPullback d t).toRingHom (RingHom.ker φ.toRingHom)) :=
  Algebra.TensorProduct.lift (quotientBaseMap d t φ hsurj)
    ((Ideal.Quotient.mkₐ ℂ _).comp (jointNormalPullback d t)) (fun _ _ => Commute.all _ _)

/-- The section is a right inverse to the actual substitution on all tensors. -/
theorem quotientToTensorFibre_section {Q : Type} [CommRing Q] [Algebra ℂ Q]
    (d t q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Q)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom) (hsurj : Function.Surjective φ)
    (x : Q ⊗[ℂ] HolGerm (ComplexModel t)) :
    quotientToTensorFibre d t q φ hφ (tensorFibreToQuotient d t φ hsurj x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a b =>
    obtain ⟨c,rfl⟩ := hsurj a
    have hbase : quotientBaseMap d t φ hsurj (φ c) =
        Ideal.Quotient.mk _ (tangentPullback d t c) := by
      change (Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ ℂ _).comp (tangentPullback d t))
        (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ ha)))
        ((Ideal.quotientKerAlgEquivOfSurjective hsurj).symm (φ c)) = _
      rw [Ideal.quotientKerAlgEquivOfSurjective_symm_apply]
      rfl
    change quotientToTensorFibre d t q φ hφ
      (quotientBaseMap d t φ hsurj (φ c) * Ideal.Quotient.mk _ (jointNormalPullback d t b)) = _
    rw [hbase, map_mul]
    change actualArtinianParameterPullback d t q φ hφ (tangentPullback d t c) *
      actualArtinianParameterPullback d t q φ hφ (jointNormalPullback d t b) = _
    rw [actualArtinianParameterPullback_base, actualArtinianParameterPullback_fibre,
      Algebra.TensorProduct.tmul_mul_tmul]
    simp
  | add a b ha hb => rw [map_add, map_add, ha, hb]
end
end Hironaka.HironakaG10ArtinianTensorSection
