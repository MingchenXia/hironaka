import Hironaka.Resolution.HironakaG10ArtinianSectionGenerators
import Hironaka.Resolution.HironakaG10ArtinianNormalIdeal
set_option autoImplicit false
open scoped TensorProduct
namespace Hironaka.HironakaG10ArtinianPolynomialIdentity
open HolGerm HironakaHolomorphicJetMonomialSpan HironakaRelativeNormalIdeal
  HironakaRelativeNormalMonomialBasis HironakaActualRelativeCoefficientGerms HironakaActualJointBaseFibre
  HironakaG10ArtinianParameterPullback HironakaG10ArtinianPullbackSurjective HironakaG10ArtinianTensorSection
  HironakaG10ArtinianSectionGenerators HironakaG10ArtinianNormalIdeal
noncomputable section

/-- The original joint quotient and the substitution-section composite agree
on every genuine relative polynomial, including whole fibre-germ coefficients. -/
theorem section_substitution_polynomial {Q : Type} [CommRing Q] [Algebra ℂ Q]
    (d t q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Q)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom) (hsurj : Function.Surjective φ)
    (P : MvPolynomial (Fin d) (HolGerm (ComplexModel t))) :
    tensorFibreToQuotient d t φ hsurj
      (actualArtinianParameterPullback d t q φ hφ
        ((swapParameterFibre d t).symm (normalPolynomialEval t d P))) =
      Ideal.Quotient.mk _ ((swapParameterFibre d t).symm (normalPolynomialEval t d P)) := by
  letI := tangentAlgebra t d
  let J := Ideal.map (tangentPullback d t).toRingHom (RingHom.ker φ.toRingHom)
  let U : HolGerm (ComplexModel (t+d)) →+* (HolGerm (ComplexModel (d+t)) ⧸ J) :=
    (tensorFibreToQuotient d t φ hsurj).toRingHom.comp
      ((actualArtinianParameterPullback d t q φ hφ).toRingHom.comp
        (swapParameterFibre d t).symm.toRingHom)
  let V : HolGerm (ComplexModel (t+d)) →+* (HolGerm (ComplexModel (d+t)) ⧸ J) :=
    (Ideal.Quotient.mk J).comp (swapParameterFibre d t).symm.toRingHom
  have hC (b : HolGerm (ComplexModel t)) :
      U (tangentPullback t d b) = V (tangentPullback t d b) := by
    have he : (swapParameterFibre d t).symm (tangentPullback t d b) =
        jointNormalPullback d t b :=
      (swapParameterFibre d t).symm_apply_eq.mpr (swapParameterFibre_fibre d t b).symm
    change tensorFibreToQuotient d t φ hsurj
      (actualArtinianParameterPullback d t q φ hφ
        ((swapParameterFibre d t).symm (tangentPullback t d b))) =
        Ideal.Quotient.mk J ((swapParameterFibre d t).symm (tangentPullback t d b))
    rw [he]
    exact section_substitution_fibre d t q φ hφ hsurj b
  have hX (i : Fin d) : U (normalCoordinate t d i) = V (normalCoordinate t d i) := by
    have he : (swapParameterFibre d t).symm (normalCoordinate t d i) =
        tangentPullback d t (coordinateGerm i) := by
      apply (swapParameterFibre d t).symm_apply_eq.mpr
      rw [swapParameterFibre_base, jointNormalPullback_coordinate']
    change tensorFibreToQuotient d t φ hsurj
      (actualArtinianParameterPullback d t q φ hφ
        ((swapParameterFibre d t).symm (normalCoordinate t d i))) =
        Ideal.Quotient.mk J ((swapParameterFibre d t).symm (normalCoordinate t d i))
    rw [he]
    exact section_substitution_base d t q φ hφ hsurj (coordinateGerm i)
  have hp : U.comp (normalPolynomialEval t d).toRingHom =
      V.comp (normalPolynomialEval t d).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro b
      change U (normalPolynomialEval t d (MvPolynomial.C b)) =
        V (normalPolynomialEval t d (MvPolynomial.C b))
      rw [normalPolynomialEval, MvPolynomial.aeval_C]
      exact hC b
    · intro i
      change U (normalPolynomialEval t d (MvPolynomial.X i)) =
        V (normalPolynomialEval t d (MvPolynomial.X i))
      rw [normalPolynomialEval, MvPolynomial.aeval_X]
      exact hX i
  exact congrArg (fun f : MvPolynomial (Fin d) (HolGerm (ComplexModel t)) →+*
    (HolGerm (ComplexModel (d+t)) ⧸ J) => f P) hp
/-- Nilpotent Taylor remainders give the reverse composite on every original
whole joint germ. -/
theorem section_substitution_all {Q : Type} [CommRing Q] [Algebra ℂ Q]
    (d t q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Q)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom) (hsurj : Function.Surjective φ)
    (g : HolGerm (ComplexModel (d+t))) :
    tensorFibreToQuotient d t φ hsurj
      (actualArtinianParameterPullback d t q φ hφ g) = Ideal.Quotient.mk _ g := by
  let J := Ideal.map (tangentPullback d t).toRingHom (RingHom.ker φ.toRingHom)
  let e := swapParameterFibre d t
  let P := actualNormalTaylorPolynomial t d (q+1) (e g)
  have hr : e g - normalPolynomialEval t d P ∈ Ideal.map e.toRingHom J :=
    normalPower_le_swapped_parameter_kernel d t q φ hφ
      (actualNormalTaylorPolynomial_remainder t d (q+1) (e g))
  have hb : e.symm (e g - normalPolynomialEval t d P) ∈ J := by
    obtain ⟨a,ha,he⟩ := (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).mp hr
    rw [← he]
    change e.symm (e a) ∈ J
    simpa only [AlgEquiv.symm_apply_apply] using ha
  have hq : Ideal.Quotient.mk J g = Ideal.Quotient.mk J (e.symm (normalPolynomialEval t d P)) := by
    apply Ideal.Quotient.eq.mpr
    simpa only [map_sub, AlgEquiv.symm_apply_apply] using hb
  have hm : actualArtinianParameterPullback d t q φ hφ g =
      actualArtinianParameterPullback d t q φ hφ (e.symm (normalPolynomialEval t d P)) := by
    change quotientToTensorFibre d t q φ hφ (Ideal.Quotient.mk J g) =
      quotientToTensorFibre d t q φ hφ (Ideal.Quotient.mk J (e.symm (normalPolynomialEval t d P)))
    rw [hq]
  rw [hm, section_substitution_polynomial]
  exact hq.symm
/-- The section is also a left inverse on the whole actual joint quotient. -/
theorem tensorSection_left_inverse {Q : Type} [CommRing Q] [Algebra ℂ Q]
    (d t q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Q)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom) (hsurj : Function.Surjective φ)
    (x : HolGerm (ComplexModel (d+t)) ⧸
      Ideal.map (tangentPullback d t).toRingHom (RingHom.ker φ.toRingHom)) :
    tensorFibreToQuotient d t φ hsurj (quotientToTensorFibre d t q φ hφ x) = x := by
  obtain ⟨g,rfl⟩ := Ideal.Quotient.mk_surjective x
  exact section_substitution_all d t q φ hφ hsurj g

/-- The whole actual joint quotient is the entire Artinian tensor fibre. -/
def actualJointQuotientTensorEquiv {Q : Type} [CommRing Q] [Algebra ℂ Q]
    (d t q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Q)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom) (hsurj : Function.Surjective φ) :
    (HolGerm (ComplexModel (d+t)) ⧸
      Ideal.map (tangentPullback d t).toRingHom (RingHom.ker φ.toRingHom)) ≃ₐ[ℂ]
      (Q ⊗[ℂ] HolGerm (ComplexModel t)) :=
  AlgEquiv.ofAlgHom (quotientToTensorFibre d t q φ hφ) (tensorFibreToQuotient d t φ hsurj)
    (by apply AlgHom.ext; intro x; exact quotientToTensorFibre_section d t q φ hφ hsurj x)
    (by apply AlgHom.ext; intro x; exact tensorSection_left_inverse d t q φ hφ hsurj x)
/-- The whole quotient equivalence respects the original parameter algebra,
not only the complex scalar structure. -/
def actualJointQuotientTensorParamEquiv {Q : Type} [CommRing Q] [Algebra ℂ Q]
    (d t q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Q)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom) (hsurj : Function.Surjective φ) :
    letI : Algebra Q (HolGerm (ComplexModel (d+t)) ⧸
      Ideal.map (tangentPullback d t).toRingHom (RingHom.ker φ.toRingHom)) :=
        (quotientBaseMap d t φ hsurj).toRingHom.toAlgebra
    letI : Algebra Q (Q ⊗[ℂ] HolGerm (ComplexModel t)) := Algebra.TensorProduct.leftAlgebra
    (HolGerm (ComplexModel (d+t)) ⧸
      Ideal.map (tangentPullback d t).toRingHom (RingHom.ker φ.toRingHom)) ≃ₐ[Q]
      (Q ⊗[ℂ] HolGerm (ComplexModel t)) := by
  letI : Algebra Q (HolGerm (ComplexModel (d+t)) ⧸
      Ideal.map (tangentPullback d t).toRingHom (RingHom.ker φ.toRingHom)) :=
        (quotientBaseMap d t φ hsurj).toRingHom.toAlgebra
  letI : Algebra Q (Q ⊗[ℂ] HolGerm (ComplexModel t)) := Algebra.TensorProduct.leftAlgebra
  refine { (actualJointQuotientTensorEquiv d t q φ hφ hsurj).toRingEquiv with
    commutes' := ?_ }
  intro a
  change quotientToTensorFibre d t q φ hφ (quotientBaseMap d t φ hsurj a) = a ⊗ₜ[ℂ] 1
  have h := quotientToTensorFibre_section d t q φ hφ hsurj (a ⊗ₜ[ℂ] (1 : HolGerm (ComplexModel t)))
  change quotientToTensorFibre d t q φ hφ
    (quotientBaseMap d t φ hsurj a *
      ((Ideal.Quotient.mkₐ ℂ _).comp (jointNormalPullback d t)) 1) = _ at h
  simpa only [map_one, mul_one] using h
end
end Hironaka.HironakaG10ArtinianPolynomialIdentity
