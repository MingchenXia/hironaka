import Hironaka.Algebra.ProjectiveSecantTangentJacobian

/-!
# An original polynomial relation with a genuine nonzero rational-point derivative
-/

noncomputable section

open IsLocalRing

namespace Hironaka.Algebra.ProjectiveSecant

open RegularSmoothConverseJacobian

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]

/-- The complete actual residue square retains the entire original algebra point, not merely its coefficient inclusion. -/
@[simp]
theorem rationalResidueEquiv_algebraMap_original (e : A →ₐ[k] k) (a : A) :
    rationalResidueEquiv e (algebraMap A (rationalPointIdeal e).ResidueField a) = e a := by
  change (Ideal.algEquivResidueFieldOfField (⊥ : Ideal k)).symm
    (Ideal.ResidueField.map (rationalPointIdeal e) (⊥ : Ideal k) e.toRingHom rfl
      (algebraMap A (rationalPointIdeal e).ResidueField a)) = e a
  rw [Ideal.ResidueField.map_algebraMap]
  exact (Ideal.algEquivResidueFieldOfField (⊥ : Ideal k)).symm_apply_apply (e a)

variable {ι : Type*} [Finite ι]

/-- Clearing the actual original localization denominator retains both actual kernel membership and a genuine nonzero original partial derivative. -/
theorem exists_polynomial_kernel_derivative_ne_zero (e : MvPolynomial ι k →ₐ[k] k)
    {Q : Type*} [CommRing Q] [IsRegularLocalRing Q]
    (f : Localization.AtPrime (rationalPointIdeal e) →+* Q) (hf : Function.Surjective f)
    (hdim : ringKrullDim Q < ringKrullDim (Localization.AtPrime (rationalPointIdeal e))) :
    ∃ F : MvPolynomial ι k,
      f (algebraMap (MvPolynomial ι k) (Localization.AtPrime (rationalPointIdeal e)) F) = 0 ∧
        ∃ j : ι, e (MvPolynomial.pderiv j F) ≠ 0 := by
  let p := rationalPointIdeal e
  let P := Localization.AtPrime p
  obtain ⟨x, hxf, j, hxj⟩ := exists_local_kernel_derivative_ne_zero e f hf hdim
  obtain ⟨F, s, he⟩ := IsLocalization.exists_mk'_eq p.primeCompl (x : P)
  have hspec : algebraMap (MvPolynomial ι k) P s * (x : P) = algebraMap (MvPolynomial ι k) P F := by
    rw [← he]
    exact IsLocalization.mk'_spec' P F s
  refine ⟨F, ?_, j, ?_⟩
  · rw [← hspec, map_mul, hxf, mul_zero]
  · have hxres : residue P (x : P) = 0 := (residue_eq_zero_iff (x : P)).mpr x.property
    have hsres : residue P (algebraMap (MvPolynomial ι k) P s) ≠ 0 :=
      (residue_ne_zero_iff_isUnit _).mpr (IsLocalization.map_units P s)
    have hd := congrArg (fun a : P => residue P (coordinateDerivation p j a)) hspec
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, hxres, zero_mul, add_zero] at hd
    rw [coordinateDerivation_algebraMap p j F] at hd
    have hpart : residue P (algebraMap (MvPolynomial ι k) P (MvPolynomial.pderiv j F)) ≠ 0 := by
      rw [← hd]
      exact mul_ne_zero hsres hxj
    intro hz
    apply hpart
    apply (rationalResidueEquiv e).injective
    change rationalResidueEquiv e (algebraMap (MvPolynomial ι k) p.ResidueField (MvPolynomial.pderiv j F)) =
      rationalResidueEquiv e 0
    rw [rationalResidueEquiv_algebraMap_original, map_zero, hz]

end Hironaka.Algebra.ProjectiveSecant
