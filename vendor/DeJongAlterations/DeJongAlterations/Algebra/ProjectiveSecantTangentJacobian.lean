import DeJongAlterations.Algebra.ProjectiveSecantTangentParameter
import DeJongAlterations.Algebra.ProjectiveSecantRationalResidue
import DeJongAlterations.Algebra.RegularSmoothConverseJacobian

/-!
# Actual rational-point cotangent Jacobians over arbitrary original fields

The native conormal injectivity calculation is adapted from
EnvelopeProperty/LocalCotangentKaehler.lean, SHA256
335b9e44518f54aaa861d650dde0cb0839061b6476400b37979b0727c2a54c02.
The original algebra point produces its residue-field identification internally.
-/

noncomputable section

open IsLocalRing TensorProduct KaehlerDifferential

namespace DeJongAlterations.Algebra.ProjectiveSecant

open RegularSmoothConverseResidue RegularSmoothConverseJacobian

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual native conormal injectivity for an actually formally etale residue extension. -/
theorem residueCotangentMap_injective_of_formallyEtale {k P : Type*}
    [CommRing k] [CommRing P] [Algebra k P] [IsLocalRing P]
    [Algebra.FormallySmooth k P] [Algebra.FormallyEtale k (ResidueField P)] :
    Function.Injective (residueCotangentMap (k := k) (R := P)) := by
  have hs : Function.Surjective (algebraMap P (ResidueField P)) := residue_surjective
  have hi := (Algebra.FormallySmooth.kerCotangentToTensor_injective_iff
    (R := k) (P := P) (A := ResidueField P) hs).mpr inferInstance
  intro x y hxy
  apply (residueKernelCotangentEquiv (R := P)).injective
  apply hi
  exact hxy

variable {k ι : Type*} [Field k] [Finite ι]

/-- The original actual rational point internally makes its actual localized cotangent Jacobian injective, without perfectness. -/
theorem rational_localizedCotangentJacobian_injective (e : MvPolynomial ι k →ₐ[k] k) :
    Function.Injective (localizedCotangentJacobian (rationalPointIdeal e)) := by
  let p := rationalPointIdeal e
  let P := Localization.AtPrime p
  let : Algebra.FormallyEtale (MvPolynomial ι k) P := Algebra.FormallyEtale.of_isLocalization p.primeCompl
  let : Algebra.FormallySmooth k P := Algebra.FormallySmooth.comp k (MvPolynomial ι k) P
  exact (Finsupp.linearEquivFunOnFinite (ResidueField P) (ResidueField P) ι).injective.comp
    (((localizedKaehlerBasis p).baseChange (ResidueField P)).repr.injective.comp
      residueCotangentMap_injective_of_formallyEtale)

/-- Strict regular-local dimension drop at the actual original rational polynomial point internally produces an original kernel element with a genuine nonzero original residue derivative. -/
theorem exists_local_kernel_derivative_ne_zero (e : MvPolynomial ι k →ₐ[k] k)
    {Q : Type*} [CommRing Q] [IsRegularLocalRing Q]
    (f : Localization.AtPrime (rationalPointIdeal e) →+* Q) (hf : Function.Surjective f)
    (hdim : ringKrullDim Q < ringKrullDim (Localization.AtPrime (rationalPointIdeal e))) :
    ∃ x : maximalIdeal (Localization.AtPrime (rationalPointIdeal e)), f x = 0 ∧
      ∃ j : ι, residue (Localization.AtPrime (rationalPointIdeal e))
        (coordinateDerivation (rationalPointIdeal e) j x) ≠ 0 := by
  obtain ⟨x, hxf, hx⟩ := exists_kernel_cotangent_ne_zero f hf hdim
  refine ⟨x, hxf, ?_⟩
  classical
  by_contra! h
  apply hx
  apply rational_localizedCotangentJacobian_injective e
  rw [map_zero]
  funext j
  rw [localizedCotangentJacobian_toCotangent]
  exact h j

end DeJongAlterations.Algebra.ProjectiveSecant
