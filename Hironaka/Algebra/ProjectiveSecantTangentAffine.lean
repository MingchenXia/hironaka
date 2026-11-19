import Hironaka.Algebra.ProjectiveSecantTangentRelation
import Hironaka.Algebra.ProjectiveSecantTangentDimension
import Mathlib.RingTheory.RingHom.Surjective

/-!
# Actual original affine dimension and regularity produce a genuine original tangent equation
-/

noncomputable section

open IsLocalRing

namespace Hironaka.Algebra.ProjectiveSecant

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {k A ι : Type u} [Field k] [CommRing A] [Algebra k A] [Finite ι]

/-- Original affine geometry internally yields an element of the WHOLE original polynomial kernel with a nonzero original rational-point partial derivative. -/
theorem exists_affine_kernel_derivative_ne_zero (φ : MvPolynomial ι k →ₐ[k] A)
    (hφ : Function.Surjective φ) (a : A →ₐ[k] k)
    [IsRegularLocalRing (Localization.AtPrime (rationalPointIdeal a))]
    (hdim : ringKrullDim A < Nat.card ι) :
    ∃ F : MvPolynomial ι k, φ F = 0 ∧ ∃ j : ι, (a.comp φ) (MvPolynomial.pderiv j F) ≠ 0 := by
  let q := rationalPointIdeal a
  let e := a.comp φ
  let p := rationalPointIdeal e
  let f : Localization.AtPrime p →+* Localization.AtPrime q :=
    Localization.localRingHom p q φ.toRingHom rfl
  have hf : Function.Surjective f := RingHom.surjective_localRingHom_of_surjective φ.toRingHom hφ q
  have hlocal : ringKrullDim (Localization.AtPrime q) < ringKrullDim (Localization.AtPrime p) := by
    rw [rational_localization_dimension]
    exact (le_of_eq (IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q))).trans_lt
      (q.height_le_ringKrullDim_of_isPrime.trans_lt hdim)
  obtain ⟨F, hF, j, hFj⟩ := exists_polynomial_kernel_derivative_ne_zero e f hf hlocal
  have hFzero : algebraMap A (Localization.AtPrime q) (φ F) = 0 := by
    change Localization.localRingHom p q φ.toRingHom rfl (algebraMap (MvPolynomial ι k) (Localization.AtPrime p) F) = 0 at hF
    rwa [Localization.localRingHom_to_map] at hF
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl (Localization.AtPrime q) (φ F)).mp hFzero
  obtain ⟨H, hH⟩ := hφ s
  have hsa : a s ≠ 0 := s.property
  have heF : e F = 0 := by
    have h := congrArg a hs
    rw [map_mul, map_zero] at h
    change a s * e F = 0 at h
    exact (mul_eq_zero.mp h).resolve_left hsa
  refine ⟨H * F, ?_, j, ?_⟩
  · rw [map_mul, hH]
    exact hs
  · have heH : e H ≠ 0 := by
      change a (φ H) ≠ 0
      rw [hH]
      exact hsa
    change e (MvPolynomial.pderiv j (H * F)) ≠ 0
    simpa only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, heF, zero_mul, add_zero] using
      mul_ne_zero heH hFj

end Hironaka.Algebra.ProjectiveSecant
