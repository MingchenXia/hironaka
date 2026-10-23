import DeJongAlterations.Algebra.AffinePrimeDimensionMaximal
import DeJongAlterations.Algebra.FunctionFieldDimensionGenericFiber
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Genuine generic-localization height bounds from a finite prime quotient

When the original quotient is finite over an injective coefficient
domain, localizing at that coefficient domain makes it a field. Its
actual kernel is maximal and contracts to the original prime. Native
localization heights and actual maximal heights then compute the
dimension of the original generic tensor algebra.
-/

noncomputable section

open scoped TensorProduct

namespace DeJongAlterations.Algebra.AffinePrimeDimension

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (R A F : Type u) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
  [Field F] [Algebra R A] [Algebra R F] [IsFractionRing R F]
  [Algebra.FiniteType R A]
  (p : Ideal A) [p.IsPrime] [Module.Finite R (A ⧸ p)]

/-- The generic tensor dimension equals the actual original prime height.
Coefficient injectivity into the finite quotient is a natural algebra hypothesis. -/
theorem genericTensor_dimension_eq_height
    (hinj : Function.Injective (algebraMap R (A ⧸ p))) :
    ringKrullDim (F ⊗[R] A) = (p.height : WithBot ℕ∞) := by
  have hRA : Function.Injective (algebraMap R A) := by
    intro a b h
    apply hinj
    exact congrArg (algebraMap A (A ⧸ p)) h
  let B := F ⊗[R] A
  let C := F ⊗[R] (A ⧸ p)
  let : IsDomain B := FunctionFieldDimension.genericTensor_isDomain R A F hRA
  let : IsDomain C := FunctionFieldDimension.genericTensor_isDomain R (A ⧸ p) F hinj
  let : Field C := (IsField.of_isDomain_of_finite F C).toField
  let φ : B →ₐ[F] C := Algebra.TensorProduct.map (AlgHom.id F F) (Ideal.Quotient.mkₐ R p)
  have hsurj : Function.Surjective φ :=
    Algebra.TensorProduct.map_surjective (AlgHom.id F F) (Ideal.Quotient.mkₐ R p)
      Function.surjective_id Ideal.Quotient.mk_surjective
  let q := RingHom.ker φ.toRingHom
  let : q.IsMaximal := RingHom.ker_isMaximal_of_surjective φ.toRingHom hsurj
  have hCinj : Function.Injective (algebraMap (A ⧸ p) C) :=
    IsLocalization.injective C (FunctionFieldDimension.coefficient_nonZeroDivisors_le R (A ⧸ p) hinj)
  have hq : q.under A = p := by
    ext a
    change φ (algebraMap A B a) = 0 ↔ a ∈ p
    change (1 : F) ⊗ₜ[R] (Ideal.Quotient.mk p a) = 0 ↔ a ∈ p
    change algebraMap (A ⧸ p) C (Ideal.Quotient.mk p a) = 0 ↔ a ∈ p
    rw [map_eq_zero_iff _ hCinj, Ideal.Quotient.eq_zero_iff_mem]
  have hheight : q.height = p.height := by
    rw [← IsLocalization.height_under (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) q, hq]
  rw [← maximalHeight_eq_ringKrullDim F B q, hheight]

end DeJongAlterations.Algebra.AffinePrimeDimension
