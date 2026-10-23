import DeJongAlterations.Algebra.FunctionFieldDimension
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.FiniteStability

/-!
# The actual fraction field of a generic affine fibre ring

The coefficient fraction map and tensor map are constructed from the actual
algebra maps. The generic tensor algebra is a genuine localization of the
original domain; its domain and fraction-field properties are proved here.
-/

noncomputable section

open scoped TensorProduct

namespace DeJongAlterations.Algebra.FunctionFieldDimension

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (R A F K : Type u) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
  [Field F] [Field K] [Algebra R A] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra A K] [IsScalarTower R A K] [IsFractionRing A K]

/-- The canonical fraction-field map extends the actual coefficient inclusion. -/
def coefficientFractionMap (hinj : Function.Injective (algebraMap R A)) : F →+* K :=
  IsFractionRing.lift (g := algebraMap R K) (by
    rw [IsScalarTower.algebraMap_eq R A K]
    exact (IsFractionRing.injective A K).comp hinj)

abbrev coefficientFractionAlgebra (hinj : Function.Injective (algebraMap R A)) : Algebra F K :=
  (coefficientFractionMap R A F K hinj).toAlgebra

omit [IsDomain R] [IsDomain A] in
theorem coefficientFractionScalarTower (hinj : Function.Injective (algebraMap R A)) :
    letI := coefficientFractionAlgebra R A F K hinj
    IsScalarTower R F K := by
  let := coefficientFractionAlgebra R A F K hinj
  have hRK : Function.Injective (algebraMap R K) := by
    rw [IsScalarTower.algebraMap_eq R A K]
    exact (IsFractionRing.injective A K).comp hinj
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change algebraMap R K a = IsFractionRing.lift hRK (algebraMap R F a)
  exact (IsFractionRing.lift_algebraMap hRK a).symm

/-- The native tensor lift into the actual original function field. -/
def genericTensorMap (hinj : Function.Injective (algebraMap R A)) : (F ⊗[R] A) →+* K := by
  let := coefficientFractionAlgebra R A F K hinj
  let := coefficientFractionScalarTower R A F K hinj
  exact (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R F K)
    (IsScalarTower.toAlgHom R A K) fun _ _ ↦ Commute.all _ _).toRingHom

abbrev genericTensorAlgebra (hinj : Function.Injective (algebraMap R A)) :
    Algebra (F ⊗[R] A) K := (genericTensorMap R A F K hinj).toAlgebra

omit [IsDomain R] [IsDomain A] in
theorem genericTensorScalarTowerRight (hinj : Function.Injective (algebraMap R A)) :
    letI := genericTensorAlgebra R A F K hinj
    IsScalarTower A (F ⊗[R] A) K := by
  let := genericTensorAlgebra R A F K hinj
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change algebraMap A K a = genericTensorMap R A F K hinj (1 ⊗ₜ[R] a)
  simp [genericTensorMap]

omit [IsDomain R] [IsDomain A] in
theorem genericTensorScalarTowerLeft (hinj : Function.Injective (algebraMap R A)) :
    letI := coefficientFractionAlgebra R A F K hinj
    letI := genericTensorAlgebra R A F K hinj
    IsScalarTower F (F ⊗[R] A) K := by
  let := coefficientFractionAlgebra R A F K hinj
  let := genericTensorAlgebra R A F K hinj
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change coefficientFractionMap R A F K hinj a = genericTensorMap R A F K hinj (a ⊗ₜ[R] 1)
  simp [genericTensorMap]
  rfl

theorem coefficient_nonZeroDivisors_le (hinj : Function.Injective (algebraMap R A)) :
    Algebra.algebraMapSubmonoid A (nonZeroDivisors R) ≤ nonZeroDivisors A := by
  rintro x ⟨r, hr, rfl⟩
  apply mem_nonZeroDivisors_iff_ne_zero.mpr
  intro heq
  exact mem_nonZeroDivisors_iff_ne_zero.mp hr (hinj (by simpa using heq))

/-- The actual generic tensor algebra is a domain, derived from coefficient injectivity. -/
theorem genericTensor_isDomain (hinj : Function.Injective (algebraMap R A)) :
    IsDomain (F ⊗[R] A) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (F ⊗[R] A)
    (coefficient_nonZeroDivisors_le R A hinj)

/-- The constructed actual tensor map makes the original fraction field its fraction field. -/
theorem genericTensor_isFractionRing (hinj : Function.Injective (algebraMap R A)) :
    letI := genericTensorAlgebra R A F K hinj
    IsFractionRing (F ⊗[R] A) K := by
  let := genericTensorAlgebra R A F K hinj
  let := genericTensorScalarTowerRight R A F K hinj
  exact IsFractionRing.isFractionRing_of_isLocalization
    (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) (F ⊗[R] A) K
      (coefficient_nonZeroDivisors_le R A hinj)

/-- The genuine finite-type generic affine fibre dimension is determined by relative field degree. -/
theorem genericTensor_dimension_eq [Algebra.FiniteType R A]
    (hinj : Function.Injective (algebraMap R A)) (d : ℕ)
    (htr : letI := coefficientFractionAlgebra R A F K hinj; Algebra.trdeg F K = d) :
    ringKrullDim (F ⊗[R] A) = d := by
  let := coefficientFractionAlgebra R A F K hinj
  let := genericTensorAlgebra R A F K hinj
  let := genericTensorScalarTowerLeft R A F K hinj
  have : IsDomain (F ⊗[R] A) := genericTensor_isDomain R A F hinj
  have : IsFractionRing (F ⊗[R] A) K := genericTensor_isFractionRing R A F K hinj
  exact ringKrullDim_eq_of_trdeg_eq_nat F (F ⊗[R] A) K d htr

end DeJongAlterations.Algebra.FunctionFieldDimension
