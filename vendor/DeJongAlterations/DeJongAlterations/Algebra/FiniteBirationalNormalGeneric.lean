import DeJongAlterations.Algebra.FunctionFieldDimensionGenericFiber
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# The genuine generic algebra of a finite domain extension

The actual coefficient fraction map and tensor map are reused from the
generic affine-fibre construction. Finiteness makes the tensor domain a
field and its actual fraction-field map an isomorphism.
-/

noncomputable section

open scoped TensorProduct

namespace DeJongAlterations.Algebra.FiniteBirationalNormalGeneric

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open FunctionFieldDimension

variable (R A K E : Type u) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
  [Field K] [Field E] [Algebra R A] [Algebra R K] [IsFractionRing R K]
  [Algebra R E] [Algebra A E] [IsScalarTower R A E] [IsFractionRing A E]
  [Module.Finite R A]

/-- The original fraction-field tensor map is bijective from finite base change. -/
theorem genericTensorMap_bijective (hinj : Function.Injective (algebraMap R A)) :
    Function.Bijective (genericTensorMap R A K E hinj) := by
  let G := K ⊗[R] A
  let := genericTensorAlgebra R A K E hinj
  let : IsDomain G := genericTensor_isDomain R A K hinj
  let : IsFractionRing G E := genericTensor_isFractionRing R A K E hinj
  let : Field G := (IsField.of_isDomain_of_finite K G).toField
  exact (IsFractionRing.algEquiv G G E).bijective

/-- The actual finite generic algebra is the original actual fraction field,
with its internally constructed coefficient-field scalar structure. -/
def genericTensorAlgEquiv (hinj : Function.Injective (algebraMap R A)) :
    letI := coefficientFractionAlgebra R A K E hinj
    (K ⊗[R] A) ≃ₐ[K] E := by
  let := coefficientFractionAlgebra R A K E hinj
  let := genericTensorAlgebra R A K E hinj
  let := genericTensorScalarTowerLeft R A K E hinj
  exact AlgEquiv.ofBijective (IsScalarTower.toAlgHom K (K ⊗[R] A) E)
    (genericTensorMap_bijective R A K E hinj)

/-- The isomorphism preserves the actual original pure tensor coefficients. -/
theorem genericTensorAlgEquiv_tmul (hinj : Function.Injective (algebraMap R A))
    (k : K) (a : A) :
    letI := coefficientFractionAlgebra R A K E hinj
    genericTensorAlgEquiv R A K E hinj (k ⊗ₜ[R] a) =
      coefficientFractionMap R A K E hinj k * algebraMap A E a := rfl

end DeJongAlterations.Algebra.FiniteBirationalNormalGeneric
