import DeJongAlterations.Algebra.FiniteBirationalNormalGeneric
import DeJongAlterations.Geometry.FiniteBirationalNormalLiftAffine

/-!
# The actual canonical generic affine algebra of a finite component

The generic tensor is identified with the original function field using
the original morphism's generic-stalk map, rather than a supplied scalar
comparison. Compatibility is forced by uniqueness of actual fraction lifting.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors

namespace DeJongAlterations.Geometry.FiniteBirationalNormal

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {T S : Scheme.{u}} [IsIntegral T] [IsIntegral S]
  (f : T ⟶ S) [IsDominant f] [IsFinite f]

omit [IsFinite f] in
/-- The original affine section map is injective through its actual generic-stalk triangle. -/
theorem finiteComponent_app_injective (U : NormalizationInExtension.NonemptyAffineOpen S) :
    Function.Injective (f.app U.1.1).hom := by
  apply Function.Injective.of_comp (f := (T.germToFunctionField (f ⁻¹ᵁ U.1.1)).hom)
  have H := congrArg CommRingCat.Hom.hom
    (NormalizationInExtension.functionFieldMap_sections f U.1.1)
  simp only [CommRingCat.hom_comp] at H
  change Function.Injective
    ((T.germToFunctionField (f ⁻¹ᵁ U.1.1)).hom.comp (f.app U.1.1).hom)
  rw [← H]
  exact (NormalizationInExtension.functionFieldMap f).hom.injective.comp
    (S.germToFunctionField_injective U.1.1)

/-- The actual generic finite affine algebra is the original canonical function field. -/
def finiteGenericAlgEquiv (U : NormalizationInExtension.NonemptyAffineOpen S) :
    letI := (f.app U.1.1).hom.toAlgebra
    letI := functionFieldAlgebra f
    (S.functionField ⊗[Γ(S, U.1.1)] Γ(T, f ⁻¹ᵁ U.1.1)) ≃ₐ[S.functionField] T.functionField := by
  let B := Γ(S, U.1.1)
  let A := Γ(T, f ⁻¹ᵁ U.1.1)
  let := (f.app U.1.1).hom.toAlgebra
  let := functionFieldAlgebra f
  let : IsDomain B := IsIntegral.component_integral U.1.1
  let : IsDomain A := IsIntegral.component_integral (f ⁻¹ᵁ U.1.1)
  let : IsFractionRing B S.functionField :=
    functionField_isFractionRing_of_isAffineOpen S U.1.1 U.1.2
  let : IsFractionRing A T.functionField :=
    functionField_isFractionRing_of_isAffineOpen T (f ⁻¹ᵁ U.1.1) (U.1.2.preimage f)
  let : Algebra B T.functionField :=
    ((T.germToFunctionField (f ⁻¹ᵁ U.1.1)).hom.comp (f.app U.1.1).hom).toAlgebra
  let : IsScalarTower B A T.functionField := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite B A := f.finite_app U.1.1 U.1.2
  have hK : Algebra.FunctionFieldDimension.coefficientFractionMap
      B A S.functionField T.functionField (finiteComponent_app_injective f U) =
      (NormalizationInExtension.functionFieldMap f).hom := by
    apply IsLocalization.ringHom_ext B⁰
    ext b
    rw [Algebra.FunctionFieldDimension.coefficientFractionMap, RingHom.comp_apply,
      IsFractionRing.lift_algebraMap]
    exact (congrArg (fun q : B ⟶ T.functionField => q b)
      (NormalizationInExtension.functionFieldMap_sections f U.1.1)).symm
  let e : (S.functionField ⊗[B] A) ≃+* T.functionField := by
    let := Algebra.FunctionFieldDimension.coefficientFractionAlgebra
      B A S.functionField T.functionField (finiteComponent_app_injective f U)
    exact (Algebra.FiniteBirationalNormalGeneric.genericTensorAlgEquiv
      B A S.functionField T.functionField (finiteComponent_app_injective f U)).toRingEquiv
  refine { e with commutes' := ?_ }
  intro k
  change Algebra.FunctionFieldDimension.coefficientFractionMap
    B A S.functionField T.functionField (finiteComponent_app_injective f U) k *
      algebraMap A T.functionField 1 = NormalizationInExtension.functionFieldMap f k
  rw [map_one, mul_one, hK]

/-- The canonical actual generic isomorphism retains both original coefficient maps. -/
theorem finiteGenericAlgEquiv_tmul (U : NormalizationInExtension.NonemptyAffineOpen S)
    (k : S.functionField) (a : Γ(T, f ⁻¹ᵁ U.1.1)) :
    letI := (f.app U.1.1).hom.toAlgebra
    letI := functionFieldAlgebra f
    finiteGenericAlgEquiv f U (k ⊗ₜ[Γ(S, U.1.1)] a) =
      NormalizationInExtension.functionFieldMap f k *
        T.germToFunctionField (f ⁻¹ᵁ U.1.1) a := by
  let := (f.app U.1.1).hom.toAlgebra
  let := functionFieldAlgebra f
  have h1 : finiteGenericAlgEquiv f U (1 ⊗ₜ[Γ(S, U.1.1)] a) =
      T.germToFunctionField (f ⁻¹ᵁ U.1.1) a := by
    simp [finiteGenericAlgEquiv, Algebra.FiniteBirationalNormalGeneric.genericTensorAlgEquiv,
      Algebra.FunctionFieldDimension.genericTensorAlgebra, RingHom.algebraMap_toAlgebra,
      Algebra.FunctionFieldDimension.genericTensorMap]
  have H : k ⊗ₜ[Γ(S, U.1.1)] a = k • (1 ⊗ₜ[Γ(S, U.1.1)] a) := by
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [H, map_smul, h1]
  rfl

end DeJongAlterations.Geometry.FiniteBirationalNormal
