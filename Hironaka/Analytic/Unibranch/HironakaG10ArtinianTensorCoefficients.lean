import Hironaka.Analytic.Unibranch.HironakaG10FlatComplexScalarExtension
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Algebra.Module.TransferInstance

/-! # Finite coefficient model for an Artinian-parameter scalar extension -/
set_option autoImplicit false
open scoped TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10ArtinianTensorCoefficients

noncomputable section

/-- A finite basis of the parameter algebra identifies its scalar extension
  of any complex vector space with finitely many coefficient vectors. -/
def parameterTensorEquiv {A E ι : Type*} [CommRing A] [Algebra ℂ A]
    [AddCommGroup E] [Module ℂ E] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ A) : (A ⊗[ℂ] E) ≃ₗ[ℂ] (ι → E) :=
  (TensorProduct.comm ℂ A E).trans
    ((TensorProduct.congr (LinearEquiv.refl ℂ E) b.equivFun).trans
      (TensorProduct.piScalarRight ℂ ℂ E ι))

/-- Pure tensors have the expected basis coefficients. -/
theorem parameterTensorEquiv_tmul {A E ι : Type*} [CommRing A] [Algebra ℂ A]
    [AddCommGroup E] [Module ℂ E] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ A) (a : A) (v : E) (i : ι) :
    parameterTensorEquiv b (a ⊗ₜ[ℂ] v) i = (b.equivFun a i) • v := by
  simp [parameterTensorEquiv]

/-- The coefficient vectors inherit the actual parameter-algebra module
  structure transported from scalar extension. -/
@[instance_reducible] def parameterCoefficientModule {A E ι : Type*} [CommRing A] [Algebra ℂ A]
    [AddCommGroup E] [Module ℂ E] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ A) : Module A (ι → E) :=
  (parameterTensorEquiv b).symm.toAddEquiv.module A

/-- The finite coefficient model is the same full scalar extension as an
  `A`-module, retaining its ordinary coordinatewise additive structure. -/
def parameterCoefficientLinearEquiv {A E ι : Type*} [CommRing A] [Algebra ℂ A]
    [AddCommGroup E] [Module ℂ E] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ A) :
    letI := parameterCoefficientModule (E := E) b
    (ι → E) ≃ₗ[A] (A ⊗[ℂ] E) := by
  letI := parameterCoefficientModule (E := E) b
  exact (parameterTensorEquiv b).symm.toAddEquiv.linearEquiv A

/-- The transported parameter action is compatible with the original
  coordinatewise complex vector-space structure. -/
theorem parameterCoefficient_scalarTower {A E ι : Type*} [CommRing A] [Algebra ℂ A]
    [AddCommGroup E] [Module ℂ E] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ A) :
    letI := parameterCoefficientModule (E := E) b
    IsScalarTower ℂ A (ι → E) := by
  let := parameterCoefficientModule (E := E) b
  exact LinearEquiv.isScalarTower A (parameterTensorEquiv b).symm

/-- The finite coefficient Banach-model carrier is automatically flat
  for its actual transported parameter-algebra structure. -/
theorem parameterCoefficient_flat {A E ι : Type*} [CommRing A] [Algebra ℂ A]
    [AddCommGroup E] [Module ℂ E] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ A) :
    letI := parameterCoefficientModule (E := E) b
    Module.Flat A (ι → E) := by
  let := parameterCoefficientModule (E := E) b
  exact Hironaka.Analytic.Unibranch.HironakaG10FlatComplexScalarExtension.flat_of_complex_tensor_equiv
    (parameterCoefficientLinearEquiv b)

end
end Hironaka.Analytic.Unibranch.HironakaG10ArtinianTensorCoefficients
