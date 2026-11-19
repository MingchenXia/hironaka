import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Data.Complex.Basic

/-! # Flatness of scalar-extended complex vector spaces -/
set_option autoImplicit false
open scoped TensorProduct

namespace Hironaka.Analytic.Unibranch.HironakaG10FlatComplexScalarExtension

/-- A scalar extension of any complex vector space is free, hence flat, over
  the parameter algebra; no finite-dimensionality is required. -/
theorem flat_tensor_complex {A E : Type*} [CommRing A] [Algebra ℂ A]
    [AddCommGroup E] [Module ℂ E] : Module.Flat A (A ⊗[ℂ] E) := by
  infer_instance

/-- Any parameter module identified with such a scalar extension is flat. -/
theorem flat_of_complex_tensor_equiv {A E M : Type*} [CommRing A] [Algebra ℂ A]
    [AddCommGroup E] [Module ℂ E] [AddCommGroup M] [Module A M]
    (e : M ≃ₗ[A] A ⊗[ℂ] E) : Module.Flat A M := by
  let : Module.Flat A (A ⊗[ℂ] E) := flat_tensor_complex
  exact Module.Flat.of_linearEquiv e

end Hironaka.Analytic.Unibranch.HironakaG10FlatComplexScalarExtension
