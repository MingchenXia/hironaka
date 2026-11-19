import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.TensorProduct.Maps

/-! Literal original closed-fibre tensor comparison, retaining EVERY representative. -/

noncomputable section

open TensorProduct

namespace Hironaka.Algebra.NodeGeometricCompletionFiberTensor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
variable (A : Type u) [CommRing A] (R : Type v) [CommRing R] [Algebra A R]
  (I : Ideal A) (L : Type w) [CommRing L] [Algebra A L] [Algebra (A ⧸ I) L]
  [IsScalarTower A (A ⧸ I) L]

/-- The whole literal closed-fibre tensor is the original tensor over the original base. -/
def tensorEquiv :
    (L ⊗[A ⧸ I] (R ⧸ I.map (algebraMap A R))) ≃ₐ[L] (L ⊗[A] R) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L)
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor R I)).trans
      (Algebra.TensorProduct.cancelBaseChange A (A ⧸ I) L L R)

/-- Every scalar and every original representative retain their literal actual image. -/
theorem tensorEquiv_tmul (l : L) (r : R) :
    tensorEquiv A R I L (l ⊗ₜ[A ⧸ I] Ideal.Quotient.mk (I.map (algebraMap A R)) r) =
      l ⊗ₜ[A] r := by
  change Algebra.TensorProduct.cancelBaseChange A (A ⧸ I) L L R
    (l ⊗ₜ[A ⧸ I] (Algebra.TensorProduct.quotIdealMapEquivQuotTensor R I
      (Ideal.Quotient.mk (I.map (algebraMap A R)) r))) = _
  rw [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk,
    Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]

/-- The inverse also preserves EVERY actual original tensor representative. -/
theorem tensorEquiv_symm_tmul (l : L) (r : R) :
    (tensorEquiv A R I L).symm (l ⊗ₜ[A] r) =
      l ⊗ₜ[A ⧸ I] Ideal.Quotient.mk (I.map (algebraMap A R)) r := by
  apply (tensorEquiv A R I L).injective
  rw [AlgEquiv.apply_symm_apply, tensorEquiv_tmul]

end Hironaka.Algebra.NodeGeometricCompletionFiberTensor
