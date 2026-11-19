import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Actual scalar base change of SAME original finite-coordinate quotient

The actual native tensor/localization target isomorphism and the genuine
original scalar-coordinate source inverse construct the entire map. Every
original unit coordinate has its literal original localized quotient value.
-/

noncomputable section

open TensorProduct

namespace Hironaka.Algebra.PluckerQuotTransition

universe u v w

variable {A : Type u} [CommRing A]
  {M : Type v} [AddCommGroup M] [Module A M]
  {E : Type w} [Fintype E] [DecidableEq E]
  (q : (E → A) →ₗ[A] M) (S : Submonoid A)

/-- SAME original actual quotient after native scalar extension, original source coordinate inverse and actual native localized target comparison. -/
def originalLocalizedCoordinateQuotient :
    (E → Localization S) →ₗ[Localization S] LocalizedModule S M :=
  (LocalizedModule.equivTensorProduct S M).symm.toLinearMap.comp
    ((q.baseChange (Localization S)).comp
      (TensorProduct.piScalarRight A (Localization S) (Localization S) E).symm.toLinearMap)

/-- EVERY ORIGINAL coordinate unit gives SAME literal localization of its ORIGINAL quotient column. -/
theorem originalLocalizedCoordinateQuotient_single (j : E) :
    originalLocalizedCoordinateQuotient q S (Pi.single j (1 : Localization S)) =
      LocalizedModule.mkLinearMap S M (q (Pi.single j (1 : A))) := by
  simp only [originalLocalizedCoordinateQuotient, LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.piScalarRight_symm_single, LinearMap.baseChange_tmul,
    LocalizedModule.equivTensorProduct_symm_apply_tmul_one, LocalizedModule.mkLinearMap_apply]

/-- The WHOLE actual original localized quotient satisfies its genuine tensor source and SAME native localized-target comparison triangle. -/
theorem originalLocalizedCoordinateQuotient_tensor_triangle :
    (originalLocalizedCoordinateQuotient q S).comp
        (TensorProduct.piScalarRight A (Localization S) (Localization S) E).toLinearMap =
      (LocalizedModule.equivTensorProduct S M).symm.toLinearMap.comp
        (q.baseChange (Localization S)) := by
  apply LinearMap.ext
  intro u
  exact congrArg (fun v => (LocalizedModule.equivTensorProduct S M).symm
      (q.baseChange (Localization S) v))
    ((TensorProduct.piScalarRight A (Localization S) (Localization S) E).symm_apply_apply u)

end Hironaka.Algebra.PluckerQuotTransition
