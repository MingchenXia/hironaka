import Hironaka.Algebra.PluckerQuotTransitionLocalizedQuotient
import Hironaka.Algebra.PluckerQuotTransitionTensorCoordinates
import Hironaka.Algebra.GrassmannQuotientKernel

/-!
# The WHOLE original localized quotient retains the actual original tensor source

The SAME original scalar-coordinate cancellation, whole tensor base change
and actual native localized-target isomorphism are compared as whole maps.
-/

noncomputable section

open TensorProduct

namespace Hironaka.Algebra.PluckerQuotTransition

universe u v w

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (S : Submonoid A)
  {M : Type v} [AddCommGroup M] [Module A M]
  (E : Type w) [Fintype E] [DecidableEq E] (q : (E → A) →ₗ[A] M)

/-- The WHOLE SAME original localized quotient on the original tensor source is actual tensor base change followed by the SAME native inverse localized-target isomorphism. -/
theorem originalLocalizedCoordinateQuotient_originalTensor_triangle :
    (originalLocalizedCoordinateQuotient q S).comp
      (TensorProduct.piScalarRight R (Localization S) (Localization S) E).toLinearMap =
      (LocalizedModule.equivTensorProduct S M).symm.toLinearMap.comp
        (GrassmannQuotientKernel.changedQuotient (B := Localization S)
          (q.comp (TensorProduct.piScalarRight R A A E).toLinearMap)) := by
  have h := originalTensorCoordinate_cancelBaseChange R A (Localization S) E
  have hinv :
      (TensorProduct.piScalarRight A (Localization S) (Localization S) E).symm.toLinearMap.comp
        (TensorProduct.piScalarRight R (Localization S) (Localization S) E).toLinearMap =
      ((TensorProduct.piScalarRight R A A E).toLinearMap.baseChange (Localization S)).comp
        (AlgebraTensorModule.cancelBaseChange R A (Localization S) (Localization S) (E → R)).symm.toLinearMap := by
    apply LinearMap.ext
    intro z
    have hz := LinearMap.congr_fun h z
    exact (congrArg (TensorProduct.piScalarRight A (Localization S) (Localization S) E).symm
      hz.symm).trans ((TensorProduct.piScalarRight A (Localization S) (Localization S) E).symm_apply_apply _)
  simp only [originalLocalizedCoordinateQuotient, GrassmannQuotientKernel.changedQuotient,
    LinearMap.baseChange_comp, LinearMap.comp_assoc, hinv]

end Hironaka.Algebra.PluckerQuotTransition
