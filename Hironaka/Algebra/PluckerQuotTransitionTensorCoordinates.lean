import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# WHOLE ORIGINAL finite tensor coordinates and actual base-change cancellation

The original tensor ambient and all original scalar coefficients are retained.
No quotient, kernel or coordinate compatibility is an assumption.
-/

noncomputable section

open TensorProduct

namespace Hironaka.Algebra.PluckerQuotTransition

universe u v

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  (I : Type v) [Fintype I] [DecidableEq I]

/-- The WHOLE original tensor-coordinate scalar diagram commutes under SAME actual inverse tensor base-change cancellation. -/
theorem originalTensorCoordinate_cancelBaseChange :
    ((TensorProduct.piScalarRight A B B I).toLinearMap.comp
      ((TensorProduct.piScalarRight R A A I).toLinearMap.baseChange B)).comp
        (AlgebraTensorModule.cancelBaseChange R A B B (I → R)).symm.toLinearMap =
      (TensorProduct.piScalarRight R B B I).toLinearMap := by
  apply AlgebraTensorModule.ext
  intro b v
  funext i
  change (v i • (1 : A)) • b = v i • b
  simpa only [one_smul] using (smul_assoc (v i) (1 : A) b)

end Hironaka.Algebra.PluckerQuotTransition
