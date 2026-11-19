import Hironaka.Algebra.GrassmannQuotientKernel
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# WHOLE original matrix tensor quotient under actual scalar base change
-/

noncomputable section

open TensorProduct

namespace Hironaka.Algebra.PluckerQuotTransition

universe u v w

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  {I : Type v} [Fintype I] [DecidableEq I]
  {E : Type w} [Fintype E] [DecidableEq E] (C : Matrix I E A)

/-- The ENTIRE actual changed original matrix tensor quotient has the SAME original coefficients evaluated by the actual algebra map, under the genuine native free-target scalar isomorphism. -/
theorem originalMatrixTensorQuotient_baseChange_triangle :
    (TensorProduct.piScalarRight A B B I).toLinearMap.comp
      (GrassmannQuotientKernel.changedQuotient (B := B)
        (C.mulVecLin.comp (TensorProduct.piScalarRight R A A E).toLinearMap)) =
      (C.map (algebraMap A B)).mulVecLin.comp
        (TensorProduct.piScalarRight R B B E).toLinearMap := by
  apply AlgebraTensorModule.ext
  intro b v
  funext i
  change (∑ j, C i j * (v j • (1 : A))) • b =
    ∑ j, algebraMap A B (C i j) * (v j • b)
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_smul]
  rw [← Algebra.smul_def (C i j) (v j • b)]
  exact congrArg (fun z : B => C i j • z)
    (by simpa only [one_smul] using (smul_assoc (v j) (1 : A) b))

end Hironaka.Algebra.PluckerQuotTransition
