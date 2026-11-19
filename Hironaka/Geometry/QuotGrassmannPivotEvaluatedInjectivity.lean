import Hironaka.Geometry.QuotGrassmannPivotOverlapRightMorphism
import Hironaka.Geometry.QuotGrassmannPivotEvaluatedClassifier
import Hironaka.Algebra.PluckerQuotTransitionKernelSource

/-!
# Actual native classifier equality forces equality of actual original inverse pivot morphisms
-/

noncomputable section

open scoped Classical TensorProduct

namespace Hironaka.Geometry.QuotGrassmann

open Algebra.PluckerQuot Algebra.PluckerQuotTransition

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type u) [CommRing R] {A ι ν : Type u} [CommRing A] [Algebra R A]
  [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]

/-- Equality of the ACTUAL native original quotient classifiers INTERNALLY derives the original coordinate kernel and both native overlap triangles, hence equality of ACTUAL original evaluated inverse pivot scheme morphisms. -/
theorem originalMatrixEvaluatedPivotMorphism_eq_of_classifier_eq
    (p t : (ι ⊕ ν) ≃ (ι ⊕ ν)) (C D : Matrix ι ν A)
    (h : originalGlobalAffineGrassmannianTensorPoint R ι ν (originalMatrixEvaluatedPivotMorphism R p C) =
      originalGlobalAffineGrassmannianTensorPoint R ι ν (originalMatrixEvaluatedPivotMorphism R t D)) :
    originalMatrixEvaluatedPivotMorphism R p C = originalMatrixEvaluatedPivotMorphism R t D := by
  have hk := congrArg Module.Grassmannian.toSubmodule h
  rw [originalMatrixEvaluatedPivotClassifier_toSubmodule,
    originalMatrixEvaluatedPivotClassifier_toSubmodule] at hk
  have hcoords := originalKernel_eq_of_comp_sourceEquiv (TensorProduct.piScalarRight R A A (ι ⊕ ν))
    (splitNormalizedMatrix p C).mulVecLin (splitNormalizedMatrix t D).mulVecLin hk
  exact originalMatrixEvaluatedPivotMorphism_eq_of_commonKernel R p t C D hcoords

end Hironaka.Geometry.QuotGrassmann
