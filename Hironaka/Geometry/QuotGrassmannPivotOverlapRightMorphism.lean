import Hironaka.Geometry.QuotGrassmannPivotOverlapRightPolynomial
import Hironaka.Geometry.QuotGrassmannPivotOverlapEvaluationMorphism

/-!
# BOTH actual original overlap triangles and actual inverse pivot morphism equality
-/

noncomputable section

open scoped Classical
open CategoryTheory AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

open Algebra.PluckerQuot Algebra.PluckerQuotTransition

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type u) [CommRing R] {A ι ν : Type u} [CommRing A] [Algebra R A]
  [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]
  (p t : (ι ⊕ ν) ≃ (ι ⊕ ν)) (C D : Matrix ι ν A)
  (h : (splitNormalizedMatrix p C).mulVecLin.ker = (splitNormalizedMatrix t D).mulVecLin.ker)

/-- The WHOLE original right chart coefficient triangle for SAME actual derived overlap spectrum morphism. -/
theorem originalCommonKernelOverlapEvaluationMorphism_right_triangle :
    originalCommonKernelOverlapEvaluationMorphism R p t C D h ≫ originalOverlapRightMorphism R p t =
      Spec.map (CommRingCat.ofHom (originalMatrixCoefficientEvaluation R D).toRingHom) := by
  rw [originalCommonKernelOverlapEvaluationMorphism, originalOverlapRightMorphism, ← Spec.map_comp]
  congr 1
  exact congrArg CommRingCat.ofHom (originalCommonKernelOverlapEvaluation_right_polynomial R p t C D h)

/-- SAME actual right evaluated original pivot factors through the SAME actual original native product open as the left pivot. -/
theorem originalCommonKernelOverlapEvaluationMorphism_right_model_triangle :
    originalCommonKernelOverlapEvaluationMorphism R p t C D h ≫ originalOverlapModelMorphism R p t =
      originalMatrixEvaluatedPivotMorphism R t D := by
  have ht := originalOverlapRightMorphism_triangle R p t
  change originalOverlapRightMorphism R p t ≫ originalPivotModelMorphism R t =
    originalOverlapModelMorphism R p t at ht
  rw [← ht, ← Category.assoc, originalCommonKernelOverlapEvaluationMorphism_right_triangle]
  rfl

include h in
/-- ACTUAL original evaluated inverse pivot scheme morphisms of the SAME entire original quotient kernel are equal in SAME original projective model; BOTH whole native overlap factorizations are internally derived. -/
theorem originalMatrixEvaluatedPivotMorphism_eq_of_commonKernel :
    originalMatrixEvaluatedPivotMorphism R p C = originalMatrixEvaluatedPivotMorphism R t D :=
  (originalCommonKernelOverlapEvaluationMorphism_model_triangle R p t C D h).symm.trans
    (originalCommonKernelOverlapEvaluationMorphism_right_model_triangle R p t C D h)

end Hironaka.Geometry.QuotGrassmann
