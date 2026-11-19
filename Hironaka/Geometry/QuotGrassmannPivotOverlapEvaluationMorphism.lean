import Hironaka.Geometry.QuotGrassmannPivotOverlapEvaluation
import Hironaka.Geometry.QuotGrassmannPivotOverlapMorphisms
import Hironaka.Geometry.QuotGrassmannPivotEvaluatedMorphism

/-!
# Actual original evaluated pivot factors through SAME original native overlap
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

/-- Actual native spectrum morphism from SAME derived overlap evaluation. -/
def originalCommonKernelOverlapEvaluationMorphism :
    Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of
      (PivotOverlapRing R ι ν (pivotIndex (coordinateSelector ι ν) p)
        (pivotIndex (coordinateSelector ι ν) t))) :=
  Spec.map (CommRingCat.ofHom (originalCommonKernelOverlapEvaluation R p t C D h))

/-- The WHOLE original left chart coefficient triangle for SAME actual native overlap spectrum morphism. -/
theorem originalCommonKernelOverlapEvaluationMorphism_left_triangle :
    originalCommonKernelOverlapEvaluationMorphism R p t C D h ≫ originalOverlapLeftMorphism R p t =
      Spec.map (CommRingCat.ofHom (originalMatrixCoefficientEvaluation R C).toRingHom) := by
  rw [originalCommonKernelOverlapEvaluationMorphism, originalOverlapLeftMorphism, ← Spec.map_comp]
  congr 1
  exact congrArg CommRingCat.ofHom (originalCommonKernelOverlapEvaluation_left_polynomial R p t C D h)

/-- SAME actual evaluated original pivot factors through SAME original native product-open scheme, internally produced from actual common quotient kernel. -/
theorem originalCommonKernelOverlapEvaluationMorphism_model_triangle :
    originalCommonKernelOverlapEvaluationMorphism R p t C D h ≫ originalOverlapModelMorphism R p t =
      originalMatrixEvaluatedPivotMorphism R p C := by
  have ht := originalOverlapLeftMorphism_triangle R p t
  change originalOverlapLeftMorphism R p t ≫ originalPivotModelMorphism R p =
    originalOverlapModelMorphism R p t at ht
  rw [← ht, ← Category.assoc, originalCommonKernelOverlapEvaluationMorphism_left_triangle]
  rfl

end Hironaka.Geometry.QuotGrassmann
