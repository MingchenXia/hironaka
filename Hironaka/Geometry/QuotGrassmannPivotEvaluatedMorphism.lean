import Hironaka.Geometry.QuotGrassmannPivotGlobalPullbackSections
import Hironaka.Algebra.PluckerQuotTransitionPivotEvaluation

/-!
# The actual original evaluated polynomial pivot morphism over its original base
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

open Algebra.PluckerQuotTransition

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type u) [CommRing R] {A ι ν : Type u} [CommRing A] [Algebra R A]
  [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]
  (p : (ι ⊕ ν) ≃ (ι ⊕ ν)) (C : Matrix ι ν A)

/-- The actual ORIGINAL polynomial evaluation followed by ORIGINAL pivot immersion into SAME original projective model. -/
def originalMatrixEvaluatedPivotMorphism : Spec (CommRingCat.of A) ⟶ projectiveModel R ι ν :=
  Spec.map (CommRingCat.ofHom (originalMatrixCoefficientEvaluation R C).toRingHom) ≫
    originalPivotModelMorphism R p

/-- SAME actual evaluated original pivot is a morphism over the ORIGINAL coefficient spectrum, with no supplied structure triangle. -/
theorem originalMatrixEvaluatedPivotMorphism_structure :
    originalMatrixEvaluatedPivotMorphism R p C ≫ projectiveStructure R ι ν =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  rw [originalMatrixEvaluatedPivotMorphism, Category.assoc, originalPivotModelMorphism_structure,
    ← Spec.map_comp]
  congr 1
  exact congrArg CommRingCat.ofHom (originalMatrixCoefficientEvaluation_coeff R C)

end Hironaka.Geometry.QuotGrassmann
