import Hironaka.Geometry.QuotGrassmannPivotEvaluatedMorphism

/-!
# ENTIRE actual original coefficient maps and evaluated pivot morphisms commute with scalars
-/

noncomputable section

open scoped Classical
open CategoryTheory AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

open Algebra.PluckerQuotTransition

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type u) [CommRing R] {A B ι ν : Type u} [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]

omit [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν] in
/-- The WHOLE actual original polynomial evaluation commutes with the SAME original scalar map and literal original matrix coefficient images. -/
theorem originalMatrixCoefficientEvaluation_comp (φ : A →ₐ[R] B) (C : Matrix ι ν A) :
    φ.comp (originalMatrixCoefficientEvaluation R C) =
      originalMatrixCoefficientEvaluation R (C.map φ) := by
  ext ij
  rcases ij with ⟨i, j⟩
  simp only [AlgHom.comp_apply, originalMatrixCoefficientEvaluation_X, Matrix.map_apply]

/-- Actual original scalar base change of the SAME actual evaluated inverse pivot morphism is its evaluation at SAME original mapped matrix coefficients. -/
theorem originalMatrixEvaluatedPivotMorphism_scalar_comp
    (φ : A →ₐ[R] B) (p : (ι ⊕ ν) ≃ (ι ⊕ ν)) (C : Matrix ι ν A) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ originalMatrixEvaluatedPivotMorphism R p C =
      originalMatrixEvaluatedPivotMorphism R p (C.map φ) := by
  rw [originalMatrixEvaluatedPivotMorphism, ← Category.assoc, ← Spec.map_comp,
    originalMatrixEvaluatedPivotMorphism]
  congr 2
  exact congrArg (fun f : ChartRing R ι ν →ₐ[R] B => CommRingCat.ofHom f.toRingHom)
    (originalMatrixCoefficientEvaluation_comp R φ C)

end Hironaka.Geometry.QuotGrassmann
