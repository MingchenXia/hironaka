import Hironaka.Geometry.QuotGrassmannPivotEvaluatedNaturality
import Hironaka.Geometry.QuotGrassmannPivotEvaluatedInjectivity

/-! Actual evaluated inverse charts agree on a genuine common original coefficient cocone. -/

noncomputable section

open scoped Classical TensorProduct
open CategoryTheory AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type u) [CommRing R] {A A₁ A₂ B ι ν : Type u}
  [CommRing A] [CommRing A₁] [CommRing A₂] [CommRing B]
  [Algebra R A] [Algebra R A₁] [Algebra R A₂] [Algebra R B]
  [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]

/-- A common ORIGINAL native quotient and a genuinely commuting original coefficient
cocone determine equal ACTUAL inverse pivot morphisms, without an overlap-map certificate. -/
theorem originalMatrixEvaluatedPivotMorphism_eq_of_common_cocone
    (N : Module.Grassmannian A (A ⊗[R] ((ι ⊕ ν) → R)) (Fintype.card ι))
    (α₁ : A →ₐ[R] A₁) (α₂ : A →ₐ[R] A₂)
    (φ₁ : A₁ →ₐ[R] B) (φ₂ : A₂ →ₐ[R] B)
    (hcomp : φ₁.comp α₁ = φ₂.comp α₂)
    (p t : (ι ⊕ ν) ≃ (ι ⊕ ν)) (C : Matrix ι ν A₁) (D : Matrix ι ν A₂)
    (hC : originalGlobalAffineGrassmannianTensorPoint R ι ν
      (originalMatrixEvaluatedPivotMorphism R p C) = Module.Grassmannian.map α₁ N)
    (hD : originalGlobalAffineGrassmannianTensorPoint R ι ν
      (originalMatrixEvaluatedPivotMorphism R t D) = Module.Grassmannian.map α₂ N) :
    Spec.map (CommRingCat.ofHom φ₁.toRingHom) ≫ originalMatrixEvaluatedPivotMorphism R p C =
      Spec.map (CommRingCat.ofHom φ₂.toRingHom) ≫ originalMatrixEvaluatedPivotMorphism R t D := by
  rw [originalMatrixEvaluatedPivotMorphism_scalar_comp,
    originalMatrixEvaluatedPivotMorphism_scalar_comp]
  apply originalMatrixEvaluatedPivotMorphism_eq_of_classifier_eq
  have h₁ := originalGlobalAffineGrassmannianTensorPoint_map R ι ν
    (A := CommRingCat.of A₁) (B := CommRingCat.of B) φ₁
    (originalMatrixEvaluatedPivotMorphism R p C)
  have h₂ := originalGlobalAffineGrassmannianTensorPoint_map R ι ν
    (A := CommRingCat.of A₂) (B := CommRingCat.of B) φ₂
    (originalMatrixEvaluatedPivotMorphism R t D)
  rw [hC, ← Module.Grassmannian.map_comp,
    originalMatrixEvaluatedPivotMorphism_scalar_comp] at h₁
  rw [hD, ← Module.Grassmannian.map_comp,
    originalMatrixEvaluatedPivotMorphism_scalar_comp] at h₂
  exact h₁.symm.trans ((congrArg (fun φ => Module.Grassmannian.map φ N) hcomp).trans h₂)

end Hironaka.Geometry.QuotGrassmann
