import DeJongAlterations.Algebra.ProjectiveLinearCoordinatesPolynomial
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The entire actual polynomial automorphism internally induced by an original linear equivalence
-/

noncomputable section

open MvPolynomial

namespace DeJongAlterations.Algebra.ProjectiveLinearCoordinates

universe u v w t

variable (k : Type u) [Field k]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The exact original row linear forms of the original matrix. -/
def matrixForm {ι : Type v} {κ : Type w} [Fintype κ] (A : Matrix ι κ k) (i : ι) : MvPolynomial κ k :=
  ∑ j, C (A i j) * X j

/-- The entire polynomial substitution of the exact original matrix forms. -/
def matrixPolynomialMap {ι : Type v} {κ : Type w} [Fintype κ] (A : Matrix ι κ k) :
    MvPolynomial ι k →ₐ[k] MvPolynomial κ k :=
  MvPolynomial.aeval (matrixForm k A)

/-- The entire actual polynomial substitution composition is exactly the actual original matrix product. -/
theorem matrixPolynomialMap_comp
    {ι : Type v} {κ : Type w} {τ : Type t} [Fintype κ] [Fintype τ] (A : Matrix ι κ k) (B : Matrix κ τ k) :
    (matrixPolynomialMap k B).comp (matrixPolynomialMap k A) = matrixPolynomialMap k (A * B) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, matrixPolynomialMap, aeval_X, matrixForm, map_sum, map_mul,
    aeval_C, aeval_X, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, map_sum, mul_assoc]
  rw [Finset.sum_comm]
  rfl

/-- The actual identity matrix gives the entire identity polynomial map. -/
theorem matrixPolynomialMap_one {ι : Type v} [Fintype ι] [DecidableEq ι] :
    matrixPolynomialMap k (1 : Matrix ι ι k) = AlgHom.id k _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [matrixPolynomialMap, matrixForm, Matrix.one_apply]

/-- The exact standard-basis matrix of the original inverse linear map cancels the original matrix. -/
theorem linearEquiv_matrix_symm_mul {ι : Type v} [Fintype ι] [DecidableEq ι]
    (e : (ι → k) ≃ₗ[k] (ι → k)) :
    LinearMap.toMatrix' e.symm.toLinearMap * LinearMap.toMatrix' e.toLinearMap = 1 := by
  rw [← LinearMap.toMatrix'_comp]
  have h : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact e.symm_apply_apply x
  rw [h, LinearMap.toMatrix'_id]

/-- The actual entire polynomial automorphism constructed from the original actual linear equivalence, with its inverse produced internally. -/
def linearPolynomialEquiv {ι : Type v} [Fintype ι] [DecidableEq ι]
    (e : (ι → k) ≃ₗ[k] (ι → k)) : MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k where
  __ := matrixPolynomialMap k (LinearMap.toMatrix' e.toLinearMap)
  invFun := matrixPolynomialMap k (LinearMap.toMatrix' e.symm.toLinearMap)
  left_inv F := by
    have h := matrixPolynomialMap_comp k (LinearMap.toMatrix' e.toLinearMap) (LinearMap.toMatrix' e.symm.toLinearMap)
    have hi := linearEquiv_matrix_symm_mul k e.symm
    simp only [LinearEquiv.symm_symm] at hi
    rw [hi, matrixPolynomialMap_one] at h
    exact AlgHom.congr_fun h F
  right_inv F := by
    have h := matrixPolynomialMap_comp k (LinearMap.toMatrix' e.symm.toLinearMap) (LinearMap.toMatrix' e.toLinearMap)
    rw [linearEquiv_matrix_symm_mul k e, matrixPolynomialMap_one] at h
    exact AlgHom.congr_fun h F

/-- Evaluating every original coordinate form recovers the SAME original entire linear map on every original vector. -/
theorem eval_linearPolynomialEquiv_X {ι : Type v} [Fintype ι] [DecidableEq ι]
    (e : (ι → k) ≃ₗ[k] (ι → k)) (x : ι → k) (i : ι) :
    MvPolynomial.eval x (linearPolynomialEquiv k e (X i)) = e x i := by
  change MvPolynomial.eval x (matrixPolynomialMap k (LinearMap.toMatrix' e.toLinearMap) (X i)) = _
  simp only [matrixPolynomialMap, aeval_X, matrixForm, map_sum, map_mul, eval_C, eval_X]
  exact congrFun (LinearMap.toMatrix'_mulVec e.toLinearMap x) i

/-- The exact entire polynomial substitution of the actual composite is the literal contravariant whole-ring composite. -/
theorem linearPolynomialEquiv_trans {ι : Type v} [Fintype ι] [DecidableEq ι]
    (e f : (ι → k) ≃ₗ[k] (ι → k)) :
    (linearPolynomialEquiv k (e.trans f)).toAlgHom =
      (linearPolynomialEquiv k e).toAlgHom.comp (linearPolynomialEquiv k f).toAlgHom := by
  change matrixPolynomialMap k (LinearMap.toMatrix' (f.toLinearMap.comp e.toLinearMap)) =
    (matrixPolynomialMap k (LinearMap.toMatrix' e.toLinearMap)).comp
      (matrixPolynomialMap k (LinearMap.toMatrix' f.toLinearMap))
  rw [LinearMap.toMatrix'_comp, matrixPolynomialMap_comp]

/-- Evaluation of the SAME entire original polynomial substitution is the SAME original polynomial evaluated at the original entire linear-map value. -/
theorem eval_linearPolynomialEquiv {ι : Type v} [Fintype ι] [DecidableEq ι]
    (e : (ι → k) ≃ₗ[k] (ι → k)) (x : ι → k) (F : MvPolynomial ι k) :
    MvPolynomial.eval x (linearPolynomialEquiv k e F) = MvPolynomial.eval (e x) F := by
  have h : (MvPolynomial.aeval x).comp (linearPolynomialEquiv k e).toAlgHom = MvPolynomial.aeval (e x) := by
    apply MvPolynomial.algHom_ext
    intro i
    simpa only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, aeval_X, aeval_eq_eval] using eval_linearPolynomialEquiv_X k e x i
  simpa only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, aeval_eq_eval] using AlgHom.congr_fun h F

end DeJongAlterations.Algebra.ProjectiveLinearCoordinates
