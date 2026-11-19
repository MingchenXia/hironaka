import Hironaka.Algebra.ProjectiveLinearCoordinatesMatrixGraded
import Hironaka.Algebra.ProjectiveSecantProjectionCoordinates

/-!
# The actual original normalization is exactly its whole matrix polynomial automorphism, over every field
-/

noncomputable section

open MvPolynomial

namespace Hironaka.Algebra.ProjectiveLinearCoordinates

universe u v

variable (k : Type u) [Field k]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Every original homogeneous degree-one polynomial is its actual standard-basis evaluation row form, including over finite fields. -/
theorem homogeneous_one_eq_basis_eval_sum {ι : Type v} [Fintype ι] [DecidableEq ι]
    {F : MvPolynomial ι k} (hF : F.IsHomogeneous 1) :
    (∑ j, C (MvPolynomial.eval (Pi.single j 1) F) * X j) = F := by
  change F ∈ homogeneousSubmodule ι k 1 at hF
  rw [MvPolynomial.homogeneousSubmodule_one_eq_span_X] at hF
  induction hF using Submodule.span_induction with
  | mem F h =>
    obtain ⟨i, rfl⟩ := h
    simp [Pi.single_apply]
  | zero => simp
  | add F G _ _ hF hG =>
    simp only [map_add, add_mul, Finset.sum_add_distrib, hF, hG]
  | smul a F _ h =>
    simp only [smul_eq_C_mul, map_mul, eval_C, mul_assoc, ← Finset.mul_sum, h]

/-- Every exact original normalization coordinate form equals its literal standard-basis matrix row polynomial. -/
theorem coordinatePolynomialEquiv_X_eq_matrixForm
    (n : ℕ) (v : Fin (n + 2) → k) (hv : v ≠ 0) (i : Fin (n + 2)) :
    coordinatePolynomialEquiv k n v hv (X i) =
      matrixForm k (LinearMap.toMatrix' (coordinateLinearEquiv k n v hv).toLinearMap) i := by
  rw [← homogeneous_one_eq_basis_eval_sum k
    (coordinatePolynomialEquiv_isHomogeneous k n v hv (MvPolynomial.isHomogeneous_X k i))]
  simp only [ProjectiveSecant.original_eval_coordinatePolynomialEquiv, matrixForm, LinearMap.toMatrix'_apply, eval_X, LinearEquiv.coe_coe]

/-- The SAME original entire polynomial normalization is exactly the actual original linear equivalence's entire matrix polynomial automorphism. -/
theorem coordinatePolynomialEquiv_toAlgHom_eq_linearPolynomialEquiv
    (n : ℕ) (v : Fin (n + 2) → k) (hv : v ≠ 0) :
    (coordinatePolynomialEquiv k n v hv).toAlgHom =
      (linearPolynomialEquiv k (coordinateLinearEquiv k n v hv)).toAlgHom := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgEquiv.toAlgHom_apply, coordinatePolynomialEquiv_X_eq_matrixForm]
  change matrixForm k (LinearMap.toMatrix' (coordinateLinearEquiv k n v hv).toLinearMap) i =
    matrixPolynomialMap k (LinearMap.toMatrix' (coordinateLinearEquiv k n v hv).toLinearMap) (X i)
  simp only [matrixPolynomialMap, aeval_X]

end Hironaka.Algebra.ProjectiveLinearCoordinates
