import Hironaka.Algebra.ProjectiveLinearCoordinatesMatrix
import Hironaka.Algebra.ProjectiveLinearCoordinatesQuotient

/-!
# The actual remaining-coordinate automorphism retains the literal whole polynomial projection triangle
-/

noncomputable section

open MvPolynomial

namespace Hironaka.Algebra.ProjectiveLinearCoordinates

universe u

variable (k : Type u) [Field k] (n : ℕ)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The SAME actual entire original matrix has zero original first-column entries in every remaining row, internally from the original centre-line equality. -/
theorem centreLine_matrix_succ_zero
    (e : (Fin (n + 2) → k) ≃ₗ[k] (Fin (n + 2) → k)) (c : k)
    (he : e (Pi.single 0 1) = c • Pi.single 0 1) (i : Fin (n + 1)) :
    LinearMap.toMatrix' e.toLinearMap i.succ 0 = 0 := by
  change e (Pi.single 0 1) i.succ = 0
  rw [he]
  simp

/-- Every actual remaining matrix entry agrees with the internally constructed actual remaining-coordinate equivalence. -/
theorem remainingLinearEquiv_matrix_entry
    (e : (Fin (n + 2) → k) ≃ₗ[k] (Fin (n + 2) → k)) (c : k) (hc : c ≠ 0)
    (he : e (Pi.single 0 1) = c • Pi.single 0 1) (i j : Fin (n + 1)) :
    LinearMap.toMatrix' e.toLinearMap i.succ j.succ =
      LinearMap.toMatrix' (remainingLinearEquiv k n e c hc he).toLinearMap i j := by
  have h := remainingLinearEquiv_tail k n e c hc he (Pi.single j.succ 1)
  have ht : tailLinearMap k n (Pi.single j.succ 1) = Pi.single j 1 := by
    ext r
    simp [tailLinearMap, Pi.single_apply]
  rw [ht] at h
  exact congrFun h i

/-- The actual internally induced remaining-coordinate equivalence preserves the literal full polynomial projection triangle on the ENTIRE original ring. -/
theorem linearPolynomialEquiv_remaining_triangle
    (e : (Fin (n + 2) → k) ≃ₗ[k] (Fin (n + 2) → k)) (c : k) (hc : c ≠ 0)
    (he : e (Pi.single 0 1) = c • Pi.single 0 1) (F : MvPolynomial (Fin (n + 1)) k) :
    linearPolynomialEquiv k e (MvPolynomial.rename Fin.succ F) =
      MvPolynomial.rename Fin.succ (linearPolynomialEquiv k (remainingLinearEquiv k n e c hc he) F) := by
  have h : (linearPolynomialEquiv k e).toAlgHom.comp (MvPolynomial.rename Fin.succ) =
      (MvPolynomial.rename Fin.succ).comp (linearPolynomialEquiv k (remainingLinearEquiv k n e c hc he)).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, rename_X]
    change matrixPolynomialMap k (LinearMap.toMatrix' e.toLinearMap) (X i.succ) =
      MvPolynomial.rename Fin.succ
        (matrixPolynomialMap k (LinearMap.toMatrix' (remainingLinearEquiv k n e c hc he).toLinearMap) (X i))
    simp only [matrixPolynomialMap, aeval_X, matrixForm, Fin.sum_univ_succ,
      centreLine_matrix_succ_zero k n e c he, map_zero, zero_mul, zero_add,
      map_add, map_sum, map_mul, rename_C, rename_X, remainingLinearEquiv_matrix_entry k n e c hc he]
  exact AlgHom.congr_fun h F

end Hironaka.Algebra.ProjectiveLinearCoordinates
