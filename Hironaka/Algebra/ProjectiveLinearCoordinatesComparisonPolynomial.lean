import Hironaka.Algebra.ProjectiveLinearCoordinatesMatrixNormalization
import Hironaka.Algebra.ProjectiveLinearCoordinatesComparison
import Hironaka.Algebra.ProjectiveLinearCoordinatesQuotientPolynomial

/-!
# The ENTIRE original polynomial projection comparison for two independently chosen same-centre normalizations
-/

noncomputable section

open MvPolynomial

namespace Hironaka.Algebra.ProjectiveLinearCoordinates

universe u

variable (k : Type u) [Field k] (n : ℕ)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual whole original normalization polynomial is the actual whole original matrix polynomial on every original polynomial. -/
theorem coordinatePolynomialEquiv_apply_eq_linearPolynomialEquiv
    (v : Fin (n + 2) → k) (hv : v ≠ 0) (F : MvPolynomial (Fin (n + 2)) k) :
    coordinatePolynomialEquiv k n v hv F = linearPolynomialEquiv k (coordinateLinearEquiv k n v hv) F := by
  simpa only [AlgEquiv.toAlgHom_apply] using
    AlgHom.congr_fun (coordinatePolynomialEquiv_toAlgHom_eq_linearPolynomialEquiv k n v hv) F

/-- The literal entire original linear normalization identity holds for the internally constructed whole comparison. -/
theorem coordinateLinearEquiv_trans_comparison
    (v : Fin (n + 2) → k) (hv : v ≠ 0) (w : Fin (n + 2) → k) (hw : w ≠ 0) :
    (coordinateLinearEquiv k n v hv).trans (normalizationComparisonLinearEquiv k n v hv w hw) =
      coordinateLinearEquiv k n w hw := by
  apply LinearEquiv.ext
  intro x
  simp only [normalizationComparisonLinearEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

/-- The independently chosen original same-centre normalizations have the exact internally produced ENTIRE original polynomial projection triangle. -/
theorem normalizationRemainingPolynomial_triangle
    (v : Fin (n + 2) → k) (hv : v ≠ 0) (w : Fin (n + 2) → k) (hw : w ≠ 0)
    (a : k) (ha : a ≠ 0) (hwa : w = a • v) (F : MvPolynomial (Fin (n + 1)) k) :
    coordinatePolynomialEquiv k n w hw (MvPolynomial.rename Fin.succ F) =
      coordinatePolynomialEquiv k n v hv
        (MvPolynomial.rename Fin.succ (linearPolynomialEquiv k (normalizationRemainingLinearEquiv k n v hv w hw a ha hwa) F)) := by
  have h := linearPolynomialEquiv_trans k (coordinateLinearEquiv k n v hv)
    (normalizationComparisonLinearEquiv k n v hv w hw)
  rw [coordinateLinearEquiv_trans_comparison] at h
  rw [coordinatePolynomialEquiv_apply_eq_linearPolynomialEquiv,
    coordinatePolynomialEquiv_apply_eq_linearPolynomialEquiv]
  have hF := AlgHom.congr_fun h (MvPolynomial.rename Fin.succ F)
  simp only [AlgEquiv.toAlgHom_apply, AlgHom.comp_apply] at hF
  rw [hF, linearPolynomialEquiv_remaining_triangle k n
    (normalizationComparisonLinearEquiv k n v hv w hw) a⁻¹ (inv_ne_zero ha)
    (normalizationComparisonLinearEquiv_apply_centre k n v hv w hw a ha hwa)]
  rfl

end Hironaka.Algebra.ProjectiveLinearCoordinates
