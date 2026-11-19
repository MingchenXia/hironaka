import Hironaka.Algebra.PluckerQuotChart
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# The genuine polynomial-coordinate universal quotient chart

Actual coefficient homomorphisms from the matrix polynomial ring classify
precisely the native pivot-chart quotient kernels. Evaluation preserves the
original normalized quotient and section formulas under every base change.
-/

noncomputable section

namespace Hironaka.Algebra.PluckerQuot

universe u v w z

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type u) [CommRing R] (ι : Type v) (κ : Type w)
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Polynomial coefficient maps are equivalent to their actual original matrix entries. -/
def coefficientMatrixEquiv (A : Type z) [CommRing A] [Algebra R A] :
    (MvPolynomial (ι × κ) R →ₐ[R] A) ≃ Matrix ι κ A where
  toFun φ i j := φ (MvPolynomial.X (i, j))
  invFun a := MvPolynomial.aeval fun ij ↦ a ij.1 ij.2
  left_inv φ := by
    ext ij
    simp
  right_inv a := by
    ext i j
    exact MvPolynomial.aeval_X _ _

/-- The actual polynomial coefficient maps classify precisely the intrinsic native quotient chart. -/
def polynomialChartEquiv (A : Type z) [CommRing A] [Algebra R A] :
    (MvPolynomial (ι × κ) R →ₐ[R] A) ≃ PivotChart (R := A) (ι := ι) (κ := κ) :=
  (coefficientMatrixEquiv R ι κ A).trans matrixChartEquiv

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
/-- Coefficient evaluation preserves the literal original quotient formula. -/
theorem map_matrixQuotient {A : Type z} [CommRing A] (φ : R →+* A)
    (a : Matrix ι κ R) (v : (ι ⊕ κ) → R) (i : ι) :
    φ (matrixQuotient a v i) =
      matrixQuotient (R := A) (ι := ι) (κ := κ)
        (fun i j ↦ φ (a i j)) (fun j : ι ⊕ κ ↦ φ (v j)) i := by
  simp only [matrixQuotient_apply, map_add, map_sum, map_mul]

end Hironaka.Algebra.PluckerQuot
