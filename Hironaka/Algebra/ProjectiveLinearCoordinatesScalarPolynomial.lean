import Hironaka.Algebra.ProjectiveLinearCoordinatesScalar

/-!
# The SAME original entire linear polynomial substitution retains its literal whole scalar coefficient triangle
-/

noncomputable section

open MvPolynomial

namespace Hironaka.Algebra.ProjectiveLinearCoordinates

universe u v w t

variable (k : Type u) (L : Type v) [Field k] [Field L] (φ : k →+* L)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual original row forms commute with the SAME original whole coefficient map. -/
theorem matrixForm_map {ι : Type w} {κ : Type t} [Fintype κ] (A : Matrix ι κ k) (i : ι) :
    MvPolynomial.map φ (matrixForm k A i) = matrixForm L (A.map φ) i := by
  simp only [matrixForm, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, Matrix.map_apply]

/-- The ENTIRE original polynomial substitution coefficient square commutes literally with the internally constructed whole scalar linear equivalence. -/
theorem scalarLinearEquiv_polynomial_coefficient_square {ι : Type w} [Fintype ι] [DecidableEq ι]
    (e : (ι → k) ≃ₗ[k] (ι → k)) :
    (MvPolynomial.map φ).comp (linearPolynomialEquiv k e).toRingHom =
      (linearPolynomialEquiv L (scalarLinearEquiv k L φ e)).toRingHom.comp (MvPolynomial.map φ) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply]
    change MvPolynomial.map φ (linearPolynomialEquiv k e (C a)) =
      linearPolynomialEquiv L (scalarLinearEquiv k L φ e) (MvPolynomial.map φ (C a))
    have hk : linearPolynomialEquiv k e (C a) = C a := (linearPolynomialEquiv k e).commutes a
    have hL : linearPolynomialEquiv L (scalarLinearEquiv k L φ e) (C (φ a)) = C (φ a) :=
      (linearPolynomialEquiv L (scalarLinearEquiv k L φ e)).commutes (φ a)
    rw [hk, MvPolynomial.map_C, hL]
  · intro i
    simp only [RingHom.comp_apply]
    change MvPolynomial.map φ (matrixPolynomialMap k (LinearMap.toMatrix' e.toLinearMap) (X i)) =
      matrixPolynomialMap L (LinearMap.toMatrix' (scalarLinearEquiv k L φ e).toLinearMap)
        (MvPolynomial.map φ (X i))
    simp only [MvPolynomial.map_X, matrixPolynomialMap, aeval_X, scalarLinearEquiv_toMatrix, matrixForm_map]

/-- The SAME original linear substitution's entire actual scalar coefficient triangle holds on EVERY original polynomial. -/
theorem scalarLinearEquiv_polynomial_coefficient_triangle {ι : Type w} [Fintype ι] [DecidableEq ι]
    (e : (ι → k) ≃ₗ[k] (ι → k)) (F : MvPolynomial ι k) :
    MvPolynomial.map φ (linearPolynomialEquiv k e F) =
      linearPolynomialEquiv L (scalarLinearEquiv k L φ e) (MvPolynomial.map φ F) :=
  RingHom.congr_fun (scalarLinearEquiv_polynomial_coefficient_square k L φ e) F

/-- Actual scalar coefficient mapping preserves nonzeroness of the SAME original nonzero vector. -/
theorem coefficient_vector_ne_zero {ι : Type w} (v : ι → k) (hv : v ≠ 0) : φ ∘ v ≠ 0 := by
  intro h
  apply hv
  ext i
  apply φ.injective
  simpa only [Function.comp_apply, Pi.zero_apply, map_zero] using congrFun h i

/-- The scalar extension of the SAME original internally chosen normalization sends the SAME actual mapped original vector exactly to the actual standard centre vector, without choosing a new pivot. -/
theorem scalar_coordinateLinearEquiv_apply_self (n : ℕ) (v : Fin (n + 2) → k) (hv : v ≠ 0) :
    scalarLinearEquiv k L φ (coordinateLinearEquiv k n v hv) (φ ∘ v) = Pi.single 0 1 := by
  rw [scalarLinearEquiv_coefficient_triangle, coordinateLinearEquiv_apply_self]
  ext i
  simp [Pi.single_apply]

end Hironaka.Algebra.ProjectiveLinearCoordinates
