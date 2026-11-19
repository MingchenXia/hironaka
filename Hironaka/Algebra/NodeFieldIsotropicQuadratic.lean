import Hironaka.Algebra.NodeFieldSplitQuadratic
import Mathlib.Tactic.FieldSimp

/-! # One ACTUAL nonzero original-field isotropic vector internally splits the SAME quadratic node -/

noncomputable section

namespace Hironaka.Algebra.NodeFieldIsotropicQuadratic

open MvPowerSeries NodeFormalMorse NodeNonsplit NodeVariableMorse
  NodeFieldQuadraticChangeSeries NodeFieldSplitQuadratic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {K : Type u} [Field K]

/-- These deterministic actual original coefficients use only division by a nonzero original coordinate, never by two. -/
def factorCoefficients (Q : Quadratic K) (v0 v1 : K) : Fin 4 → K := by
  classical
  exact if v0 = 0 then ![1, 0, Q.a0, Q.a1]
    else ![-(v1 / v0), 1, Q.a1 + Q.a2 * (v1 / v0), Q.a2]

/-- The actual isotropy equation produces the ENTIRE exact product over the SAME original field. -/
theorem factorization (Q : Quadratic K) (v0 v1 : K)
    (hzero : Q.value v0 v1 = 0) (hne : v0 ≠ 0 ∨ v1 ≠ 0) :
    Q.series = linearForm (factorCoefficients Q v0 v1 0) (factorCoefficients Q v0 v1 1) *
      linearForm (factorCoefficients Q v0 v1 2) (factorCoefficients Q v0 v1 3) := by
  by_cases h0 : v0 = 0
  · have h1 : v1 ≠ 0 := hne.resolve_left (not_not_intro h0)
    have ha2 : Q.a2 = 0 := by
      have h : Q.a2 * v1 ^ 2 = 0 := by simpa [Quadratic.value, h0] using hzero
      exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero 2 h1)
    simp only [factorCoefficients, h0, ↓reduceIte, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val]
    rw [product_expansion]
    change quadraticSeries Q.a0 Q.a1 Q.a2 = quadraticSeries (1 * Q.a0) _ (0 * Q.a1)
    simp [ha2]
  · have he : Q.a0 + Q.a1 * (v1 / v0) + Q.a2 * (v1 / v0) ^ 2 = 0 := by
      field_simp [h0]
      unfold Quadratic.value at hzero
      linear_combination hzero
    have hfirst : -(v1 / v0) * (Q.a1 + Q.a2 * (v1 / v0)) = Q.a0 := by
      linear_combination -he
    have hmiddle : -(v1 / v0) * Q.a2 + 1 * (Q.a1 + Q.a2 * (v1 / v0)) = Q.a1 := by ring
    simp only [factorCoefficients, h0, ↓reduceIte, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val]
    rw [product_expansion]
    change quadraticSeries Q.a0 Q.a1 Q.a2 = quadraticSeries _ _ (1 * Q.a2)
    rw [hfirst, hmiddle, one_mul]

/-- Actual factorization is a conclusion, not an input; no determinant or algebraic-closure certificate occurs. -/
theorem exists_factorization (Q : Quadratic K) (v0 v1 : K)
    (hzero : Q.value v0 v1 = 0) (hne : v0 ≠ 0 ∨ v1 ≠ 0) :
    ∃ a b c d : K, Q.series = linearForm a b * linearForm c d :=
  ⟨_, _, _, _, factorization Q v0 v1 hzero hne⟩

/-- The actual original inverse discriminant internally makes the produced tangent determinant nonzero, also in characteristic two. -/
theorem determinant_ne_zero (Q : Quadratic K) (v0 v1 : K)
    (hzero : Q.value v0 v1 = 0) (hne : v0 ≠ 0 ∨ v1 ≠ 0) :
    factorCoefficients Q v0 v1 0 * factorCoefficients Q v0 v1 3 -
      factorCoefficients Q v0 v1 1 * factorCoefficients Q v0 v1 2 ≠ 0 :=
  NodeFieldSplitQuadratic.determinant_ne_zero Q _ _ _ _ (factorization Q v0 v1 hzero hne)

/-- The genuine SAME-field coordinate automorphism comes from the internally produced factors. -/
def coordinateEquiv (Q : Quadratic K) (v0 v1 : K)
    (hzero : Q.value v0 v1 = 0) (hne : v0 ≠ 0 ∨ v1 ≠ 0) : Series K ≃ₐ[K] Series K :=
  splitEquiv Q _ _ _ _ (factorization Q v0 v1 hzero hne)

/-- The SAME original Q goes EXACTLY to the literal split product. -/
theorem coordinateEquiv_quadratic (Q : Quadratic K) (v0 v1 : K)
    (hzero : Q.value v0 v1 = 0) (hne : v0 ≠ 0 ∨ v1 ≠ 0) :
    coordinateEquiv Q v0 v1 hzero hne Q.series = (X 0 : Series K) * X 1 :=
  splitEquiv_quadratic Q _ _ _ _ (factorization Q v0 v1 hzero hne)

/-- EVERY original field coefficient is fixed. -/
theorem coordinateEquiv_coefficient (Q : Quadratic K) (v0 v1 : K)
    (hzero : Q.value v0 v1 = 0) (hne : v0 ≠ 0 ∨ v1 ≠ 0) (r : K) :
    coordinateEquiv Q v0 v1 hzero hne (C r) = C r :=
  splitEquiv_coefficient Q _ _ _ _ (factorization Q v0 v1 hzero hne) r

/-- BOTH original coordinates retain precisely the actual internally constructed adjugate inverse forms. -/
theorem coordinateEquiv_coordinate (Q : Quadratic K) (v0 v1 : K)
    (hzero : Q.value v0 v1 = 0) (hne : v0 ≠ 0 ∨ v1 ≠ 0) (i : Fin 2) :
    let a := factorCoefficients Q v0 v1 0
    let b := factorCoefficients Q v0 v1 1
    let c := factorCoefficients Q v0 v1 2
    let d := factorCoefficients Q v0 v1 3
    coordinateEquiv Q v0 v1 hzero hne (X i) =
      linearCoordinates ((a * d - b * c)⁻¹ * d) (-((a * d - b * c)⁻¹) * b)
        (-((a * d - b * c)⁻¹) * c) ((a * d - b * c)⁻¹ * a) i :=
  splitEquiv_coordinate Q _ _ _ _ (factorization Q v0 v1 hzero hne) i

/-- The SAME original quadratic quotient is genuinely the split quotient over its ORIGINAL field. -/
def quotientEquiv (Q : Quadratic K) (v0 v1 : K)
    (hzero : Q.value v0 v1 = 0) (hne : v0 ≠ 0 ∨ v1 ≠ 0) :
    QuadraticNode Q ≃ₐ[K] NodeFlatPresentation.SplitNode K :=
  NodeFieldSplitQuadratic.quotientEquiv Q _ _ _ _ (factorization Q v0 v1 hzero hne)

/-- EVERY original series representative follows the SAME actual coordinate automorphism. -/
theorem quotientEquiv_mk (Q : Quadratic K) (v0 v1 : K)
    (hzero : Q.value v0 v1 = 0) (hne : v0 ≠ 0 ∨ v1 ≠ 0) (f : Series K) :
    quotientEquiv Q v0 v1 hzero hne (Ideal.Quotient.mk _ f) =
      Ideal.Quotient.mk _ (coordinateEquiv Q v0 v1 hzero hne f) := rfl

/-- EVERY original field coefficient retains its literal original quotient class. -/
theorem quotientEquiv_coefficient (Q : Quadratic K) (v0 v1 : K)
    (hzero : Q.value v0 v1 = 0) (hne : v0 ≠ 0 ∨ v1 ≠ 0) (r : K) :
    quotientEquiv Q v0 v1 hzero hne (Ideal.Quotient.mk _ (C r)) = Ideal.Quotient.mk _ (C r) := by
  rw [quotientEquiv_mk, coordinateEquiv_coefficient]

/-- BOTH original quotient coordinates retain the SAME actual internally produced inverse-coordinate expressions. -/
theorem quotientEquiv_coordinate (Q : Quadratic K) (v0 v1 : K)
    (hzero : Q.value v0 v1 = 0) (hne : v0 ≠ 0 ∨ v1 ≠ 0) (i : Fin 2) :
    let a := factorCoefficients Q v0 v1 0
    let b := factorCoefficients Q v0 v1 1
    let c := factorCoefficients Q v0 v1 2
    let d := factorCoefficients Q v0 v1 3
    quotientEquiv Q v0 v1 hzero hne (Ideal.Quotient.mk _ (X i)) = Ideal.Quotient.mk _
      (linearCoordinates ((a * d - b * c)⁻¹ * d) (-((a * d - b * c)⁻¹) * b)
        (-((a * d - b * c)⁻¹) * c) ((a * d - b * c)⁻¹ * a) i) := by
  rw [quotientEquiv_mk, coordinateEquiv_coordinate]

end Hironaka.Algebra.NodeFieldIsotropicQuadratic
