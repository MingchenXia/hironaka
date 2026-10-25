import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring

/-! # Actual binary quadratic changes preserve the original discriminant, including characteristic two

All coefficient formulas are literal commutative-ring identities. The field
corollary uses the actual nonzero determinant and actual transformed diagonal
coefficients, without division by two or a supplied nondegeneracy certificate.
-/

namespace DeJongAlterations.Algebra.NodeFieldQuadraticChange

section Ring

universe u
variable {R : Type u} [CommRing R]

/-- The determinant of the SAME actual original linear coordinates. -/
def determinant (p q r s : R) : R := p * s - q * r

/-- The actual first coefficient after the prescribed original binary change. -/
def firstCoefficient (a b c p r : R) : R := a * p ^ 2 + b * p * r + c * r ^ 2

/-- The actual mixed coefficient; the literal formula includes characteristic two. -/
def middleCoefficient (a b c p q r s : R) : R :=
  2 * a * p * q + b * (p * s + q * r) + 2 * c * r * s

/-- The actual last coefficient after the prescribed original binary change. -/
def lastCoefficient (a b c q s : R) : R := a * q ^ 2 + b * q * s + c * s ^ 2

/-- The ENTIRE actual discriminant change is a polynomial identity over every commutative ring. -/
theorem discriminant_change (a b c p q r s : R) :
    middleCoefficient a b c p q r s ^ 2 -
      4 * firstCoefficient a b c p r * lastCoefficient a b c q s =
        determinant p q r s ^ 2 * (b ^ 2 - 4 * a * c) := by
  simp only [determinant, firstCoefficient, middleCoefficient, lastCoefficient]
  ring

/-- Actual inverse first-coefficient identity, requiring no inverse of the determinant or of two. -/
theorem recover_first (a b c p q r s : R) :
    determinant p q r s ^ 2 * a =
      s ^ 2 * firstCoefficient a b c p r - r * s * middleCoefficient a b c p q r s +
        r ^ 2 * lastCoefficient a b c q s := by
  simp only [determinant, firstCoefficient, middleCoefficient, lastCoefficient]
  ring

/-- Actual inverse mixed-coefficient identity, including characteristic two. -/
theorem recover_middle (a b c p q r s : R) :
    determinant p q r s ^ 2 * b =
      -2 * q * s * firstCoefficient a b c p r +
        (p * s + q * r) * middleCoefficient a b c p q r s -
          2 * p * r * lastCoefficient a b c q s := by
  simp only [determinant, firstCoefficient, middleCoefficient, lastCoefficient]
  ring

/-- Actual inverse last-coefficient identity, requiring no chosen inverse matrix. -/
theorem recover_last (a b c p q r s : R) :
    determinant p q r s ^ 2 * c =
      q ^ 2 * firstCoefficient a b c p r - p * q * middleCoefficient a b c p q r s +
        p ^ 2 * lastCoefficient a b c q s := by
  simp only [determinant, firstCoefficient, middleCoefficient, lastCoefficient]
  ring

end Ring

section Field

universe v
variable {L : Type v} [Field L]

/-- An actual invertible binary change preserves the nonzero original quadratic coefficient triple. -/
theorem transformed_not_all_zero (a b c p q r s : L)
    (hdet : determinant p q r s ≠ 0) (habc : ¬ (a = 0 ∧ b = 0 ∧ c = 0)) :
    ¬ (firstCoefficient a b c p r = 0 ∧ middleCoefficient a b c p q r s = 0 ∧
      lastCoefficient a b c q s = 0) := by
  rintro ⟨hA, hB, hC⟩
  have hd2 : determinant p q r s ^ 2 ≠ 0 := pow_ne_zero 2 hdet
  have ha : determinant p q r s ^ 2 * a = 0 := by
    simpa [hA, hB, hC] using recover_first a b c p q r s
  have hb : determinant p q r s ^ 2 * b = 0 := by
    simpa [hA, hB, hC] using recover_middle a b c p q r s
  have hc : determinant p q r s ^ 2 * c = 0 := by
    simpa [hA, hB, hC] using recover_last a b c p q r s
  exact habc ⟨(mul_eq_zero.mp ha).resolve_left hd2,
    (mul_eq_zero.mp hb).resolve_left hd2, (mul_eq_zero.mp hc).resolve_left hd2⟩

/-- If BOTH actual transformed diagonal coefficients vanish, the SAME actual middle coefficient is nonzero. -/
theorem middle_ne_zero (a b c p q r s : L)
    (hdet : determinant p q r s ≠ 0) (habc : ¬ (a = 0 ∧ b = 0 ∧ c = 0))
    (hA : firstCoefficient a b c p r = 0) (hC : lastCoefficient a b c q s = 0) :
    middleCoefficient a b c p q r s ≠ 0 := by
  intro hB
  exact transformed_not_all_zero a b c p q r s hdet habc ⟨hA, hB, hC⟩

/-- Actual invertible split coordinates INTERNALLY prove nonzero original discriminant, in EVERY characteristic. -/
theorem discriminant_ne_zero (a b c p q r s : L)
    (hdet : determinant p q r s ≠ 0) (habc : ¬ (a = 0 ∧ b = 0 ∧ c = 0))
    (hA : firstCoefficient a b c p r = 0) (hC : lastCoefficient a b c q s = 0) :
    b ^ 2 - 4 * a * c ≠ 0 := by
  intro hdisc
  have hB := middle_ne_zero a b c p q r s hdet habc hA hC
  have hzero : middleCoefficient a b c p q r s ^ 2 = 0 := by
    simpa [hA, hC, hdisc] using discriminant_change a b c p q r s
  exact (pow_ne_zero 2 hB) hzero

end Field

end DeJongAlterations.Algebra.NodeFieldQuadraticChange
