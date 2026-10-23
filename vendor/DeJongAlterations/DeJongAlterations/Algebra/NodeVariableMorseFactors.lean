import DeJongAlterations.Algebra.NodeNonsplitQuadratic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic.NormNum

/-! # Internally constructed independent factors of the original quadratic -/

noncomputable section

namespace DeJongAlterations.Algebra.NodeVariableMorse

open NodeNonsplit

universe u
variable {K : Type u} [Field K]

/-- Actual factor coefficients and their proved coefficient and determinant identities. -/
structure QuadraticFactors (Q : Quadratic K) where
  a : K
  b : K
  c : K
  d : K
  determinant_ne_zero : a * d - b * c ≠ 0
  first_coefficient : a * c = Q.a0
  middle_coefficient : a * d + b * c = Q.a1
  last_coefficient : b * d = Q.a2

/-- The actual discriminant inverse excludes a zero original discriminant. -/
theorem quadraticDiscriminant_ne_zero (Q : Quadratic K) :
    Q.a1 ^ 2 - 4 * Q.a0 * Q.a2 ≠ 0 := by
  intro hz
  have hh := Q.inverse_discriminant
  rw [hz, mul_zero] at hh
  exact zero_ne_one hh

/-- The original nondegenerate quadratic internally supplies two independent factors in every characteristic. -/
theorem exists_quadraticFactors [IsAlgClosed K] (Q : Quadratic K) :
    Nonempty (QuadraticFactors Q) := by
  by_cases ha : Q.a0 = 0
  · have hb : Q.a1 ≠ 0 := by
      intro hz
      apply quadraticDiscriminant_ne_zero Q
      rw [ha, hz]
      ring
    exact ⟨{
      a := 0, b := 1, c := Q.a1, d := Q.a2
      determinant_ne_zero := by simpa using neg_ne_zero.mpr hb
      first_coefficient := by simpa using ha.symm
      middle_coefficient := by simp
      last_coefficient := by simp }⟩
  · let p : Polynomial K := Polynomial.C Q.a0 * Polynomial.X ^ 2 +
      Polynomial.C Q.a1 * Polynomial.X + Polynomial.C Q.a2
    have hp2 : p.coeff 2 = Q.a0 := by simp [p]
    have hp : p.degree ≠ 0 := by
      intro hz
      have hh : p.coeff 2 = 0 := Polynomial.coeff_eq_zero_of_degree_lt (by rw [hz]; norm_num)
      exact ha (hp2.symm.trans hh)
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_root p hp
    have he : Q.a0 * r ^ 2 + Q.a1 * r + Q.a2 = 0 := by
      simpa [Polynomial.IsRoot, p] using hr
    have hdet : Q.a1 + 2 * Q.a0 * r ≠ 0 := by
      intro hz
      have hs : (Q.a1 + 2 * Q.a0 * r) ^ 2 = Q.a1 ^ 2 - 4 * Q.a0 * Q.a2 := by
        linear_combination 4 * Q.a0 * he
      apply quadraticDiscriminant_ne_zero Q
      rw [← hs, hz, zero_pow two_ne_zero]
    exact ⟨{
      a := 1, b := -r, c := Q.a0, d := Q.a1 + Q.a0 * r
      determinant_ne_zero := by convert hdet using 1; ring
      first_coefficient := by simp
      middle_coefficient := by ring
      last_coefficient := by linear_combination -he }⟩

/-- The actual independent factors are chosen only from the proved original coefficient theorem. -/
def quadraticFactors [IsAlgClosed K] (Q : Quadratic K) : QuadraticFactors Q :=
  Classical.choice (exists_quadraticFactors Q)

/-- The original quadratic equals the product of its internally constructed actual linear factors. -/
theorem QuadraticFactors.value_eq (Q : Quadratic K) (F : QuadraticFactors Q) (u v : K) :
    Q.value u v = (F.a * u + F.b * v) * (F.c * u + F.d * v) := by
  rw [Quadratic.value, ← F.first_coefficient, ← F.middle_coefficient, ← F.last_coefficient]
  ring

end DeJongAlterations.Algebra.NodeVariableMorse
