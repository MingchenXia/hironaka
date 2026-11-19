/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Hironaka.Geometry.ProperSteinProjectiveCechReesCoefficients

/-! # Actual homogeneous multiplication in coefficient-extended Rees algebras

Adapted closed native proof from
`EnvelopeProperty/EnvelopeProperty/AlgGeom/FormalFunctionsReesMultiplication.lean`,
SHA256 d4167f63fb04f0076e7adcf68bdcb98417187426a949887090ccb0b483864f61.
Only Mathlib and the actual owned original Rees coefficient helper are imported. -/

open scoped Polynomial DirectSum
noncomputable section
universe u
namespace Hironaka.Geometry.ProperSteinProjectiveCech.ReesMultiplication

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (I : Ideal R)

/-- An original ideal-power element has its actual image in the extended power. -/
def mappedPower {e : ℕ} (a : ↥(I ^ e)) :
    ↥((I.map (algebraMap R A)) ^ e) :=
  ⟨algebraMap R A a, by
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem (algebraMap R A) a.2⟩

/-- Literal multiplication by the original extended homogeneous coefficient. -/
def powerMultiply {e : ℕ} (a : ↥(I ^ e)) (d : ℕ) :
    ↥((I.map (algebraMap R A)) ^ d) →ₗ[R]
      ↥((I.map (algebraMap R A)) ^ (e + d)) where
  toFun x := ⟨(mappedPower I (A := A) a : A) * (x : A), by
    rw [pow_add]
    exact Ideal.mul_mem_mul (mappedPower I (A := A) a).2 x.2⟩
  map_add' x y := Subtype.ext (mul_add _ _ _)
  map_smul' r x := by
    apply Subtype.ext
    change algebraMap R A a * (r • (x : A)) = r • (algebraMap R A a * (x : A))
    simp only [Algebra.smul_def, mul_left_comm]

/-- Every original coefficient is multiplied literally, with no replacement action. -/
theorem powerMultiply_apply {e : ℕ} (a : ↥(I ^ e)) (d : ℕ)
    (x : ↥((I.map (algebraMap R A)) ^ d)) :
    (powerMultiply I a d x : A) = algebraMap R A a * (x : A) := rfl

/-- The actual polynomial monomial in an actual Rees algebra. -/
def monomial (J : Ideal A) (d : ℕ) (x : ↥(J ^ d)) : reesAlgebra J :=
  ⟨Polynomial.monomial d (x : A), reesAlgebra.monomial_mem.mpr x.2⟩

/-- Actual multiplication of original homogeneous Rees elements shifts exactly
by the original polynomial degree and multiplies the actual coefficients. -/
theorem monomial_mul {e : ℕ} (a : ↥(I ^ e)) (d : ℕ)
    (x : ↥((I.map (algebraMap R A)) ^ d)) :
    monomial (I.map (algebraMap R A)) e (mappedPower I a) *
      monomial (I.map (algebraMap R A)) d x =
        monomial (I.map (algebraMap R A)) (e + d) (powerMultiply I a d x) := by
  apply Subtype.ext
  exact Polynomial.monomial_mul_monomial _ _ _ _

/-- The genuine coefficient decomposition identifies ACTUAL homogeneous Rees
multiplication with the actual shifted ideal-power inclusion. -/
theorem powerEquiv_monomial_mul {e : ℕ} (a : ↥(I ^ e)) (d : ℕ)
    (x : ↥((I.map (algebraMap R A)) ^ d)) :
    ReesCoefficients.powerEquiv (I.map (algebraMap R A))
      (monomial (I.map (algebraMap R A)) e (mappedPower I a) *
        monomial (I.map (algebraMap R A)) d x) =
      DirectSum.lof A ℕ (fun n => ↥((I.map (algebraMap R A)) ^ n))
        (e + d) (powerMultiply I a d x) := by
  rw [monomial_mul]
  exact ReesCoefficients.coefficients_monomial _ _ _

section Restriction

variable {B : Type u} [CommRing B] [Algebra R B] (φ : A →ₐ[R] B)

/-- The original algebra map restricts to every genuine extended ideal power. -/
def powerRestriction (d : ℕ) :
    ↥((I.map (algebraMap R A)) ^ d) →ₗ[R]
      ↥((I.map (algebraMap R B)) ^ d) where
  toFun x := ⟨φ x, by
    have hx := Ideal.mem_map_of_mem φ.toRingHom x.2
    rw [Ideal.map_pow, Ideal.map_map] at hx
    have hφ : φ.toRingHom.comp (algebraMap R A) = algebraMap R B := by
      ext r
      exact φ.commutes r
    rwa [hφ] at hx⟩
  map_add' x y := Subtype.ext (map_add φ _ _)
  map_smul' r x := Subtype.ext (φ.toLinearMap.map_smul r (x : A))

/-- The ENTIRE original homogeneous multiplication square commutes with
the actual ideal-power restriction along the given original algebra map. -/
theorem powerRestriction_multiply {e : ℕ} (a : ↥(I ^ e)) (d : ℕ) :
    (powerRestriction I φ (e + d)).comp (powerMultiply I (A := A) a d) =
      (powerMultiply I (A := B) a d).comp (powerRestriction I φ d) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change φ (algebraMap R A a * (x : A)) = algebraMap R B a * φ (x : A)
  rw [map_mul, φ.commutes]

end Restriction

end Hironaka.Geometry.ProperSteinProjectiveCech.ReesMultiplication
