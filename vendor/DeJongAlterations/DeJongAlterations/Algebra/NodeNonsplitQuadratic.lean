import DeJongAlterations.Algebra.NodeFormalMorseDecomposition
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! # Actual inverse-Hessian identities for binary quadratics in arbitrary characteristic -/

noncomputable section

namespace DeJongAlterations.Algebra.NodeNonsplit

open MvPowerSeries

universe u v

/-- Original quadratic coefficients with the inverse of their actual discriminant. -/
@[ext]
structure Quadratic (R : Type u) [CommRing R] where
  a0 : R
  a1 : R
  a2 : R
  invDiscriminant : R
  inverse_discriminant : invDiscriminant * (a1 ^ 2 - 4 * a0 * a2) = 1

variable {R : Type u} [CommRing R]

/-- The original discriminant-unit hypothesis internally supplies its actual inverse. -/
def Quadratic.ofCoefficients (a0 a1 a2 : R) (h : IsUnit (a1 ^ 2 - 4 * a0 * a2)) : Quadratic R where
  a0 := a0
  a1 := a1
  a2 := a2
  invDiscriminant := ↑(h.unit⁻¹)
  inverse_discriminant := by
    calc
      ↑(h.unit⁻¹) * (a1 ^ 2 - 4 * a0 * a2) = ↑(h.unit⁻¹) * (h.unit : R) :=
        congrArg (fun x : R => ↑(h.unit⁻¹) * x) h.unit_spec.symm
      _ = 1 := Units.inv_mul _

/-- Literal coefficient transport, including the actual inverse. -/
def Quadratic.map (Q : Quadratic R) {S : Type v} [CommRing S] (f : R →+* S) : Quadratic S where
  a0 := f Q.a0
  a1 := f Q.a1
  a2 := f Q.a2
  invDiscriminant := f Q.invDiscriminant
  inverse_discriminant := by
    simpa only [map_mul, map_sub, map_pow, map_ofNat, map_one] using congrArg f Q.inverse_discriminant

@[simp]
theorem Quadratic.map_map (Q : Quadratic R) {S T : Type*} [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) : (Q.map f).map g = Q.map (g.comp f) := by
  ext <;> rfl

@[simp]
theorem Quadratic.map_id (Q : Quadratic R) : Q.map (RingHom.id R) = Q := by
  ext <;> rfl

/-- The literal original quadratic polynomial evaluated at the actual two elements. -/
def Quadratic.value (Q : Quadratic R) (u v : R) : R := Q.a0 * u ^ 2 + Q.a1 * u * v + Q.a2 * v ^ 2

def Quadratic.left (Q : Quadratic R) (a b : R) : R :=
  Q.invDiscriminant * (Q.a1 * b - 2 * Q.a2 * a)

def Quadratic.right (Q : Quadratic R) (a b : R) : R :=
  Q.invDiscriminant * (Q.a1 * a - 2 * Q.a0 * b)

/-- The Hessian inverse requires only the actual discriminant unit, including in characteristic two. -/
theorem Quadratic.gradient_correction (Q : Quadratic R) (u v a b : R) :
    (2 * Q.a0 * u + Q.a1 * v) * Q.left a b +
      (Q.a1 * u + 2 * Q.a2 * v) * Q.right a b = u * a + v * b := by
  calc
    _ = (Q.invDiscriminant * (Q.a1 ^ 2 - 4 * Q.a0 * Q.a2)) * (u * a + v * b) := by
      unfold Quadratic.left Quadratic.right
      ring
    _ = u * a + v * b := by rw [Q.inverse_discriminant, one_mul]

/-- Exact quadratic expansion with no division by two. -/
theorem Quadratic.expansion (Q : Quadratic R) (u v a b : R) :
    Q.value (u - Q.left a b) (v - Q.right a b) =
      Q.value u v - u * a - v * b + Q.value (Q.left a b) (Q.right a b) := by
  have he := Q.gradient_correction u v a b
  unfold Quadratic.value
  linear_combination -he

/-- The original quadratic in the literal original formal-series ring. -/
def Quadratic.series (Q : Quadratic R) : NodeFormalMorse.Series R :=
  (Q.map C).value (X 0) (X 1)

@[simp]
theorem Quadratic.map_series (Q : Quadratic R) {S : Type*} [CommRing S] (f : R →+* S) :
    MvPowerSeries.map f Q.series = (Q.map f).series := by
  simp [Quadratic.series, Quadratic.value, Quadratic.map]

end DeJongAlterations.Algebra.NodeNonsplit
