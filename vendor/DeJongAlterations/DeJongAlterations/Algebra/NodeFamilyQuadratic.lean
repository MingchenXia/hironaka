import DeJongAlterations.Algebra.NodeBlowupChart
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.ComputeDegree

/-!
# The actual node as a monic quadratic algebra over a polynomial ring

The coordinate `w=u+v` gives a division-free presentation in every characteristic.
-/

noncomputable section

open Polynomial

namespace DeJongAlterations.Algebra.NodeFamilyQuadratic

open NodeBlowupChart

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type u} [CommRing A]

/-- The monic quadratic equation in `z` with coefficient variable `w`. -/
def quadratic (t : A) : A[X][X] := X ^ 2 - C X * X + C (C t)

abbrev QuadraticAlgebra (t : A) := AdjoinRoot (quadratic t)

theorem quadratic_monic (t : A) : (quadratic t).Monic := by
  unfold quadratic
  monicity!

/-- The actual coefficient-variable class in the quadratic quotient. -/
def sumCoordinate (t : A) : QuadraticAlgebra t := algebraMap A[X] (QuadraticAlgebra t) X

/-- The actual root-coordinate class in the quadratic quotient. -/
def rootCoordinate (t : A) : QuadraticAlgebra t := AdjoinRoot.root (quadratic t)

theorem quadratic_relation (t : A) :
    rootCoordinate t ^ 2 - sumCoordinate t * rootCoordinate t +
      algebraMap A (QuadraticAlgebra t) t = 0 := by
  have h := AdjoinRoot.mk_self (f := quadratic t)
  change (AdjoinRoot.mk (quadratic t)) (X ^ 2 - C X * X + C (C t)) = 0 at h
  rw [map_add, map_sub, map_pow, map_mul, AdjoinRoot.mk_X,
    AdjoinRoot.mk_C, AdjoinRoot.mk_C] at h
  exact h

/-- The forward polynomial substitution `u=w-z`, `v=z`. -/
def forwardPolynomial (t : A) : MvPolynomial (Fin 2) A →ₐ[A] QuadraticAlgebra t :=
  MvPolynomial.aeval ![sumCoordinate t - rootCoordinate t, rootCoordinate t]

private theorem forwardPolynomial_relation (t : A) :
    forwardPolynomial t (MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C t) = 0 := by
  simp only [forwardPolynomial, map_sub, map_mul, MvPolynomial.aeval_X,
    MvPolynomial.aeval_C, Matrix.cons_val_zero, Matrix.cons_val_one]
  calc
    _ = -(rootCoordinate t ^ 2 - sumCoordinate t * rootCoordinate t +
      algebraMap A (QuadraticAlgebra t) t) := by ring
    _ = 0 := by rw [quadratic_relation, neg_zero]

private theorem forwardPolynomial_ideal (t : A) :
    NodeChart.uChartIdeal A t ≤ RingHom.ker (forwardPolynomial t).toRingHom := by
  apply Ideal.span_le.mpr
  rintro _ rfl
  exact forwardPolynomial_relation t

/-- The actual quotient homomorphism to the monic quadratic presentation. -/
def forward (t : A) : Node A t →ₐ[A] QuadraticAlgebra t :=
  Ideal.Quotient.liftₐ _ (forwardPolynomial t) (fun _ h ↦ forwardPolynomial_ideal t h)

@[simp]
theorem forward_coordinate0 (t : A) :
    forward t (coordinate t 0) = sumCoordinate t - rootCoordinate t := by
  simp [forward, coordinate, forwardPolynomial]

@[simp]
theorem forward_coordinate1 (t : A) :
    forward t (coordinate t 1) = rootCoordinate t := by
  simp [forward, coordinate, forwardPolynomial]

/-- The reverse coefficient substitution `w=u+v`. -/
def backwardCoefficient (t : A) : A[X] →ₐ[A] Node A t :=
  Polynomial.aeval (coordinate t 0 + coordinate t 1)

private theorem backward_relation (t : A) :
    (quadratic t).eval₂ (backwardCoefficient t) (coordinate t 1) = 0 := by
  simp only [quadratic, Polynomial.eval₂_add, Polynomial.eval₂_sub,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_mul, Polynomial.eval₂_C]
  change coordinate t 1 ^ 2 - backwardCoefficient t X * coordinate t 1 +
    backwardCoefficient t (C t) = 0
  rw [show backwardCoefficient t X = coordinate t 0 + coordinate t 1 from Polynomial.aeval_X _,
    show backwardCoefficient t (C t) = algebraMap A (Node A t) t from Polynomial.aeval_C _ _]
  have hprod : coordinate t 0 * coordinate t 1 = algebraMap A (Node A t) t :=
    NodeDomain.nodeCoordinateProduct t
  calc
    _ = algebraMap A (Node A t) t - coordinate t 0 * coordinate t 1 := by ring
    _ = 0 := by rw [hprod]; exact sub_self _

/-- The actual reverse homomorphism from the full monic quadratic quotient. -/
def backward (t : A) : QuadraticAlgebra t →ₐ[A] Node A t :=
  AdjoinRoot.liftAlgHom (quadratic t) (backwardCoefficient t) (coordinate t 1) (backward_relation t)

@[simp]
theorem backward_root (t : A) : backward t (rootCoordinate t) = coordinate t 1 :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

@[simp]
theorem backward_sum (t : A) : backward t (sumCoordinate t) = coordinate t 0 + coordinate t 1 := by
  change backward t (AdjoinRoot.of (quadratic t) X) = _
  rw [backward, AdjoinRoot.liftAlgHom_of]
  exact Polynomial.aeval_X _

private theorem backward_forward (t : A) : (backward t).comp (forward t) = AlgHom.id A _ := by
  apply Ideal.Quotient.algHom_ext
  ext i
  fin_cases i
  · change backward t (forward t (coordinate t 0)) = coordinate t 0
    simp
  · change backward t (forward t (coordinate t 1)) = coordinate t 1
    simp

private theorem forward_backward (t : A) : (forward t).comp (backward t) = AlgHom.id A _ := by
  apply AdjoinRoot.algHom_ext'
  · ext
    change forward t (backward t (sumCoordinate t)) = sumCoordinate t
    simp
  · change forward t (backward t (rootCoordinate t)) = rootCoordinate t
    simp

/-- A genuine coefficient-preserving isomorphism of the entire original node algebra. -/
def quadraticEquiv (t : A) : Node A t ≃ₐ[A] QuadraticAlgebra t :=
  AlgEquiv.ofAlgHom (forward t) (backward t) (forward_backward t) (backward_forward t)

end DeJongAlterations.Algebra.NodeFamilyQuadratic
