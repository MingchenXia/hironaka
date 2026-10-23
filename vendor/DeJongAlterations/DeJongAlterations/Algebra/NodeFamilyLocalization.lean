import DeJongAlterations.Algebra.NodeFamilyFlat
import Mathlib.RingTheory.Smooth.Basic

/-! The actual coordinate-unit node chart is a polynomial torus over the coefficient base. -/

noncomputable section

open Polynomial

namespace DeJongAlterations.Algebra.NodeFamilyLocalization

open NodeBlowupChart

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type u} [CommRing A]

abbrev PolynomialTorus (A : Type u) [CommRing A] := Localization.Away (X : A[X])
abbrev CoordinateOpen (t : A) := Localization.Away (coordinate t 0)

/-- The actual polynomial-torus evaluation `u↦U`, `v↦t/U`. -/
def nodeEvaluationPolynomial (t : A) : MvPolynomial (Fin 2) A →ₐ[A] PolynomialTorus A :=
  MvPolynomial.aeval ![algebraMap A[X] (PolynomialTorus A) X,
    algebraMap A (PolynomialTorus A) t * IsLocalization.Away.invSelf (X : A[X])]

private theorem evaluation_ideal (t : A) :
    NodeChart.uChartIdeal A t ≤ RingHom.ker (nodeEvaluationPolynomial t).toRingHom := by
  apply Ideal.span_le.mpr
  rintro _ rfl
  change nodeEvaluationPolynomial t
    (MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C t) = 0
  simp only [nodeEvaluationPolynomial, map_sub, map_mul, MvPolynomial.aeval_X,
    MvPolynomial.aeval_C, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [mul_left_comm, IsLocalization.Away.mul_invSelf, mul_one, sub_self]

/-- Evaluation descends through the literal node quotient over an arbitrary base ring. -/
def nodeEvaluation (t : A) : Node A t →ₐ[A] PolynomialTorus A :=
  Ideal.Quotient.liftₐ _ (nodeEvaluationPolynomial t) (fun _ h ↦ evaluation_ideal t h)

@[simp]
theorem nodeEvaluation_coordinate0 (t : A) :
    nodeEvaluation t (coordinate t 0) = algebraMap A[X] (PolynomialTorus A) X := by
  simp [nodeEvaluation, nodeEvaluationPolynomial, coordinate]

@[simp]
theorem nodeEvaluation_coordinate1 (t : A) :
    nodeEvaluation t (coordinate t 1) = algebraMap A (PolynomialTorus A) t *
      IsLocalization.Away.invSelf (X : A[X]) := by
  simp [nodeEvaluation, nodeEvaluationPolynomial, coordinate]

/-- The actual localization homomorphism obtained from evaluation. -/
def forward (t : A) : CoordinateOpen t →ₐ[A] PolynomialTorus A :=
  IsLocalization.Away.liftAlgHom (coordinate t 0) (f := nodeEvaluation t) (by
    rw [nodeEvaluation_coordinate0]
    exact IsLocalization.Away.algebraMap_isUnit _)

@[simp]
theorem forward_algebraMap (t : A) (a : Node A t) :
    forward t (algebraMap (Node A t) (CoordinateOpen t) a) = nodeEvaluation t a := by
  simp only [forward, IsLocalization.Away.coe_liftAlgHom, IsLocalization.Away.lift_eq]
  rfl

/-- The actual coefficient homomorphism sending the polynomial variable to the node coordinate. -/
def backwardCoefficient (t : A) : A[X] →ₐ[A] CoordinateOpen t :=
  Polynomial.aeval (algebraMap (Node A t) (CoordinateOpen t) (coordinate t 0))

/-- The actual reverse localization homomorphism. -/
def backward (t : A) : PolynomialTorus A →ₐ[A] CoordinateOpen t :=
  IsLocalization.Away.liftAlgHom (X : A[X]) (f := backwardCoefficient t) (by
    change IsUnit ((Polynomial.aeval _) X)
    rw [Polynomial.aeval_X]
    exact IsLocalization.Away.algebraMap_isUnit _)

@[simp]
theorem backward_algebraMap (t : A) (a : A[X]) :
    backward t (algebraMap A[X] (PolynomialTorus A) a) = backwardCoefficient t a := by
  simp only [backward, IsLocalization.Away.coe_liftAlgHom, IsLocalization.Away.lift_eq]
  rfl

private theorem map_invSelf {R S : Type u} [CommRing R] [CommRing S] (r : R) (s : S)
    (f : Localization.Away r →+* Localization.Away s)
    (h : f (algebraMap R (Localization.Away r) r) = algebraMap S (Localization.Away s) s) :
    f (IsLocalization.Away.invSelf r) = IsLocalization.Away.invSelf s := by
  apply (IsLocalization.Away.algebraMap_isUnit s :
    IsUnit (algebraMap S (Localization.Away s) s)).mul_left_cancel
  calc
    _ = f (algebraMap R (Localization.Away r) r * IsLocalization.Away.invSelf r) := by
      rw [map_mul, h]
    _ = 1 := by rw [IsLocalization.Away.mul_invSelf, map_one]
    _ = _ := (IsLocalization.Away.mul_invSelf s).symm

@[simp]
theorem backward_invSelf (t : A) :
    backward t (IsLocalization.Away.invSelf (X : A[X])) =
      IsLocalization.Away.invSelf (coordinate t 0) := by
  apply map_invSelf (X : A[X]) (coordinate t 0) (backward t).toRingHom
  change backward t (algebraMap A[X] (PolynomialTorus A) X) = _
  rw [backward_algebraMap]
  exact Polynomial.aeval_X _

private theorem backward_nodeEvaluation (t : A) :
    (backward t).comp (nodeEvaluation t) =
      IsScalarTower.toAlgHom A (Node A t) (CoordinateOpen t) := by
  apply Ideal.Quotient.algHom_ext
  ext i
  fin_cases i
  · change backward t (nodeEvaluation t (coordinate t 0)) =
      algebraMap (Node A t) (CoordinateOpen t) (coordinate t 0)
    rw [nodeEvaluation_coordinate0, backward_algebraMap]
    exact Polynomial.aeval_X _
  · change backward t (nodeEvaluation t (coordinate t 1)) =
      algebraMap (Node A t) (CoordinateOpen t) (coordinate t 1)
    rw [nodeEvaluation_coordinate1, map_mul, AlgHom.commutes, backward_invSelf]
    have hp : coordinate t 0 * coordinate t 1 = algebraMap A (Node A t) t :=
      NodeDomain.nodeCoordinateProduct t
    calc
      _ = algebraMap (Node A t) (CoordinateOpen t) (coordinate t 0 * coordinate t 1) *
          IsLocalization.Away.invSelf (coordinate t 0) := by
        rw [hp, ← IsScalarTower.algebraMap_apply]
      _ = algebraMap (Node A t) (CoordinateOpen t) (coordinate t 1) *
          (algebraMap (Node A t) (CoordinateOpen t) (coordinate t 0) *
            IsLocalization.Away.invSelf (coordinate t 0)) := by rw [map_mul]; ring
      _ = _ := by rw [IsLocalization.Away.mul_invSelf, mul_one]

private theorem backward_forward (t : A) : (backward t).comp (forward t) = AlgHom.id A _ := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (coordinate t 0))
  apply RingHom.ext
  intro a
  change backward t (forward t (algebraMap (Node A t) (CoordinateOpen t) a)) =
    algebraMap (Node A t) (CoordinateOpen t) a
  rw [forward_algebraMap]
  exact AlgHom.congr_fun (backward_nodeEvaluation t) a

private theorem forward_backward (t : A) : (forward t).comp (backward t) = AlgHom.id A _ := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (X : A[X]))
  have hcoef : (forward t).comp (backwardCoefficient t) =
      IsScalarTower.toAlgHom A A[X] (PolynomialTorus A) := by
    ext
    change forward t (backwardCoefficient t X) = algebraMap A[X] (PolynomialTorus A) X
    rw [show backwardCoefficient t X =
      algebraMap (Node A t) (CoordinateOpen t) (coordinate t 0) from Polynomial.aeval_X _]
    rw [forward_algebraMap, nodeEvaluation_coordinate0]
  apply RingHom.ext
  intro a
  change forward t (backward t (algebraMap A[X] (PolynomialTorus A) a)) =
    algebraMap A[X] (PolynomialTorus A) a
  rw [backward_algebraMap]
  exact AlgHom.congr_fun hcoef a

/-- A coefficient-preserving isomorphism of the whole actual coordinate localization with a polynomial torus. -/
def coordinateLocalizationEquiv (t : A) : CoordinateOpen t ≃ₐ[A] PolynomialTorus A :=
  AlgEquiv.ofAlgHom (forward t) (backward t) (forward_backward t) (backward_forward t)

/-- The actual polynomial torus is smooth over every commutative coefficient ring. -/
theorem polynomialTorus_smooth : Algebra.Smooth A (PolynomialTorus A) := by
  let : Algebra.Smooth A A[X] := {}
  let : Algebra.Smooth A[X] (PolynomialTorus A) := Algebra.Smooth.of_isLocalization_Away X
  exact Algebra.Smooth.comp A A[X] (PolynomialTorus A)

/-- Genuine smoothness of the actual node coefficient algebra after inverting its first coordinate. -/
theorem coordinateOpen_smooth (t : A) : Algebra.Smooth A (CoordinateOpen t) := by
  let : Algebra.Smooth A (PolynomialTorus A) := polynomialTorus_smooth
  exact Algebra.Smooth.of_equiv (coordinateLocalizationEquiv t).symm

/-- The actual node-coordinate interchange induces an isomorphism of their actual localizations. -/
def swapLocalizationEquiv (t : A) : CoordinateOpen t ≃ₐ[A]
    Localization.Away (coordinate t 1) :=
  IsLocalization.algEquivOfAlgEquiv _ _ (nodeSwap t) (by
    rw [Submonoid.map_powers, nodeSwap_coordinate0])

/-- Both actual coordinate-unit node algebras are smooth over the original coefficient ring. -/
theorem coordinateOpen_smooth_of_index (t : A) (i : Fin 2) :
    Algebra.Smooth A (Localization.Away (coordinate t i)) := by
  fin_cases i
  · exact coordinateOpen_smooth t
  · let : Algebra.Smooth A (CoordinateOpen t) := coordinateOpen_smooth t
    exact Algebra.Smooth.of_equiv (swapLocalizationEquiv t)

end DeJongAlterations.Algebra.NodeFamilyLocalization
