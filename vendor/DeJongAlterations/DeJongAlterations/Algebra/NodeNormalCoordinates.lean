import DeJongAlterations.Algebra.NodeFamilyLocalization
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# The actual coordinate quotient of the literal node

Killing the first original coordinate gives the polynomial ring over the actual
parameter quotient. Its original second-coordinate class is therefore regular.
-/

noncomputable section

open Polynomial

namespace DeJongAlterations.Algebra.NodeNormalCoordinates

open NodeBlowupChart

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type u} [CommRing A]

/-- The actual parameter quotient of the original coefficient ring. -/
abbrev ParameterQuotient (t : A) := A ⧸ Ideal.span {t}

/-- The literal first-coordinate ideal in the original node quotient. -/
abbrev coordinateIdeal (t : A) : Ideal (Node A t) := Ideal.span {coordinate t 0}

/-- The actual quotient of the original node by its first coordinate. -/
abbrev CoordinateQuotient (t : A) := Node A t ⧸ coordinateIdeal t

/-- The original node quotient homomorphism killing its first coordinate. -/
def mkCoordinate (t : A) : Node A t →ₐ[A] CoordinateQuotient t :=
  Ideal.Quotient.mkₐ A (coordinateIdeal t)

/-- The actual first coordinate vanishes in its actual quotient. -/
theorem mkCoordinate_coordinate0 (t : A) : mkCoordinate t (coordinate t 0) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

/-- The original parameter also vanishes in this actual coordinate quotient. -/
theorem mkCoordinate_parameter (t : A) :
    mkCoordinate t (algebraMap A (Node A t) t) = 0 := by
  have h : mkCoordinate t (coordinate t 0 * coordinate t 1) =
      mkCoordinate t (algebraMap A (Node A t) t) :=
    congrArg (mkCoordinate t) (NodeDomain.nodeCoordinateProduct t)
  rw [map_mul, mkCoordinate_coordinate0] at h
  exact h.symm.trans (zero_mul (mkCoordinate t (coordinate t 1)))

/-- The actual polynomial substitution `u↦0`, `v↦V`, with coefficients reduced modulo the parameter. -/
def forwardPolynomial (t : A) : MvPolynomial (Fin 2) A →ₐ[A] (ParameterQuotient t)[X] :=
  MvPolynomial.aeval ![0, X]

private theorem forwardPolynomial_ideal (t : A) :
    NodeChart.uChartIdeal A t ≤ RingHom.ker (forwardPolynomial t).toRingHom := by
  apply Ideal.span_le.mpr
  rintro _ rfl
  change forwardPolynomial t (MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C t) = 0
  simp only [forwardPolynomial, map_sub, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
    Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul, zero_sub]
  have ht : algebraMap A (ParameterQuotient t) t = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  change -C (algebraMap A (ParameterQuotient t) t) = 0
  rw [ht, map_zero, neg_zero]

/-- Substitution descends through the entire actual node relation. -/
def forwardNode (t : A) : Node A t →ₐ[A] (ParameterQuotient t)[X] :=
  Ideal.Quotient.liftₐ _ (forwardPolynomial t) (fun _ h => forwardPolynomial_ideal t h)

@[simp]
theorem forwardNode_coordinate0 (t : A) : forwardNode t (coordinate t 0) = 0 := by
  simp [forwardNode, coordinate, forwardPolynomial]

@[simp]
theorem forwardNode_coordinate1 (t : A) : forwardNode t (coordinate t 1) = X := by
  simp [forwardNode, coordinate, forwardPolynomial]

private theorem forwardNode_coordinateIdeal (t : A) :
    coordinateIdeal t ≤ RingHom.ker (forwardNode t).toRingHom := by
  apply Ideal.span_le.mpr
  rintro _ rfl
  exact forwardNode_coordinate0 t

/-- The actual forward homomorphism on the entire first-coordinate quotient. -/
def forward (t : A) : CoordinateQuotient t →ₐ[A] (ParameterQuotient t)[X] :=
  Ideal.Quotient.liftₐ _ (forwardNode t) (fun _ h => forwardNode_coordinateIdeal t h)

@[simp]
theorem forward_mkCoordinate (t : A) (a : Node A t) :
    forward t (mkCoordinate t a) = forwardNode t a := rfl

/-- The original coefficient map genuinely factors through the actual parameter quotient. -/
def quotientCoefficient (t : A) : ParameterQuotient t →ₐ[A] CoordinateQuotient t :=
  Ideal.Quotient.liftₐ _ (Algebra.ofId A (CoordinateQuotient t)) (fun a ha => by
    have hI : Ideal.span {t} ≤ RingHom.ker (algebraMap A (CoordinateQuotient t)) := by
      apply Ideal.span_le.mpr
      intro b hb
      have hbt : b = t := Set.mem_singleton_iff.mp hb
      change algebraMap A (CoordinateQuotient t) b = 0
      rw [hbt]
      exact ((mkCoordinate t).commutes t).symm.trans (mkCoordinate_parameter t)
    exact hI ha)

@[simp]
theorem quotientCoefficient_mk (t a : A) :
    quotientCoefficient t (Ideal.Quotient.mk (Ideal.span {t}) a) =
      mkCoordinate t (algebraMap A (Node A t) a) := rfl

/-- Evaluation in the actual surviving original coordinate is the reverse homomorphism. -/
def backward (t : A) : (ParameterQuotient t)[X] →ₐ[A] CoordinateQuotient t :=
  Polynomial.eval₂AlgHom (quotientCoefficient t) (mkCoordinate t (coordinate t 1))
    (fun a => Commute.all (quotientCoefficient t a) (mkCoordinate t (coordinate t 1)))

@[simp]
theorem backward_C (t : A) (a : ParameterQuotient t) :
    backward t (Polynomial.C a) = quotientCoefficient t a := by
  simp [backward, Polynomial.eval₂AlgHom]

@[simp]
theorem backward_X (t : A) : backward t X = mkCoordinate t (coordinate t 1) := by
  simp [backward, Polynomial.eval₂AlgHom]

private theorem forward_backward (t : A) : (forward t).comp (backward t) = AlgHom.id A _ := by
  apply AlgHom.coe_ringHom_injective
  apply Polynomial.ringHom_ext
  · intro b
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    change forward t (backward t (C (Ideal.Quotient.mk (Ideal.span {t}) a))) =
      C (Ideal.Quotient.mk (Ideal.span {t}) a)
    rw [backward_C, quotientCoefficient_mk, AlgHom.commutes, AlgHom.commutes]
    rfl
  · change forward t (backward t X) = X
    rw [backward_X, forward_mkCoordinate, forwardNode_coordinate1]

private theorem backward_forward (t : A) : (backward t).comp (forward t) = AlgHom.id A _ := by
  apply Ideal.Quotient.algHom_ext
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change backward t (forward t (mkCoordinate t (coordinate t 0))) = mkCoordinate t (coordinate t 0)
    rw [mkCoordinate_coordinate0, map_zero, map_zero]
  · change backward t (forward t (mkCoordinate t (coordinate t 1))) = mkCoordinate t (coordinate t 1)
    rw [forward_mkCoordinate, forwardNode_coordinate1, backward_X]

/-- The actual original coordinate quotient is the literal polynomial ring over the actual parameter quotient. -/
def coordinateQuotientEquiv (t : A) : CoordinateQuotient t ≃ₐ[A] (ParameterQuotient t)[X] :=
  AlgEquiv.ofAlgHom (forward t) (backward t) (forward_backward t) (backward_forward t)

/-- The actual surviving original coordinate is exactly the polynomial variable. -/
theorem coordinateQuotientEquiv_coordinate1 (t : A) :
    coordinateQuotientEquiv t (mkCoordinate t (coordinate t 1)) = X :=
  forwardNode_coordinate1 t

/-- The original second coordinate is genuinely regular modulo the original first coordinate. -/
theorem coordinate1_regular_mod_coordinate0 (t : A) :
    IsRegular (Ideal.Quotient.mk (Ideal.span {coordinate t 0}) (coordinate t 1)) := by
  have hl : IsLeftRegular (Ideal.Quotient.mk (Ideal.span {coordinate t 0}) (coordinate t 1)) := by
    intro a b hab
    apply (coordinateQuotientEquiv t).injective
    have h := congrArg (coordinateQuotientEquiv t) hab
    change coordinateQuotientEquiv t (mkCoordinate t (coordinate t 1) * a) =
      coordinateQuotientEquiv t (mkCoordinate t (coordinate t 1) * b) at h
    rw [map_mul, map_mul, coordinateQuotientEquiv_coordinate1] at h
    exact Polynomial.isRegular_X.left h
  exact ⟨hl, hl.right_of_commute (fun a => Commute.all _ a)⟩

end DeJongAlterations.Algebra.NodeNormalCoordinates
