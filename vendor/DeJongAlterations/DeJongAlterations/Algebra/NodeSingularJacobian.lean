import DeJongAlterations.Algebra.NodeSingularQuotient
import DeJongAlterations.Algebra.NodeSingularDerivative

/-!
# The literal derivative ideal and its actual quotient

This is the native formal derivative ideal. Identification with the first
Fitting ideal of the original completed coherent differential module is a
separate geometric comparison, not an input or a definition here.
-/

noncomputable section

namespace DeJongAlterations.Algebra.NodeSingular

open MvPowerSeries NodeNonsplit NodeFormalMorse

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {R : Type u} [CommRing R]

/-- The actual images of the two native partial derivatives of the original equation. -/
def jacobianIdeal (Q : Quadratic R) (h : R) : Ideal (Node Q h) :=
  (Ideal.span {MvPowerSeries.pderiv R (0 : Fin 2) (Q.series - C h),
    MvPowerSeries.pderiv R (1 : Fin 2) (Q.series - C h)}).map
      (Ideal.Quotient.mk (equationIdeal Q h))

/-- The derivative ideal is exactly the original coordinate ideal, scheme-theoretically. -/
theorem jacobianIdeal_eq_coordinateIdeal (Q : Quadratic R) (h : R) :
    jacobianIdeal Q h = coordinateIdeal Q h := by
  unfold jacobianIdeal
  rw [partialDerivativeIdeal_eq, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
  rfl

/-- Native formal derivatives and the original inverse-Hessian gradient give the same ideal. -/
theorem jacobianIdeal_eq_gradientIdeal (Q : Quadratic R) (h : R) :
    jacobianIdeal Q h = gradientIdeal Q h :=
  (jacobianIdeal_eq_coordinateIdeal Q h).trans (gradientIdeal_eq Q h).symm

/-- The original formal derivative quotient is canonically the original parameter zero locus. -/
def jacobianQuotientEquiv (Q : Quadratic R) (h : R) :
    (Node Q h ⧸ jacobianIdeal Q h) ≃ₐ[R] R ⧸ Ideal.span {h} :=
  (Ideal.quotientEquivAlgOfEq R (jacobianIdeal_eq_gradientIdeal Q h)).trans
    (gradientQuotientEquiv Q h)

@[simp]
theorem jacobianQuotientEquiv_coefficient (Q : Quadratic R) (h r : R) :
    jacobianQuotientEquiv Q h
      (Ideal.Quotient.mk (jacobianIdeal Q h) (Ideal.Quotient.mk (equationIdeal Q h) (C r))) =
      Ideal.Quotient.mk (Ideal.span {h}) r := by
  rfl

end DeJongAlterations.Algebra.NodeSingular
