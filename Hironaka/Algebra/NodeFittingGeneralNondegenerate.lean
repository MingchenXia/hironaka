import Hironaka.Algebra.NodeFittingGeneralBaseChange

/-!
# Actual original polynomial differential-presentation minors at a nondegenerate jet

The actual pulled algebraic cotangent presentation of the same original
polynomial has derivative-ideal quotient equal to the original field.
No original geometric hypersurface or coherent-completion identification
is assumed or asserted.
-/

noncomputable section

namespace Hironaka.Algebra.NodeFittingGeneral

open NodeFormalMorse NodeVariableMorse MvPowerSeries

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {K : Type u} [Field K]

/-- The original actual derivative image ideal is exactly the native formal Jacobian image. -/
theorem formalDerivativeIdeal_eq_equationDerivativeIdeal (f : MvPolynomial (Fin 2) K) :
    formalDerivativeIdeal f = equationDerivativeIdeal (f : Series K) := by
  unfold formalDerivativeIdeal equationDerivativeIdeal originalJacobianIdeal
  rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]

/-- The genuine pulled cotangent presentation's actual first minors are the whole original constant kernel. -/
theorem formalPresentationFirstFittingIdeal_eq_constantKernel (f : MvPolynomial (Fin 2) K)
    (hc : constantCoeff (f : Series K) = 0)
    (h0 : coeff (Finsupp.single 0 1) (f : Series K) = 0)
    (h1 : coeff (Finsupp.single 1 1) (f : Series K) = 0)
    (hΔ : jetDiscriminant (f : Series K) ≠ 0) :
    formalPresentationFirstFittingIdeal f =
      RingHom.ker (equationConstantMap (f : Series K) hc).toRingHom := by
  rw [formalPresentationFirstFittingIdeal_eq_derivatives,
    formalDerivativeIdeal_eq_equationDerivativeIdeal,
    equationConstantMap_kernel _ hc h0 h1 hΔ]

/-- The actual quotient by the original pulled differential-presentation minors is the original field. -/
def formalMinorsQuotientEquiv (f : MvPolynomial (Fin 2) K)
    (hc : constantCoeff (f : Series K) = 0)
    (h0 : coeff (Finsupp.single 0 1) (f : Series K) = 0)
    (h1 : coeff (Finsupp.single 1 1) (f : Series K) = 0)
    (hΔ : jetDiscriminant (f : Series K) ≠ 0) :
    (FormalHypersurface f ⧸ formalPresentationFirstFittingIdeal f) ≃ₐ[K] K :=
  (Ideal.quotientEquivAlgOfEq K
    ((formalPresentationFirstFittingIdeal_eq_derivatives f).trans
      (formalDerivativeIdeal_eq_equationDerivativeIdeal f))).trans
    (equationJacobianQuotientEquiv (f : Series K) hc h0 h1 hΔ)

/-- The actual isomorphism retains the same original coefficient map. -/
@[simp]
theorem formalMinorsQuotientEquiv_coefficient (f : MvPolynomial (Fin 2) K)
    (hc : constantCoeff (f : Series K) = 0)
    (h0 : coeff (Finsupp.single 0 1) (f : Series K) = 0)
    (h1 : coeff (Finsupp.single 1 1) (f : Series K) = 0)
    (hΔ : jetDiscriminant (f : Series K) ≠ 0) (a : K) :
    formalMinorsQuotientEquiv f hc h0 h1 hΔ
      (Ideal.Quotient.mk (formalPresentationFirstFittingIdeal f)
        (Ideal.Quotient.mk (Ideal.span {(f : Series K)}) (C a))) = a := rfl

/-- The polynomial-side original coefficient reaches its own original value under the actual triangle. -/
@[simp]
theorem formalMinorsQuotientEquiv_polynomialCoefficient (f : MvPolynomial (Fin 2) K)
    (hc : constantCoeff (f : Series K) = 0)
    (h0 : coeff (Finsupp.single 0 1) (f : Series K) = 0)
    (h1 : coeff (Finsupp.single 1 1) (f : Series K) = 0)
    (hΔ : jetDiscriminant (f : Series K) ≠ 0) (a : K) :
    formalMinorsQuotientEquiv f hc h0 h1 hΔ
      (Ideal.Quotient.mk (formalPresentationFirstFittingIdeal f)
        (polynomialToFormal f (Ideal.Quotient.mk (polynomialIdeal f) (MvPolynomial.C a)))) = a := by
  rw [polynomialToFormal_coefficient, formalMinorsQuotientEquiv_coefficient]

end Hironaka.Algebra.NodeFittingGeneral
