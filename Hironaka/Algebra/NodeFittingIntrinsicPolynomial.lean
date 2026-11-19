import Hironaka.Algebra.NodeFittingModuleOneRelation
import Hironaka.Algebra.NodeFittingGeneralNondegenerate

/-!
# The genuine intrinsic first Fitting ideal of original polynomial differentials

The original native gradient and its entire proved kernel construct the
actual native finite matrix presentation. The original geometric family
completion comparison and ideal-sheaf gluing remain separate.
-/

noncomputable section

namespace Hironaka.Algebra.NodeFittingIntrinsic

open NodeFittingGeneral NodeFittingModule NodeFormalMorse

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {R : Type u} [CommRing R]

/-- The original genuine polynomial differential module's internally constructed actual presentation. -/
def polynomialDifferentialPresentation (f : MvPolynomial (Fin 2) R) :
    FiniteMatrixPresentation (R := PolynomialHypersurface f)
      (KaehlerDifferential R (PolynomialHypersurface f)) :=
  oneRelationPresentation (polynomialPresentation f).cotangentSpaceBasis (gradientVector f)
    (polynomialPresentation f).toExtension.toKaehler
    (toKaehler_surjective f) (toKaehler_kernel f)

/-- The same original actual kernel internally proves native finite presentation of the genuine differentials. -/
instance polynomialDifferentials_finitePresentation (f : MvPolynomial (Fin 2) R) :
    Module.FinitePresentation (PolynomialHypersurface f)
      (KaehlerDifferential R (PolynomialHypersurface f)) :=
  (polynomialDifferentialPresentation f).finitePresentation

/-- The whole intrinsic first Fitting ideal is exactly the original actual gradient minors ideal. -/
theorem polynomial_fittingIdeal_eq (f : MvPolynomial (Fin 2) R) :
    fittingIdeal (R := PolynomialHypersurface f)
      (M := KaehlerDifferential R (PolynomialHypersurface f)) 1 =
        presentationFirstFittingIdeal f :=
  fittingIdeal_oneRelation (polynomialPresentation f).cotangentSpaceBasis (gradientVector f)
    (polynomialPresentation f).toExtension.toKaehler
    (toKaehler_surjective f) (toKaehler_kernel f)

/-- The entire original pulled differential kernel internally supplies its actual native finite matrix presentation. -/
def formalDifferentialPresentation (f : MvPolynomial (Fin 2) R) :
    FiniteMatrixPresentation (R := FormalHypersurface f) (FormalModelDifferentials f) :=
  oneRelationPresentation (formalCotangentBasis f) (formalGradientVector f)
    (formalDifferentialMap f) (formalDifferential_surjective f) (formalDifferential_kernel f)

/-- The actual original pulled differential module is natively finitely presented. -/
instance formalDifferentials_finitePresentation (f : MvPolynomial (Fin 2) R) :
    Module.FinitePresentation (FormalHypersurface f) (FormalModelDifferentials f) :=
  (formalDifferentialPresentation f).finitePresentation

/-- The intrinsic pulled first Fitting ideal is the actual original formal gradient minors ideal. -/
theorem formal_fittingIdeal_eq (f : MvPolynomial (Fin 2) R) :
    fittingIdeal (R := FormalHypersurface f) (M := FormalModelDifferentials f) 1 =
      formalPresentationFirstFittingIdeal f :=
  fittingIdeal_oneRelation (formalCotangentBasis f) (formalGradientVector f)
    (formalDifferentialMap f) (formalDifferential_surjective f) (formalDifferential_kernel f)

/-- These are the actual original native formal derivative images, as whole ideals. -/
theorem formal_fittingIdeal_eq_derivatives (f : MvPolynomial (Fin 2) R) :
    fittingIdeal (R := FormalHypersurface f) (M := FormalModelDifferentials f) 1 =
      formalDerivativeIdeal f :=
  (formal_fittingIdeal_eq f).trans (formalPresentationFirstFittingIdeal_eq_derivatives f)

section Field

open NodeVariableMorse MvPowerSeries
variable {K : Type u} [Field K]

/-- The actual original formal hypersurface quotient by its intrinsic pulled differential Fitting ideal. -/
def intrinsicFormalSingularQuotientEquiv (f : MvPolynomial (Fin 2) K)
    (hc : constantCoeff (f : Series K) = 0)
    (h0 : coeff (Finsupp.single 0 1) (f : Series K) = 0)
    (h1 : coeff (Finsupp.single 1 1) (f : Series K) = 0)
    (hΔ : jetDiscriminant (f : Series K) ≠ 0) :
    (FormalHypersurface f ⧸ fittingIdeal (R := FormalHypersurface f)
      (M := FormalModelDifferentials f) 1) ≃ₐ[K] K :=
  (Ideal.quotientEquivAlgOfEq K (formal_fittingIdeal_eq f)).trans
    (formalMinorsQuotientEquiv f hc h0 h1 hΔ)

/-- The same original coefficient triangle survives the intrinsic singular quotient. -/
@[simp]
theorem intrinsicFormalSingularQuotientEquiv_coefficient (f : MvPolynomial (Fin 2) K)
    (hc : constantCoeff (f : Series K) = 0)
    (h0 : coeff (Finsupp.single 0 1) (f : Series K) = 0)
    (h1 : coeff (Finsupp.single 1 1) (f : Series K) = 0)
    (hΔ : jetDiscriminant (f : Series K) ≠ 0) (a : K) :
    intrinsicFormalSingularQuotientEquiv f hc h0 h1 hΔ
      (Ideal.Quotient.mk (fittingIdeal (R := FormalHypersurface f)
        (M := FormalModelDifferentials f) 1)
        (Ideal.Quotient.mk (Ideal.span {(f : Series K)}) (C a))) = a := rfl

end Field
end Hironaka.Algebra.NodeFittingIntrinsic
