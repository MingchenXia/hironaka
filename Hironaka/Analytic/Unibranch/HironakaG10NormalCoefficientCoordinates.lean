import Hironaka.Resolution.HironakaRelativeNormalNormalPowerSpread
import Hironaka.Resolution.HironakaG10ArtinianParameterPullback

/-! # Actual normal coefficients as moving quotient coordinates -/
set_option autoImplicit false
namespace Hironaka.Analytic.Unibranch.HironakaG10NormalCoefficientCoordinates
open Hironaka Hironaka
  OkaRelationSheaf HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaActualRelativeCoefficientGerms

/-- The actual monomial-basis coordinate of the normal-power quotient is the
same analytic coefficient germ used in Artinian parameter substitution. -/
theorem normalMonomialBasis_repr_eq_coefficient (d t q : ℕ)
    (g : HolGerm (ComplexModel (d+t))) (α : normalExponentIndex t q) :
    let := tangentAlgebra d t
    let := normalExponentFintype t q
    (normalMonomialBasis d t q).repr
        (Ideal.Quotient.mk (normalIdeal d t ^ q) g) α =
      actualNormalAnalyticCoefficientGerm d t g α.val := by
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  have hcoord : (normalMonomialBasis d t q).repr
      (Ideal.Quotient.mk (normalIdeal d t ^ q) g) α =
      actualNormalJetCoordinates d t q g α := by
    change (Pi.basisFun (HolGerm (ComplexModel d)) (normalExponentIndex t q)).repr
      ((normalPowerLinearEquiv d t q).symm
        (Ideal.Quotient.mk (normalIdeal d t ^ q) g)) α =
      ((normalPowerLinearEquiv d t q).symm
        (Ideal.Quotient.mk (normalIdeal d t ^ q) g)) α
    simp only [Pi.basisFun_repr]
  exact hcoord.trans ((actualNormalTaylorPolynomial_coefficient d t q g α).symm.trans
    (actualNormalTaylorPolynomial_coefficient_eq_germ d t q g α.val α.property))

end Hironaka.Analytic.Unibranch.HironakaG10NormalCoefficientCoordinates
