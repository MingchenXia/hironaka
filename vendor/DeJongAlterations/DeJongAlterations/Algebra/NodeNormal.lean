import DeJongAlterations.Algebra.NodeNormalCoordinates
import DeJongAlterations.Algebra.NodeNormalIntersection
import Mathlib.RingTheory.Polynomial.IsIntegral

/-!
# Normality of the actual node over an integrally closed domain

The two actual coordinate localizations are polynomial Laurent algebras.
The literal coordinate quotient supplies their genuine regular-pair intersection.
-/

noncomputable section

namespace DeJongAlterations.Algebra.NodeNormal

open Polynomial NodeBlowupChart NodeFamilyLocalization

universe u

variable {A : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]

/-- The actual one-variable polynomial torus over a normal domain is normal. -/
theorem polynomialTorus_isIntegrallyClosed : IsIntegrallyClosed (PolynomialTorus A) := by
  exact isIntegrallyClosed_of_isLocalization _ (Submonoid.powers (Polynomial.X : A[X]))
    (powers_le_nonZeroDivisors_of_noZeroDivisors Polynomial.X_ne_zero)

/-- The actual first-coordinate localization of the node is normal. -/
theorem coordinate0_isIntegrallyClosed (t : A) :
    IsIntegrallyClosed (Localization.Away (coordinate t 0)) := by
  let := polynomialTorus_isIntegrallyClosed (A := A)
  exact IsIntegrallyClosed.of_equiv (coordinateLocalizationEquiv t).symm.toRingEquiv

/-- The actual second-coordinate localization of the node is normal. -/
theorem coordinate1_isIntegrallyClosed (t : A) :
    IsIntegrallyClosed (Localization.Away (coordinate t 1)) := by
  let := coordinate0_isIntegrallyClosed t
  exact IsIntegrallyClosed.of_equiv (swapLocalizationEquiv t).toRingEquiv

/-- The literal node with nonzero parameter over an integrally closed domain is integrally closed.
No Noetherian, regular-pair, localization-normality or intersection certificate is an input. -/
theorem node_isIntegrallyClosed (t : A) (ht : t ≠ 0) :
    IsIntegrallyClosed (Node A t) := by
  let := NodeDomain.nodeQuotient_isDomain t ht
  exact NodeNormalIntersection.isIntegrallyClosed_of_regular_pair
    (coordinate t 0) (coordinate t 1)
    (NodeDomain.nodeCoordinate_ne_zero t ht 0)
    (NodeDomain.nodeCoordinate_ne_zero t ht 1)
    (NodeNormalCoordinates.coordinate1_regular_mod_coordinate0 t)
    (coordinate0_isIntegrallyClosed t) (coordinate1_isIntegrallyClosed t)

end DeJongAlterations.Algebra.NodeNormal
