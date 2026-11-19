import Hironaka.Algebra.ProjectiveProjectionFiniteChartCompatibility
import Hironaka.Geometry.ProjectiveIdealRepresentation

/-!
# Actual remaining-coordinate algebra on an original projective quotient chart
-/

noncomputable section

open MvPolynomial AlgebraicGeometry HomogeneousLocalization

namespace Hironaka.Algebra.ProjectiveSecant

open Geometry.ProjectiveIdeal ProjectiveProjectionFinite

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)
  (J : HomogeneousIdeal (ProjectiveGrading k (n + 1))) (j : Fin (n + 1))

/-- The coefficient field acts through the literal original full chart map. -/
@[instance_reducible]
def chartAlgebra : Algebra k (QuotientChart k n J j) :=
  ((fullChartPolynomialMap k n J j).comp (MvPolynomial.C : k →+* CoordinateRing k j.succ)).toAlgebra

attribute [local instance] chartAlgebra

/-- The original surjective coordinate map retains the actual coefficient field. -/
def fullPolynomialAlgHom : CoordinateRing k j.succ →ₐ[k] QuotientChart k n J j where
  __ := fullChartPolynomialMap k n J j
  commutes' _ := rfl

/-- The actual quotient chart is finite type over the original coefficient field. -/
theorem chart_finiteType : Algebra.FiniteType k (QuotientChart k n J j) :=
  Algebra.FiniteType.of_surjective (fullPolynomialAlgHom k n J j)
    (fullChartPolynomialMap_surjective k n J j)

/-- The literal original remaining affine coordinates map into the same original quotient chart. -/
def remainingPolynomialMap : CoordinateRing k j →ₐ[k] QuotientChart k n J j :=
  (fullPolynomialAlgHom k n J j).comp (MvPolynomial.rename (chartIndexLift n j))

/-- The whole original remaining-coordinate map retains every original coordinate value. -/
theorem remainingPolynomialMap_apply (P : CoordinateRing k j) :
    remainingPolynomialMap k n J j P =
      fullChartPolynomialMap k n J j (MvPolynomial.rename (chartIndexLift n j) P) := rfl

/-- Actual homogeneous lifting uses exactly the original remaining homogeneous variables and denominator. -/
theorem remainingPolynomialMap_dehom {d : ℕ} {F : MvPolynomial (Fin (n + 1)) k}
    (hF : F.IsHomogeneous d) :
    remainingPolynomialMap k n J j (coordinateDehom j F) =
      Away.map (GradedQuotient.gradedMk (ProjectiveGrading k (n + 1)) J.toIdeal) (X j.succ)
        (Away.mk (ProjectiveGrading k (n + 1)) (MvPolynomial.isHomogeneous_X k j.succ)
          d (MvPolynomial.rename Fin.succ F) (by simpa using hF.rename_isHomogeneous (f := Fin.succ))) := by
  rw [remainingPolynomialMap_apply, coordinateDehom_rename_succ]
  change Away.map (GradedQuotient.gradedMk (ProjectiveGrading k (n + 1)) J.toIdeal) (X j.succ)
    (homogeneousChartRatioHom j.succ (coordinateDehom j.succ (MvPolynomial.rename Fin.succ F))) = _
  rw [homogeneousChartRatioHom_dehom_of_isHomogeneous j.succ (hF.rename_isHomogeneous (f := Fin.succ))]

end Hironaka.Algebra.ProjectiveSecant
