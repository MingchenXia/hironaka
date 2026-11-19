import Hironaka.Algebra.ProjectiveSecantGeometricReducedLocalization
import Mathlib.RingTheory.EssentialFiniteness

/-!
# The actual fraction field of the original geometrically reduced finite-type domain is formally smooth
-/

noncomputable section

namespace Hironaka.Algebra.ProjectiveSecant

universe u

/-- The actual original geometric hypothesis internally makes its actual fraction field formally smooth over the same original coefficient field. -/
theorem formallySmooth_fractionRing_of_geometricallyReduced
    (k A K : Type u) [Field k] [CommRing A] [IsDomain A] [Field K]
    [Algebra k A] [Algebra k K] [Algebra A K] [IsScalarTower k A K]
    [IsFractionRing A K] [Algebra.FiniteType k A] [Algebra.IsGeometricallyReduced k A] :
    Algebra.FormallySmooth k K := by
  let : Algebra.IsGeometricallyReduced k K :=
    isGeometricallyReduced_of_isLocalization k A K (nonZeroDivisors A)
  let : Algebra.EssFiniteType A K := Algebra.EssFiniteType.of_isLocalization K (nonZeroDivisors A)
  let : Algebra.EssFiniteType k K := Algebra.EssFiniteType.comp k A K
  exact formallySmooth_of_isGeometricallyReduced k K

end Hironaka.Algebra.ProjectiveSecant
