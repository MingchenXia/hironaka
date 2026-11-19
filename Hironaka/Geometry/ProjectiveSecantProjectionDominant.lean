import Hironaka.Geometry.FiniteVarietyDominance
import Hironaka.Geometry.ProjectiveCurveFibrationCharts
import Hironaka.Geometry.ProjectiveProjectionPointFinite
import Mathlib.RingTheory.KrullDimension.Polynomial

/-!
# Original full-dimensional finite projective projections are actually dominant
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveProjectionPoint ProjectiveRationalPointCoordinates

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual native polynomial affine chart computes the dimension of the entire original projective target. -/
theorem projectiveSpace_dimension (k : Type u) [Field k] (n : ℕ) :
    topologicalKrullDim (projectiveSpace k n) = n := by
  rw [← FunctionFieldDimension.topologicalKrullDim_eq_of_openImmersion
    (projectiveSpaceStructure k n) (ProjectiveCurveFibration.affineChart k n)]
  change topologicalKrullDim (PrimeSpectrum (MvPolynomial (Fin n) k)) = n
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  simp [MvPolynomial.ringKrullDim_of_isNoetherianRing]

/-- The SAME original finite projection is dominant by its actual original dimension, without any supplied image or dominance certificate. -/
theorem originalProjection_isDominant_of_dimension_eq
    (k : Type u) [Field k] (n : ℕ) {X : Scheme.{u}} [IsIntegral X]
    (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]
    (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
    (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
    (hout : pointImage k n p ∉ Set.range i) (hdim : topologicalKrullDim X = n) :
    IsDominant (projectionFromPoint k n p hp i hout) := by
  let : IsFinite (projectionFromPoint k n p hp i hout) := projectionFromPoint_isFinite k n p hp i hout
  let : IsVariety (projectiveSpaceStructure k n) := .mk
  apply FiniteVarietyDominance.isDominant_of_dimension_le (projectiveSpaceStructure k n)
  rw [projectiveSpace_dimension, hdim]

end Hironaka.Geometry.ProjectiveSecant
