import Hironaka.Algebra.ProjectiveSecantGeneralDimension
import Hironaka.Geometry.ProjectiveSecantChartDimension

/-!
# An actual chart relation for an arbitrary original closed projective source
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization TopologicalSpace

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveIdeal ProjectiveProjection
open Algebra.ProjectiveProjectionFinite Algebra.ProjectiveSecant

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] Algebra.ProjectiveSecant.chartAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ) {X : Scheme.{u}}
  (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i] (j : Fin (n + 1))

/-- Original dimension alone supplies a relation in the whole original chart ring, without reducing it. -/
theorem exists_original_chart_relation_general (hdim : topologicalKrullDim X < n) :
    ∃ P : CoordinateRing k j, P ≠ 0 ∧
      remainingPolynomialMap k n (representativeIdeal k n i) j P = 0 := by
  let A := originalChartRing k n i j
  let : Algebra.FiniteType k A := chart_finiteType k n (representativeIdeal k n i) j
  apply exists_nonzero_relation_of_dimension_lt_general k A
    (remainingPolynomialMap k n (representativeIdeal k n i) j)
  have hcard : Fintype.card (ChartIndex j) = n := by simp [ChartIndex]
  rw [hcard]
  exact lt_of_le_of_lt (originalChartRing_dimension_le k n i j) hdim

end Hironaka.Geometry.ProjectiveSecant
