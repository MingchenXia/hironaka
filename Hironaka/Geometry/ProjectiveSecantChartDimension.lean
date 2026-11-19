import Hironaka.Algebra.ProjectiveSecantChart
import Hironaka.Algebra.ProjectiveSecantDimension
import Hironaka.Geometry.ProjectiveProjectionClosedSubscheme
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.KrullDimension

/-!
# Original integral projective schemes supply the actual secant-chart dimension bound
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

/-- The actual remaining-coordinate chart ring of the original closed immersion's entire kernel. -/
abbrev originalChartRing := QuotientChart k n (representativeIdeal k n i) j

/-- Its literal native homogeneous chart is an actual open subscheme of the original source. -/
def chartToOriginal : Spec (CommRingCat.of (originalChartRing k n i j)) ⟶ X :=
  Proj.awayι (GradedQuotient.grading (ProjectiveGrading k (n + 1)) (representativeIdeal k n i).toIdeal)
      (Ideal.Quotient.mk (representativeIdeal k n i).toIdeal (MvPolynomial.X j.succ))
      ((GradedQuotient.gradedMk (ProjectiveGrading k (n + 1)) (representativeIdeal k n i).toIdeal).map_mem
        (MvPolynomial.isHomogeneous_X k j.succ)) (by decide : 0 < (1 : ℕ)) ≫
    (representativeIso k n i).inv

instance chartToOriginal_isOpenImmersion : IsOpenImmersion (chartToOriginal k n i j) := by
  dsimp only [chartToOriginal]
  infer_instance

/-- Nonemptiness of the actual chart derives its domain structure from original integrality. -/
theorem originalChartRing_isDomain [IsIntegral X] [Nontrivial (originalChartRing k n i j)] :
    IsDomain (originalChartRing k n i j) := by
  let : Nonempty (Spec (CommRingCat.of (originalChartRing k n i j))) := inferInstance
  let : IsIntegral (Spec (CommRingCat.of (originalChartRing k n i j))) :=
    isIntegral_of_isOpenImmersion (chartToOriginal k n i j)
  exact (affine_isIntegral_iff (CommRingCat.of (originalChartRing k n i j))).mp inferInstance

/-- The actual native chart's dimension is bounded by that of the original source, without a dimension certificate. -/
theorem originalChartRing_dimension_le : ringKrullDim (originalChartRing k n i j) ≤ topologicalKrullDim X := by
  have h := (chartToOriginal k n i j).isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
  change topologicalKrullDim (PrimeSpectrum (originalChartRing k n i j)) ≤ topologicalKrullDim X at h
  rwa [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] at h

/-- The original dimension bound internally produces an actual remaining-coordinate equation on the original chart. -/
theorem exists_original_chart_relation [IsIntegral X] (hdim : topologicalKrullDim X < n) :
    ∃ P : CoordinateRing k j, P ≠ 0 ∧
      remainingPolynomialMap k n (representativeIdeal k n i) j P = 0 := by
  let A := originalChartRing k n i j
  rcases subsingleton_or_nontrivial A with hsub | hnon
  · let := hsub
    exact ⟨1, one_ne_zero, Subsingleton.elim _ _⟩
  · let := hnon
    let : IsDomain A := originalChartRing_isDomain k n i j
    let : Algebra.FiniteType k A := chart_finiteType k n (representativeIdeal k n i) j
    apply exists_nonzero_relation_of_dimension_lt k A (remainingPolynomialMap k n (representativeIdeal k n i) j)
    have hcard : Fintype.card (ChartIndex j) = n := by simp [ChartIndex]
    rw [hcard]
    exact lt_of_le_of_lt (originalChartRing_dimension_le k n i j) hdim

end Hironaka.Geometry.ProjectiveSecant
