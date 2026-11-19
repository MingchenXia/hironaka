import Hironaka.Geometry.ProjectiveSecantProjectionChartRelation
import Hironaka.Geometry.ProjectiveSecantProjectionChartPoint
import Hironaka.Algebra.ProjectiveSecantProjectionChartPolynomial
import Hironaka.Algebra.ProjectiveSecantProjectionUnramifiedLocalization

/-!
# The literal original projection-chart algebra is unramified at the same actual original source point

The whole original scheme projection's native chart comparison is a separate
remaining geometric step. No scheme-level unramifiedness is claimed here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveIdeal ProjectiveProjection ProjectiveProjectionCenter ProjectiveRationalPointCoordinates
open Algebra.ProjectiveSecant Algebra.ProjectiveLinearCoordinates

universe u

attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)
  {X : Scheme.{u}} (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]
  (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
  (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)

/-- The actual whole original source-chart algebra map of the literal original remaining-coordinate projection ratios. -/
def originalProjectionSourceChartMap (j : Fin (n + 1)) : HomogeneousChartRing k j →+*
    Γ(X, (i ≫ (coordinateAutomorphism k n (pointVector k n p hp) (pointVector_ne_zero k n p hp)).hom) ⁻¹ᵁ
      nativeCoordinateOpen j.succ) :=
  sourceProjectionChartMap k n j (tangentChartPolynomialMap k n
    (i ≫ (coordinateAutomorphism k n (pointVector k n p hp) (pointVector_ne_zero k n p hp)).hom) j.succ)

variable (s : Spec (CommRingCat.of k) ⟶ X)
  (hs : (s ≫ i) ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
  (hdim : topologicalKrullDim X ≤ n)
  (hx : s (⊥ : PrimeSpectrum k) ∈ (i ≫ projectiveSpaceStructure k (n + 1)).smoothLocus)

/-- Actual original geometric source, smooth rational point and outside centre in the computed tangent open internally produce native unramifiedness of the literal original remaining-ratio chart algebra at the actual source prime representing the SAME original point. No algebra generation, relation, source prime or derivative certificate is supplied. -/
theorem exists_original_projection_source_chart_isUnramifiedAt
    (hout : pointImage k n p ∉ Set.range i)
    (hc : pointImage k n p ∈ originalTangentOpen k n i s hs hdim hx) :
    ∃ (j : Fin (n + 1))
      (Q : PrimeSpectrum Γ(X,
        (i ≫ (coordinateAutomorphism k n (pointVector k n p hp) (pointVector_ne_zero k n p hp)).hom) ⁻¹ᵁ
          nativeCoordinateOpen j.succ)),
      (tangentSourceChart_isAffine k n
        (i ≫ (coordinateAutomorphism k n (pointVector k n p hp) (pointVector_ne_zero k n p hp)).hom) j.succ).fromSpec Q =
          s (⊥ : PrimeSpectrum k) ∧
      letI := (originalProjectionSourceChartMap k n i p hp j).toAlgebra
      Algebra.IsUnramifiedAt (HomogeneousChartRing k j) Q.asIdeal := by
  obtain ⟨j, Q, _, hQ, hder⟩ := exists_actual_projection_chart_prime_derivative k n i p hp s hs hdim hx hout hc
  let i' := i ≫ (coordinateAutomorphism k n (pointVector k n p hp) (pointVector_ne_zero k n p hp)).hom
  let φ := tangentChartPolynomialMap k n i' j.succ
  let K := projectionCoordinateTangentEquation k n p hp i s hs hdim hx
  let G := sourceProjectionPolynomial k n j K
  let t := sourceDiscardedRatio k n j φ
  let := (sourceProjectionChartMap k n j φ).toAlgebra
  have hgen : Algebra.adjoin (HomogeneousChartRing k j) {t} = ⊤ :=
    sourceProjectionChartMap_adjoin_eq_top k n j φ (tangentChartPolynomialMap_surjective k n i' j.succ)
  have hG : Polynomial.aeval t G = 0 := by
    change Polynomial.eval₂ (sourceProjectionChartMap k n j φ) t G = 0
    rw [sourceProjectionPolynomial_eval]
    exact projectionCoordinateTangentEquation_mem_kernel k n i p hp s hs hdim hx j.succ
  have hG' : Polynomial.aeval t G.derivative ∉ Q.asIdeal := by
    change Polynomial.eval₂ (sourceProjectionChartMap k n j φ) t G.derivative ∉ Q.asIdeal
    rw [sourceProjectionPolynomial_eval_derivative]
    simpa only [original_pderiv_coordinateDehom] using hder
  exact ⟨j, Q, hQ, isUnramifiedAt_of_monogenic_relation t hgen G hG Q.asIdeal hG'⟩

end Hironaka.Geometry.ProjectiveSecant
