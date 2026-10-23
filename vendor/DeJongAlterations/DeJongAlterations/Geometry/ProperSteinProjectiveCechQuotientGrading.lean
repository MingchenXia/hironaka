import DeJongAlterations.Geometry.ProperSteinProjectiveCechNativeAway
import DeJongAlterations.Geometry.ProperSteinProjectiveCechFiniteGraded
import DeJongAlterations.Algebra.ProjectiveIdealGradedQuotient

/-!
# The SAME actual original homogeneous quotient and its finite coordinate cohomology

Natural and integral gradings retain the SAME original ideal, quotient,
polynomial scalar action and actual homogeneous component images.
No field, desired decomposition or target cohomology-finiteness certificate is assumed.
-/

universe u
open CategoryTheory AlgebraicGeometry
open DeJongAlterations.Geometry.ProjectiveIdeal
namespace DeJongAlterations.Geometry.ProperSteinProjectiveCech
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {K I : Type u} [CommRing K] [LinearOrder I] [Fintype I]
attribute [local instance] MvPolynomial.gradedAlgebra

omit [LinearOrder I] in
/-- The ENTIRE original naturally homogeneous ideal is homogeneous in the SAME integral grading. -/
theorem polynomialHomogeneousIdeal_integral
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule I K)) :
    J.toIdeal.IsHomogeneous (polynomialIntegralGrading (K := K) (I := I)) := by
  obtain ⟨s, hs⟩ :=
    (Ideal.IsHomogeneous.iff_exists (MvPolynomial.homogeneousSubmodule I K) J.toIdeal).mp
      J.isHomogeneous
  rw [hs]
  apply Ideal.homogeneous_span
  rintro p ⟨q, _, rfl⟩
  obtain ⟨d, hd⟩ := q.property
  exact ⟨(d : ℤ), (polynomialNatIntegralHomogeneous_iff q.val d).mp hd⟩

/-- The genuine integral component of the SAME original polynomial ideal quotient. -/
def polynomialQuotientIntegralPiece
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule I K)) (k : ℤ) :
    Submodule K (MvPolynomial I K ⧸ J.toIdeal) :=
  GradedQuotient.grading (polynomialIntegralGrading (K := K) (I := I)) J.toIdeal k

/-- Original homogeneity internally produces the native decomposition of the SAME actual quotient. -/
instance polynomialQuotientIntegralDecomposition
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule I K)) :
    DirectSum.Decomposition (polynomialQuotientIntegralPiece J) :=
  (GradedQuotient.gradedRing (polynomialIntegralGrading (K := K) (I := I)) J.toIdeal
    (polynomialHomogeneousIdeal_integral J)).toDecomposition

/-- The SAME actual polynomial-module scalar action preserves the original integral quotient degrees. -/
instance polynomialQuotientIntegralGradedSMul
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule I K)) :
    SetLike.GradedSMul (polynomialIntegralGrading (K := K) (I := I))
      (polynomialQuotientIntegralPiece J) where
  smul_mem := by
    intro i j p q hp hq
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hq
    refine Submodule.mem_map.mpr ⟨p * a, SetLike.mul_mem_graded hp ha, ?_⟩
    change Ideal.Quotient.mk J.toIdeal (p * a) = p • Ideal.Quotient.mk J.toIdeal a
    rw [map_mul]
    rfl

omit [LinearOrder I] in
/-- BOTH genuine quotient gradings retain the SAME actual original nonnegative degree piece. -/
theorem polynomialQuotientNatIntegralPiece_iff
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule I K))
    (q : MvPolynomial I K ⧸ J.toIdeal) (d : ℕ) :
    q ∈ GradedQuotient.grading (MvPolynomial.homogeneousSubmodule I K) J.toIdeal d ↔
      q ∈ polynomialQuotientIntegralPiece J (d : ℤ) := by
  constructor
  · rintro ⟨a, ha, he⟩
    exact ⟨a, (polynomialNatIntegralHomogeneous_iff a d).mp ha, he⟩
  · rintro ⟨a, ha, he⟩
    exact ⟨a, (polynomialNatIntegralHomogeneous_iff a d).mpr ha, he⟩

/-- Actual quotient coordinate cohomology is finite in EVERY integral degree over the original Noetherian base. -/
theorem polynomialQuotientCoordinateCech_homology_finite [IsNoetherianRing K]
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule I K)) (k : ℤ) (p : ℕ) :
    Module.Finite K
      ((homogeneousCoordinateCechComplex (polynomialIntegralGrading (K := K) (I := I))
        (polynomialQuotientIntegralPiece J) (fun i => (MvPolynomial.X i : MvPolynomial I K))
        polynomialCoordinate_X_degree k).homology p) := by
  let : Module.Finite (MvPolynomial I K) (MvPolynomial I K) := Module.Finite.self (MvPolynomial I K)
  let : Module.Finite (MvPolynomial I K) (MvPolynomial I K ⧸ J.toIdeal) :=
    Module.Finite.of_surjective
      (Ideal.Quotient.mkₐ (MvPolynomial I K) J.toIdeal).toLinearMap
      (Ideal.Quotient.mk_surjective)
  exact finiteGradedPolynomialCoordinateCech_homology_finite (polynomialQuotientIntegralPiece J) k p

end
end DeJongAlterations.Geometry.ProperSteinProjectiveCech
