import Hironaka.Geometry.ProjectiveIdealRepresentation

/-!
# Whole original affine ideal membership lifts to a whole original homogeneous relation with exact dehomogenization
-/

noncomputable section

open MvPolynomial AlgebraicGeometry HomogeneousLocalization

namespace Hironaka.Algebra.ProjectiveSecant

open Geometry.ProjectiveIdeal

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)
  (J : HomogeneousIdeal (ProjectiveGrading k (n + 1))) (j : Fin (n + 2))

/-- Native original localization produces a positive homogeneous member of the WHOLE original ideal, with exactly the same original affine polynomial. -/
theorem exists_homogeneous_mem_exact_dehom {F : CoordinateRing k j}
    (hF : F ∈ J.toIdeal.map (coordinateDehom j).toRingHom) (hFn : F ≠ 0) :
    ∃ (d : ℕ) (H : MvPolynomial (Fin (n + 2)) k),
      0 < d ∧ H.IsHomogeneous d ∧ H ≠ 0 ∧ H ∈ J ∧ coordinateDehom j H = F := by
  obtain ⟨d, H, hH, hHF⟩ := exists_homogeneous_coordinateDehom j F
  have hHn : H ≠ 0 := by
    intro hz
    apply hFn
    rw [← hHF, hz, map_zero]
  rw [← homogeneousQuotient_coordinateKernel J j] at hF
  change Away.map (GradedQuotient.gradedMk (ProjectiveGrading k (n + 1)) J.toIdeal) (X j)
    (homogeneousChartRatioHom j F) = 0 at hF
  rw [← hHF, homogeneousChartRatioHom_dehom_of_isHomogeneous j hH] at hF
  obtain ⟨m, hm⟩ := (GradedQuotient.awayMap_mk_eq_zero_iff (ProjectiveGrading k (n + 1)) J
    (MvPolynomial.isHomogeneous_X k j) d H (by simpa using hH)).mp hF
  let K := X j ^ (m + 1) * H
  have hK : K.IsHomogeneous (m + 1 + d) := by
    simpa [K] using ((MvPolynomial.isHomogeneous_X k j).pow (m + 1)).mul hH
  have hKJ : K ∈ J := by
    have he : K = X j * (X j ^ m * H) := by
      simp only [K, pow_succ]
      ac_rfl
    rw [he]
    exact J.toIdeal.mul_mem_left _ hm
  have hX : coordinateDehom (R := k) j (X j) = 1 := by simp [coordinateDehom]
  refine ⟨m + 1 + d, K, Nat.add_pos_left (Nat.succ_pos _) _, hK,
    mul_ne_zero (pow_ne_zero _ (MvPolynomial.X_ne_zero j)) hHn, hKJ, ?_⟩
  change coordinateDehom j (X j ^ (m + 1) * H) = F
  rw [map_mul, map_pow, hX, one_pow, one_mul, hHF]

end Hironaka.Algebra.ProjectiveSecant
