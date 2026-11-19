import Hironaka.Algebra.ProjectiveSecantChart

/-!
# True homogeneous secant equations in the entire original quotient ideal
-/

noncomputable section

open MvPolynomial AlgebraicGeometry HomogeneousLocalization

namespace Hironaka.Algebra.ProjectiveSecant

open Geometry.ProjectiveIdeal ProjectiveProjectionFinite

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] chartAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)
  (J : HomogeneousIdeal (ProjectiveGrading k (n + 1))) (j : Fin (n + 1))

/-- Native homogeneous localization clears an actual original remaining-coordinate power into the whole ideal. -/
theorem exists_power_mul_mem_of_chart_zero {d : ℕ} {F : MvPolynomial (Fin (n + 1)) k}
    (hF : F.IsHomogeneous d) (hz : remainingPolynomialMap k n J j (coordinateDehom j F) = 0) :
    ∃ m : ℕ, MvPolynomial.rename Fin.succ (X j ^ m * F) ∈ J := by
  rw [remainingPolynomialMap_dehom k n J j hF, Away.map_mk] at hz
  have hval := congrArg HomogeneousLocalization.val hz
  simp only [Away.val_mk, HomogeneousLocalization.val_zero] at hval
  change Localization.mk (Ideal.Quotient.mk J.toIdeal (MvPolynomial.rename Fin.succ F))
    (⟨Ideal.Quotient.mk J.toIdeal (X j.succ) ^ d, d, rfl⟩ :
      Submonoid.powers (Ideal.Quotient.mk J.toIdeal (X j.succ))) = 0 at hval
  rw [Localization.mk_eq_mk'] at hval
  obtain ⟨s, hs⟩ := (IsLocalization.mk'_eq_zero_iff _ _).mp hval
  rcases s with ⟨s, m, hm⟩
  change s * Ideal.Quotient.mk J.toIdeal (MvPolynomial.rename Fin.succ F) = 0 at hs
  rw [← hm] at hs
  refine ⟨m, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
  simpa only [map_mul, map_pow, MvPolynomial.rename_X,
    map_mul, map_pow] using hs

/-- An internally obtained actual affine relation yields a nonzero positive homogeneous secant equation. -/
theorem exists_homogeneous_remaining_equation
    (hrel : ∃ P : CoordinateRing k j, P ≠ 0 ∧ remainingPolynomialMap k n J j P = 0) :
    ∃ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) k),
      0 < d ∧ F.IsHomogeneous d ∧ F ≠ 0 ∧ MvPolynomial.rename Fin.succ F ∈ J := by
  obtain ⟨P, hP, hPz⟩ := hrel
  obtain ⟨d, F, hF, hdehom⟩ := exists_homogeneous_coordinateDehom j P
  have hFn : F ≠ 0 := by
    intro hz
    apply hP
    rw [← hdehom, hz, map_zero]
  obtain ⟨m, hm⟩ := exists_power_mul_mem_of_chart_zero k n J j hF (by rwa [hdehom])
  let H := X j ^ (m + 1) * F
  have hH : H.IsHomogeneous (m + 1 + d) := by
    have hpow := (MvPolynomial.isHomogeneous_X k j).pow (m + 1)
    simpa [H] using hpow.mul hF
  refine ⟨m + 1 + d, H, Nat.add_pos_left (Nat.succ_pos _) _, hH,
    mul_ne_zero (pow_ne_zero _ (MvPolynomial.X_ne_zero j)) hFn, ?_⟩
  have heq : MvPolynomial.rename Fin.succ H =
      X j.succ * MvPolynomial.rename Fin.succ (X j ^ m * F) := by
    simp only [H, map_mul, map_pow, MvPolynomial.rename_X, pow_succ]
    ac_rfl
  rw [heq]
  exact J.toIdeal.mul_mem_left _ hm

end Hironaka.Algebra.ProjectiveSecant
