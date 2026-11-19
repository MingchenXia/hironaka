import Hironaka.Algebra.ProjectiveSecantLine
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# Genuine binary linear-form endpoint uniqueness in arbitrary characteristic
-/

noncomputable section

open MvPolynomial AlgebraicGeometry

namespace Hironaka.Algebra.ProjectiveSecant

open Geometry.ProjectiveIdeal ProjectiveProjectionFinite

/-- Euler in degree one gives the whole original linear form from its actual constant partial derivatives. -/
theorem homogeneous_linear_eq_sum {R I : Type*} [CommRing R] [Fintype I] [DecidableEq I]
    {F : MvPolynomial I R} (hF : F.IsHomogeneous 1) :
    F = ∑ i, C ((pderiv i F).coeff 0) * X i := by
  have hc (i : I) : pderiv i F = C ((pderiv i F).coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
      ((MvPolynomial.totalDegree_zero_iff_isHomogeneous I).mpr hF.pderiv)
  have he := hF.sum_X_mul_pderiv
  simp only [one_smul] at he
  calc
    F = ∑ i, X i * pderiv i F := he.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact (congrArg (fun z => X i * z) (hc i)).trans (mul_comm _ _)

/-- Both actual native endpoint vanishings force an entire binary homogeneous linear form to vanish, without any characteristic restriction. -/
theorem binary_homogeneous_linear_eq_zero {k : Type*} [Field k]
    {F : MvPolynomial (Fin 2) k} (hF : F.IsHomogeneous 1)
    (h0 : centreGradedMap k 0 F = 0)
    (h1 : MvPolynomial.eval (fun i : Fin 2 => if i = 0 then 0 else 1) F = 0) : F = 0 := by
  have he := homogeneous_linear_eq_sum hF
  simp only [Fin.sum_univ_two] at he
  have hc0 : (pderiv (0 : Fin 2) F).coeff 0 = 0 := by
    have hS := centreGradedMap_X_zero k 0
    have hT : centreGradedMap k 0 (X (1 : Fin 2)) = 0 := centreGradedMap_X_succ k 0 (0 : Fin 1)
    rw [he, map_add, map_mul, map_mul, hS, hT, mul_zero, add_zero] at h0
    have hh := congrArg (MvPolynomial.eval (fun _ : Unit => (1 : k))) h0
    simpa [centreGradedMap] using hh
  have hc1 : (pderiv (1 : Fin 2) F).coeff 0 = 0 := by
    rw [he] at h1
    simpa using h1
  rw [he, hc0, hc1]
  simp

end Hironaka.Algebra.ProjectiveSecant
