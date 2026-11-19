import Hironaka.Algebra.ProjectiveSecantTangentDifferential

/-!
# Actual normalization at an internally nonzero remaining coordinate preserves the discarded derivative
-/

noncomputable section

open MvPolynomial

namespace Hironaka.Algebra.ProjectiveSecant

open Geometry.ProjectiveIdeal Geometry.ProjectiveRationalPointCoordinates

universe u

variable (k : Type u) [Field k] (n : ℕ)

/-- The actual original remaining affine ratios at an actual nonzero remaining homogeneous coordinate. -/
def projectionChartVector (w : Fin (n + 2) → k) (j : Fin (n + 1))
    (l : ChartIndex j.succ) : k := (w j.succ)⁻¹ * w l.val

/-- The entire actual dehomogenization evaluation is exact actual homogeneous vector normalization. -/
theorem original_eval_dehom_projectionChartVector (w : Fin (n + 2) → k)
    (j : Fin (n + 1)) (hw : w j.succ ≠ 0) (K : MvPolynomial (Fin (n + 2)) k) :
    MvPolynomial.eval (projectionChartVector k n w j) (coordinateDehom j.succ K) =
      MvPolynomial.eval (fun l => (w j.succ)⁻¹ * w l) K := by
  have he : (MvPolynomial.eval (projectionChartVector k n w j)).comp
      (coordinateDehom j.succ).toRingHom = MvPolynomial.eval (fun l => (w j.succ)⁻¹ * w l) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [coordinateDehom]
    · intro l
      by_cases hl : l = j.succ
      · subst l
        simp [coordinateDehom, hw]
      · simp [coordinateDehom, coordinateDehomCoord, hl, projectionChartVector]
  exact RingHom.congr_fun he K

/-- Homogeneous scaling at the actual internally nonzero remaining coordinate preserves the genuine nonzero actual discarded-coordinate derivative. -/
theorem original_projectionChartDerivative_ne_zero (w : Fin (n + 2) → k)
    (j : Fin (n + 1)) (hw : w j.succ ≠ 0)
    {d : ℕ} {K : MvPolynomial (Fin (n + 2)) k} (hK : K.IsHomogeneous d)
    (hderiv : MvPolynomial.eval w (MvPolynomial.pderiv 0 K) ≠ 0) :
    MvPolynomial.eval (projectionChartVector k n w j)
      (MvPolynomial.pderiv (⟨0, Ne.symm (Fin.succ_ne_zero j)⟩ : ChartIndex j.succ)
        (coordinateDehom j.succ K)) ≠ 0 := by
  rw [original_pderiv_coordinateDehom, original_eval_dehom_projectionChartVector k n w j hw]
  have he : MvPolynomial.eval (fun l => (w j.succ)⁻¹ * w l) (MvPolynomial.pderiv 0 K) =
      (w j.succ)⁻¹ ^ (d - 1) * MvPolynomial.eval w (MvPolynomial.pderiv 0 K) :=
    homogeneous_eval₂_scaled hK.pderiv (RingHom.id k) w (w j.succ)⁻¹
  rw [he]
  exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hw)) hderiv

end Hironaka.Algebra.ProjectiveSecant
