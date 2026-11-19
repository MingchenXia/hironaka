import Hironaka.Algebra.ProjectiveSecantTangentLinearForm
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# The whole original homogeneous gradient equals the original affine differential form
-/

noncomputable section

open MvPolynomial

namespace Hironaka.Algebra.ProjectiveSecant

/-- Split an actual original finite sum into the actual remaining-coordinate sum and its original distinguished term. -/
theorem original_sum_split_coordinate {I M : Type*} [Fintype I] [DecidableEq I]
    [AddCommMonoid M] (j : I) (f : I → M) :
    ∑ i, f i = (∑ l : {i : I // i ≠ j}, f l.val) + f j := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
  rw [Finset.sum_subtype (p := fun i : I => i ≠ j) (Finset.univ.erase j) (by simp) f]

/-- Euler's exact homogeneous identity identifies the whole original gradient linear form with the actual affine differential at the same normalized original point, without dividing by the degree. -/
theorem original_homogeneous_gradient_eq_tangentLinearForm
    {k : Type*} [Field k] {n : ℕ} (j : Fin (n + 1))
    {d : ℕ} {H : MvPolynomial (Fin (n + 1)) k} (hH : H.IsHomogeneous d)
    (q : Fin (n + 1) → k) (hq : q j = 1) (hHq : MvPolynomial.eval q H = 0) :
    (∑ l : Fin (n + 1), C (MvPolynomial.eval q (pderiv l H)) * X l) =
      tangentLinearForm k j q (fun l => MvPolynomial.eval q (pderiv l.val H)) := by
  classical
  have he := congrArg (MvPolynomial.eval q) hH.sum_X_mul_pderiv
  simp only [map_sum, map_mul, MvPolynomial.eval_X, map_nsmul, hHq, nsmul_zero] at he
  rw [original_sum_split_coordinate j] at he
  simp only [hq, one_mul] at he
  have hj : MvPolynomial.eval q (pderiv j H) =
      -(∑ l : {i : Fin (n + 1) // i ≠ j}, MvPolynomial.eval q (pderiv l.val H) * q l.val) := by
    have hs : (∑ l : {i : Fin (n + 1) // i ≠ j}, q l.val * MvPolynomial.eval q (pderiv l.val H)) =
        ∑ l : {i : Fin (n + 1) // i ≠ j}, MvPolynomial.eval q (pderiv l.val H) * q l.val := by
      apply Finset.sum_congr rfl
      intro l _
      exact mul_comm _ _
    rw [hs] at he
    linear_combination he
  rw [original_sum_split_coordinate j, hj]
  simp only [tangentLinearForm, map_neg, neg_mul, sub_eq_add_neg]

end Hironaka.Algebra.ProjectiveSecant
