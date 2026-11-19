import Hironaka.Geometry.ProjectiveRationalPointCoordinatesEvaluation
import Mathlib.Data.Fintype.Card

/-!
# The actual original homogeneous tangent hyperplane from original affine derivatives
-/

noncomputable section

open MvPolynomial

namespace Hironaka.Algebra.ProjectiveSecant

universe u

variable (k : Type u) [Field k] {I : Type} [Fintype I] [DecidableEq I] (j : I)

/-- The literal original tangent linear form in the whole original homogeneous coordinate ring. -/
def tangentLinearForm (q : I → k) (a : {i : I // i ≠ j} → k) : MvPolynomial I k := by
  classical
  exact (∑ l : {i : I // i ≠ j}, C (a l) * X l.val) -
    C (∑ l : {i : I // i ≠ j}, a l * q l.val) * X j

/-- Actual original derivative coefficients give a genuine homogeneous degree-one form. -/
theorem tangentLinearForm_isHomogeneous (q : I → k) (a : {i : I // i ≠ j} → k) :
    (tangentLinearForm k j q a).IsHomogeneous 1 := by
  classical
  have hs : (∑ l : {i : I // i ≠ j}, C (a l) * X l.val : MvPolynomial I k).IsHomogeneous 1 := by
    apply MvPolynomial.IsHomogeneous.sum
    intro l _
    simpa using (MvPolynomial.isHomogeneous_C I (a l)).mul (MvPolynomial.isHomogeneous_X k l.val)
  have hc : (C (∑ l : {i : I // i ≠ j}, a l * q l.val) * X j : MvPolynomial I k).IsHomogeneous 1 := by
    simpa using (MvPolynomial.isHomogeneous_C I (∑ l : {i : I // i ≠ j}, a l * q l.val)).mul (MvPolynomial.isHomogeneous_X k j)
  exact hs.sub hc

/-- The original normalized fixed vector lies on its actual original homogeneous tangent equation. -/
theorem tangentLinearForm_eval_fixed (q : I → k) (hq : q j = 1) (a : {i : I // i ≠ j} → k) :
    MvPolynomial.eval q (tangentLinearForm k j q a) = 0 := by
  classical
  simp only [tangentLinearForm, map_sub, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
    hq, mul_one, sub_self]

/-- Evaluating the whole original linear form at an actual remaining-coordinate basis vector gives exactly its original derivative coefficient. -/
theorem tangentLinearForm_eval_basis (q : I → k) (a : {i : I // i ≠ j} → k) (l : {i : I // i ≠ j}) :
    MvPolynomial.eval (fun i : I => if i = l.val then 1 else 0) (tangentLinearForm k j q a) = a l := by
  classical
  have hj : j ≠ l.val := Ne.symm l.property
  simp only [tangentLinearForm, map_sub, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
    if_neg hj, mul_zero, sub_zero]
  rw [Finset.sum_eq_single l]
  · simp
  · intro r _ hrl
    have hrl' : r.val ≠ l.val := fun h => hrl (Subtype.ext h)
    simp [hrl']
  · simp

/-- An actual nonzero original partial derivative proves nonvanishing of the entire original homogeneous linear form. -/
theorem tangentLinearForm_ne_zero (q : I → k) (a : {i : I // i ≠ j} → k)
    (ha : ∃ l, a l ≠ 0) : tangentLinearForm k j q a ≠ 0 := by
  classical
  obtain ⟨l, hl⟩ := ha
  intro h
  have he := congrArg (MvPolynomial.eval (fun i : I => if i = l.val then 1 else 0)) h
  rw [tangentLinearForm_eval_basis, map_zero] at he
  exact hl he

end Hironaka.Algebra.ProjectiveSecant
