import Hironaka.Algebra.ProjectiveLinearCoordinatesPolynomial
import Hironaka.Algebra.ProjectiveSecantTangentDifferential

/-!
# Literal inverse projection coordinates give the exact original directional derivative
-/

noncomputable section

open MvPolynomial

namespace Hironaka.Algebra.ProjectiveSecant

open ProjectiveLinearCoordinates

universe u

variable (k : Type u) [Field k] (n : ℕ)

/-- Evaluation of the actual whole polynomial pullback is evaluation at the actual original linear-coordinate image. -/
theorem original_eval_coordinatePolynomialEquiv (v : Fin (n + 2) → k) (hv : v ≠ 0)
    (x : Fin (n + 2) → k) (H : MvPolynomial (Fin (n + 2)) k) :
    MvPolynomial.eval x (coordinatePolynomialEquiv k n v hv H) =
      MvPolynomial.eval (coordinateLinearEquiv k n v hv x) H := by
  have he : (MvPolynomial.eval x).comp (coordinatePolynomialEquiv k n v hv).toRingHom =
      MvPolynomial.eval (coordinateLinearEquiv k n v hv x) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      have hc : coordinatePolynomialEquiv k n v hv (C c) = C c :=
        (coordinatePolynomialEquiv k n v hv).commutes c
      simp only [RingHom.comp_apply, MvPolynomial.eval_C]
      change MvPolynomial.eval x (coordinatePolynomialEquiv k n v hv (C c)) = c
      rw [hc, MvPolynomial.eval_C]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [coordinateLinearEquiv, swapLinearEquiv, normalizeLinearEquiv, div_eq_mul_inv, mul_comm]
      · simp [coordinateLinearEquiv, swapLinearEquiv, normalizeLinearEquiv, div_eq_mul_inv]
        ring
  exact RingHom.congr_fun he H

/-- The actual whole inverse polynomial pullback retains exactly the original inverse linear-coordinate evaluation. -/
theorem original_eval_inverseCoordinatePolynomialEquiv (v : Fin (n + 2) → k) (hv : v ≠ 0)
    (x : Fin (n + 2) → k) (H : MvPolynomial (Fin (n + 2)) k) :
    MvPolynomial.eval x ((coordinatePolynomialEquiv k n v hv).symm H) =
      MvPolynomial.eval ((coordinateLinearEquiv k n v hv).symm x) H := by
  have he := original_eval_coordinatePolynomialEquiv k n v hv
    ((coordinateLinearEquiv k n v hv).symm x) ((coordinatePolynomialEquiv k n v hv).symm H)
  simpa only [AlgEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] using he.symm

/-- The first partial derivative of each actual inverse normalized form is its literal original vector coefficient. -/
theorem original_pderiv_inverseNormalizeForm (w : Fin (n + 2) → k) (i : Fin (n + 2)) :
    MvPolynomial.pderiv 0 (inverseNormalizeForm k n w i) = C (w i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [inverseNormalizeForm]
  · simp [inverseNormalizeForm, pderiv_X_of_ne (Fin.succ_ne_zero j)]

/-- The first column of the actual internally constructed inverse coordinates is exactly the original centre vector. -/
theorem original_pderiv_inverseCoordinatePolynomialEquiv_X
    (v : Fin (n + 2) → k) (hv : v ≠ 0) (i : Fin (n + 2)) :
    MvPolynomial.pderiv 0 ((coordinatePolynomialEquiv k n v hv).symm (X i)) = C (v i) := by
  change MvPolynomial.pderiv 0
    (inverseNormalizePolynomialMap k n (swapLinearEquiv k n (pivot k n v hv) v)
      (MvPolynomial.rename (Equiv.swap 0 (pivot k n v hv)) (X i))) = _
  rw [MvPolynomial.rename_X]
  simp only [inverseNormalizePolynomialMap, MvPolynomial.aeval_X,
    original_pderiv_inverseNormalizeForm, swapLinearEquiv, LinearEquiv.coe_mk,
    LinearMap.coe_mk, AddHom.coe_mk, Equiv.swap_apply_self]

/-- The actual discarded-coordinate derivative of the whole original inverse substitution is exactly the original centre-direction derivative. -/
theorem original_pderiv_inverseCoordinatePolynomialEquiv
    (v : Fin (n + 2) → k) (hv : v ≠ 0) (H : MvPolynomial (Fin (n + 2)) k) :
    MvPolynomial.pderiv 0 ((coordinatePolynomialEquiv k n v hv).symm H) =
      ∑ i : Fin (n + 2), (coordinatePolynomialEquiv k n v hv).symm (MvPolynomial.pderiv i H) * C (v i) := by
  have he : MvPolynomial.aeval (fun i => (coordinatePolynomialEquiv k n v hv).symm (X i)) =
      (coordinatePolynomialEquiv k n v hv).symm.toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  have heval (F : MvPolynomial (Fin (n + 2)) k) :
      (coordinatePolynomialEquiv k n v hv).symm F =
        MvPolynomial.aeval (fun i => (coordinatePolynomialEquiv k n v hv).symm (X i)) F :=
    (AlgHom.congr_fun he F).symm
  rw [heval H]
  rw [original_derivation_aeval]
  simp only [he, original_pderiv_inverseCoordinatePolynomialEquiv_X]
  rfl

/-- The actual transformed vector evaluates the actual discarded-coordinate derivative to the exact original centre-direction derivative at the original vector. -/
theorem original_eval_pderiv_inverseCoordinatePolynomialEquiv
    (v : Fin (n + 2) → k) (hv : v ≠ 0)
    (q : Fin (n + 2) → k) (H : MvPolynomial (Fin (n + 2)) k) :
    MvPolynomial.eval (coordinateLinearEquiv k n v hv q)
        (MvPolynomial.pderiv 0 ((coordinatePolynomialEquiv k n v hv).symm H)) =
      ∑ i : Fin (n + 2), MvPolynomial.eval q (MvPolynomial.pderiv i H) * v i := by
  rw [original_pderiv_inverseCoordinatePolynomialEquiv]
  simp only [map_sum, map_mul, original_eval_inverseCoordinatePolynomialEquiv,
    LinearEquiv.symm_apply_apply, MvPolynomial.eval_C]

end Hironaka.Algebra.ProjectiveSecant
