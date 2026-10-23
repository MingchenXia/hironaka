import DeJongAlterations.Algebra.ProjectiveLinearCoordinates
import DeJongAlterations.Geometry.ProjectiveIdealCharts
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# The actual graded polynomial coordinate automorphism

Original linear coordinate forms and their explicit inverse construct the
entire polynomial equivalence. The coefficient field and all original
homogeneous degrees are preserved.
-/

noncomputable section

open MvPolynomial

namespace DeJongAlterations.Algebra.ProjectiveLinearCoordinates

open Geometry.ProjectiveIdeal

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k] (n : ℕ)

/-- Original normalized homogeneous linear coordinate forms. -/
def normalizeForm (w : Fin (n + 2) → k) : Fin (n + 2) → MvPolynomial (Fin (n + 2)) k :=
  Fin.cases (C ((w 0)⁻¹) * X 0) (fun i => X i.succ - C (w i.succ * (w 0)⁻¹) * X 0)

/-- The actual inverse normalized homogeneous coordinate forms. -/
def inverseNormalizeForm (w : Fin (n + 2) → k) : Fin (n + 2) → MvPolynomial (Fin (n + 2)) k :=
  Fin.cases (C (w 0) * X 0) (fun i => X i.succ + C (w i.succ) * X 0)

/-- Actual substitution of the normalized original coordinate forms. -/
def normalizePolynomialMap (w : Fin (n + 2) → k) :
    MvPolynomial (Fin (n + 2)) k →ₐ[k] MvPolynomial (Fin (n + 2)) k :=
  MvPolynomial.aeval (normalizeForm k n w)

/-- Actual substitution of the inverse original coordinate forms. -/
def inverseNormalizePolynomialMap (w : Fin (n + 2) → k) :
    MvPolynomial (Fin (n + 2)) k →ₐ[k] MvPolynomial (Fin (n + 2)) k :=
  MvPolynomial.aeval (inverseNormalizeForm k n w)

/-- Both actual polynomial substitutions cancel on the whole ring, in one order. -/
theorem inverseNormalize_comp_normalize (w : Fin (n + 2) → k) (hw : w 0 ≠ 0) :
    (inverseNormalizePolynomialMap k n w).comp (normalizePolynomialMap k n w) = AlgHom.id k _ := by
  have h0 (P : MvPolynomial (Fin (n + 2)) k) : C ((w 0)⁻¹) * (C (w 0) * P) = P := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hw, map_one, one_mul]
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [normalizePolynomialMap, inverseNormalizePolynomialMap, normalizeForm,
      inverseNormalizeForm, mul_assoc, h0]
  · simp [normalizePolynomialMap, inverseNormalizePolynomialMap, normalizeForm,
      inverseNormalizeForm, mul_assoc, h0]

/-- Both actual polynomial substitutions cancel on the whole ring, in the opposite order. -/
theorem normalize_comp_inverseNormalize (w : Fin (n + 2) → k) (hw : w 0 ≠ 0) :
    (normalizePolynomialMap k n w).comp (inverseNormalizePolynomialMap k n w) = AlgHom.id k _ := by
  have h0 (P : MvPolynomial (Fin (n + 2)) k) : C (w 0) * (C ((w 0)⁻¹) * P) = P := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hw, map_one, one_mul]
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [normalizePolynomialMap, inverseNormalizePolynomialMap, normalizeForm,
      inverseNormalizeForm, mul_assoc, h0]
  · simp [normalizePolynomialMap, inverseNormalizePolynomialMap, normalizeForm,
      inverseNormalizeForm, mul_assoc]

/-- The actual normalized polynomial automorphism, internally proved invertible. -/
def normalizePolynomialEquiv (w : Fin (n + 2) → k) (hw : w 0 ≠ 0) :
    MvPolynomial (Fin (n + 2)) k ≃ₐ[k] MvPolynomial (Fin (n + 2)) k where
  __ := normalizePolynomialMap k n w
  invFun := inverseNormalizePolynomialMap k n w
  left_inv F := AlgHom.congr_fun (inverseNormalize_comp_normalize k n w hw) F
  right_inv F := AlgHom.congr_fun (normalize_comp_inverseNormalize k n w hw) F

/-- The original coordinate permutation as an entire polynomial automorphism. -/
def swapPolynomialEquiv (j : Fin (n + 2)) :
    MvPolynomial (Fin (n + 2)) k ≃ₐ[k] MvPolynomial (Fin (n + 2)) k where
  __ := MvPolynomial.rename (Equiv.swap 0 j)
  invFun := MvPolynomial.rename (Equiv.swap 0 j)
  left_inv F := by
    change MvPolynomial.rename (Equiv.swap 0 j) (MvPolynomial.rename (Equiv.swap 0 j) F) = F
    rw [MvPolynomial.rename_rename]
    simp only [Function.comp_def, Equiv.swap_apply_self]
    change MvPolynomial.rename id F = F
    exact MvPolynomial.rename_id_apply F
  right_inv F := by
    change MvPolynomial.rename (Equiv.swap 0 j) (MvPolynomial.rename (Equiv.swap 0 j) F) = F
    rw [MvPolynomial.rename_rename]
    simp only [Function.comp_def, Equiv.swap_apply_self]
    change MvPolynomial.rename id F = F
    exact MvPolynomial.rename_id_apply F

/-- The literal pullback of the internally constructed linear coordinate change. -/
def coordinatePolynomialEquiv (v : Fin (n + 2) → k) (hv : v ≠ 0) :
    MvPolynomial (Fin (n + 2)) k ≃ₐ[k] MvPolynomial (Fin (n + 2)) k :=
  (normalizePolynomialEquiv k n (swapLinearEquiv k n (pivot k n v hv) v)
    (by simpa [swapLinearEquiv] using pivot_ne_zero k n v hv)).trans
      (swapPolynomialEquiv k n (pivot k n v hv))

/-- The first original linear coordinate form is the actual normalized pivot coordinate. -/
@[simp]
theorem coordinatePolynomialEquiv_X_zero (v : Fin (n + 2) → k) (hv : v ≠ 0) :
    coordinatePolynomialEquiv k n v hv (X 0) = C ((v (pivot k n v hv))⁻¹) * X (pivot k n v hv) := by
  simp [coordinatePolynomialEquiv, normalizePolynomialEquiv, swapPolynomialEquiv,
    normalizePolynomialMap, normalizeForm, swapLinearEquiv]

/-- Every remaining original linear coordinate form is the exact pivot-normalized original form. -/
@[simp]
theorem coordinatePolynomialEquiv_X_succ (v : Fin (n + 2) → k) (hv : v ≠ 0) (j : Fin (n + 1)) :
    coordinatePolynomialEquiv k n v hv (X j.succ) =
      X (Equiv.swap 0 (pivot k n v hv) j.succ) -
        C (v (Equiv.swap 0 (pivot k n v hv) j.succ) * (v (pivot k n v hv))⁻¹) * X (pivot k n v hv) := by
  simp [coordinatePolynomialEquiv, normalizePolynomialEquiv, swapPolynomialEquiv,
    normalizePolynomialMap, normalizeForm, swapLinearEquiv]

end DeJongAlterations.Algebra.ProjectiveLinearCoordinates
