import Mathlib.LinearAlgebra.StdBasis

/-!
# Internally chosen linear coordinates at an original nonzero vector

The original vector is extended to an actual basis, using one nonzero
coordinate and explicit mutually inverse elementary coordinate maps.
-/

noncomputable section

open Module

namespace DeJongAlterations.Algebra.ProjectiveLinearCoordinates

universe u

variable (k : Type u) [Field k] (n : ℕ)

/-- An original nonzero coordinate is internally selected. -/
def pivot (v : Fin (n + 2) → k) (hv : v ≠ 0) : Fin (n + 2) :=
  Classical.choose (show ∃ j, v j ≠ 0 from by
    by_contra h
    push Not at h
    exact hv (funext h))

/-- The selected original coordinate really is nonzero. -/
theorem pivot_ne_zero (v : Fin (n + 2) → k) (hv : v ≠ 0) : v (pivot k n v hv) ≠ 0 :=
  Classical.choose_spec (show ∃ j, v j ≠ 0 from by
    by_contra h
    push Not at h
    exact hv (funext h))

/-- The literal coordinate permutation interchanging zero and the selected coordinate. -/
def swapLinearEquiv (j : Fin (n + 2)) :
    (Fin (n + 2) → k) ≃ₗ[k] (Fin (n + 2) → k) where
  toFun x i := x (Equiv.swap 0 j i)
  invFun x i := x (Equiv.swap 0 j i)
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp
  map_add' x y := rfl
  map_smul' a x := rfl

/-- The elementary coordinate change at a vector with nonzero first coordinate. -/
def normalizeLinearEquiv (w : Fin (n + 2) → k) (hw : w 0 ≠ 0) :
    (Fin (n + 2) → k) ≃ₗ[k] (Fin (n + 2) → k) where
  toFun x := Fin.cases (x 0 / w 0) (fun i => x i.succ - w i.succ * (x 0 / w 0))
  invFun y := Fin.cases (w 0 * y 0) (fun i => y i.succ + w i.succ * y 0)
  left_inv x := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cases_zero]; rw [mul_comm, div_mul_cancel₀ _ hw]
    · simp
  right_inv y := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hw]
    · simp [hw]
  map_add' x y := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [add_div]
    · simp [add_div, mul_add]; ring
  map_smul' a x := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [mul_div_assoc]
    · simp [mul_div_assoc, mul_sub]; ring

/-- The actual linear automorphism sends the original vector to the first standard vector. -/
def coordinateLinearEquiv (v : Fin (n + 2) → k) (hv : v ≠ 0) :
    (Fin (n + 2) → k) ≃ₗ[k] (Fin (n + 2) → k) :=
  (swapLinearEquiv k n (pivot k n v hv)).trans
    (normalizeLinearEquiv k n (swapLinearEquiv k n (pivot k n v hv) v)
      (by simpa [swapLinearEquiv] using pivot_ne_zero k n v hv))

/-- The original vector, not a supplied proportional vector, maps exactly to e0. -/
theorem coordinateLinearEquiv_apply_self (v : Fin (n + 2) → k) (hv : v ≠ 0) :
    coordinateLinearEquiv k n v hv v = Pi.single 0 1 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [coordinateLinearEquiv, normalizeLinearEquiv, swapLinearEquiv, pivot_ne_zero]
  · simp [coordinateLinearEquiv, normalizeLinearEquiv, swapLinearEquiv, pivot_ne_zero]

/-- An actual basis internally extending the original nonzero vector. -/
def coordinateBasis (v : Fin (n + 2) → k) (hv : v ≠ 0) :
    Basis (Fin (n + 2)) k (Fin (n + 2) → k) :=
  (Pi.basisFun k (Fin (n + 2))).map (coordinateLinearEquiv k n v hv).symm

/-- The first vector of the internally constructed basis is the original vector. -/
theorem coordinateBasis_zero (v : Fin (n + 2) → k) (hv : v ≠ 0) :
    coordinateBasis k n v hv 0 = v := by
  apply (coordinateLinearEquiv k n v hv).injective
  simp [coordinateBasis, coordinateLinearEquiv_apply_self, Pi.basisFun_apply]

end DeJongAlterations.Algebra.ProjectiveLinearCoordinates
