import Hironaka.Algebra.ProjectiveLinearCoordinatesGraded
import Hironaka.Geometry.ProjectiveProjectionCenterPoint

/-!
# The original vector evaluates the internally constructed coordinates to the standard centre
-/

noncomputable section

open MvPolynomial AlgebraicGeometry

namespace Hironaka.Geometry.ProjectiveProjectionCenter

open ProjectiveIdeal Algebra.ProjectiveLinearCoordinates
open Algebra.ProjectiveProjectionFinite

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)

/-- Literal vector evaluation of a coordinate permutation is evaluation at that permuted vector. -/
theorem vectorGradedMap_comp_swap (v : Fin (n + 2) → k) (j : Fin (n + 2)) :
    (vectorGradedMap k n v).toRingHom.comp (MvPolynomial.rename (Equiv.swap 0 j)).toRingHom =
      (vectorGradedMap k n (swapLinearEquiv k n j v)).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [vectorGradedMap]
  · intro i
    simp [vectorGradedMap, swapLinearEquiv]

/-- Literal evaluation of the actual normalized forms sends the original vector exactly to e0. -/
theorem vectorGradedMap_comp_normalize (w : Fin (n + 2) → k) (hw : w 0 ≠ 0) :
    (vectorGradedMap k n w).toRingHom.comp (normalizePolynomialMap k n w).toRingHom =
      (centreGradedMap k n).toRingHom := by
  have h0 (P : MvPolynomial Unit k) : C ((w 0)⁻¹) * (C (w 0) * P) = P := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hw, map_one, one_mul]
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [vectorGradedMap, normalizePolynomialMap, centreGradedMap]
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [normalizePolynomialMap, normalizeForm, vectorGradedMap, centreGradedMap,
        mul_assoc, h0]
    · simp [normalizePolynomialMap, normalizeForm, vectorGradedMap, centreGradedMap,
        mul_assoc, h0]

/-- The original vector and the entire original graded coordinate map give the actual standard-centre substitution. -/
theorem vectorGradedMap_comp_coordinates (v : Fin (n + 2) → k) (hv : v ≠ 0) :
    (vectorGradedMap k n v).comp (coordinateGradedMap k n v hv) = centreGradedMap k n := by
  have hcoord : (coordinateGradedMap k n v hv).toRingHom =
      (MvPolynomial.rename (Equiv.swap 0 (pivot k n v hv))).toRingHom.comp
        (normalizePolynomialMap k n (swapLinearEquiv k n (pivot k n v hv) v)).toRingHom := rfl
  have h : (vectorGradedMap k n v).toRingHom.comp (coordinateGradedMap k n v hv).toRingHom =
      (centreGradedMap k n).toRingHom := by
    rw [hcoord, ← RingHom.comp_assoc, vectorGradedMap_comp_swap]
    exact vectorGradedMap_comp_normalize k n _
      (by simpa [swapLinearEquiv] using pivot_ne_zero k n v hv)
  apply DFunLike.ext
  intro F
  exact RingHom.congr_fun h F

end Hironaka.Geometry.ProjectiveProjectionCenter
