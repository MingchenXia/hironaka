import Hironaka.Algebra.ProjectiveLinearCoordinatesQuotient

/-!
# Actual whole triangles comparing the internally chosen normalizations of the same original centre line
-/

noncomputable section

namespace Hironaka.Algebra.ProjectiveLinearCoordinates

universe u

variable (k : Type u) [Field k] (n : ℕ)

/-- The entire actual normalization comparison is constructed from the original vectors, without an input automorphism. -/
def normalizationComparisonLinearEquiv
    (v : Fin (n + 2) → k) (hv : v ≠ 0) (w : Fin (n + 2) → k) (hw : w ≠ 0) :
    (Fin (n + 2) → k) ≃ₗ[k] (Fin (n + 2) → k) :=
  (coordinateLinearEquiv k n v hv).symm.trans (coordinateLinearEquiv k n w hw)

/-- The actual internally chosen original normalization inverse sends the literal standard centre vector back to the SAME original vector. -/
theorem coordinateLinearEquiv_symm_apply_centre (v : Fin (n + 2) → k) (hv : v ≠ 0) :
    (coordinateLinearEquiv k n v hv).symm (Pi.single 0 1) = v := by
  apply (coordinateLinearEquiv k n v hv).injective
  rw [LinearEquiv.apply_symm_apply, coordinateLinearEquiv_apply_self]

/-- Proportional original centre vectors make the actual entire normalization comparison preserve the centre line with the exact inverse scalar. -/
theorem normalizationComparisonLinearEquiv_apply_centre
    (v : Fin (n + 2) → k) (hv : v ≠ 0) (w : Fin (n + 2) → k) (hw : w ≠ 0)
    (a : k) (ha : a ≠ 0) (hwa : w = a • v) :
    normalizationComparisonLinearEquiv k n v hv w hw (Pi.single 0 1) = a⁻¹ • Pi.single 0 1 := by
  change coordinateLinearEquiv k n w hw ((coordinateLinearEquiv k n v hv).symm (Pi.single 0 1)) = _
  rw [coordinateLinearEquiv_symm_apply_centre]
  have h : a • coordinateLinearEquiv k n w hw v = Pi.single 0 1 := by
    rw [← map_smul, ← hwa]
    exact coordinateLinearEquiv_apply_self k n w hw
  calc
    coordinateLinearEquiv k n w hw v = a⁻¹ • (a • coordinateLinearEquiv k n w hw v) := by
      rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
    _ = a⁻¹ • Pi.single 0 1 := by rw [h]

/-- The actual invertible remaining-coordinate comparison is internally constructed from the two SAME-centre original vectors. -/
def normalizationRemainingLinearEquiv
    (v : Fin (n + 2) → k) (hv : v ≠ 0) (w : Fin (n + 2) → k) (hw : w ≠ 0)
    (a : k) (ha : a ≠ 0) (hwa : w = a • v) :
    (Fin (n + 1) → k) ≃ₗ[k] (Fin (n + 1) → k) :=
  remainingLinearEquiv k n (normalizationComparisonLinearEquiv k n v hv w hw) a⁻¹
    (inv_ne_zero ha) (normalizationComparisonLinearEquiv_apply_centre k n v hv w hw a ha hwa)

/-- BOTH independently chosen actual normalizations of the SAME original centre retain the literal whole remaining-coordinate triangle on EVERY original vector. -/
theorem normalizationRemainingLinearEquiv_triangle
    (v : Fin (n + 2) → k) (hv : v ≠ 0) (w : Fin (n + 2) → k) (hw : w ≠ 0)
    (a : k) (ha : a ≠ 0) (hwa : w = a • v) (x : Fin (n + 2) → k) :
    tailLinearMap k n (coordinateLinearEquiv k n w hw x) =
      normalizationRemainingLinearEquiv k n v hv w hw a ha hwa
        (tailLinearMap k n (coordinateLinearEquiv k n v hv x)) := by
  simpa only [normalizationRemainingLinearEquiv, normalizationComparisonLinearEquiv,
    LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] using
    remainingLinearEquiv_tail k n (normalizationComparisonLinearEquiv k n v hv w hw) a⁻¹
      (inv_ne_zero ha) (normalizationComparisonLinearEquiv_apply_centre k n v hv w hw a ha hwa)
      (coordinateLinearEquiv k n v hv x)

end Hironaka.Algebra.ProjectiveLinearCoordinates
