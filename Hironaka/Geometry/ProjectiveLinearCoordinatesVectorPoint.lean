import Hironaka.Geometry.ProjectiveRationalPointCoordinatesEvaluation
import Hironaka.Algebra.ProjectiveLinearCoordinates

/-!
# Original native projective point equality internally produces actual vector proportionality
-/

noncomputable section

open AlgebraicGeometry MvPolynomial

namespace Hironaka.Geometry.ProjectiveLinearCoordinates

open ProjectiveProjectionCenter ProjectiveRationalPointCoordinates
open Algebra.ProjectiveLinearCoordinates

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k] (n : ℕ)

/-- Equality of SAME actual native original vector points gives every original cross-coordinate relation internally. -/
theorem vectorPoint_eq_cross_relation
    (v : Fin (n + 2) → k) (hv : v ≠ 0) (w : Fin (n + 2) → k) (hw : w ≠ 0)
    (h : vectorPoint k n v hv = vectorPoint k n w hw) (i j : Fin (n + 2)) :
    v j * w i = v i * w j := by
  let F : MvPolynomial (Fin (n + 2)) k := C (v j) * X i - C (v i) * X j
  have hF : F.IsHomogeneous 1 := by
    apply MvPolynomial.IsHomogeneous.sub
    · simpa using (MvPolynomial.isHomogeneous_C _ (v j)).mul (MvPolynomial.isHomogeneous_X k i)
    · simpa using (MvPolynomial.isHomogeneous_C _ (v i)).mul (MvPolynomial.isHomogeneous_X k j)
  have hm : F ∈ (vectorPoint k n v hv).asHomogeneousIdeal := by
    rw [vectorPoint_mem_homogeneous k n v hv hF]
    simp only [F, map_sub, map_mul, eval_C, eval_X]
    ring
  rw [h, vectorPoint_mem_homogeneous k n w hw hF] at hm
  exact sub_eq_zero.mp (by simpa only [F, map_sub, map_mul, eval_C, eval_X] using hm)

/-- The SAME actual native original projective point internally supplies the actual nonzero whole-vector proportionality scalar; no ratio certificate is supplied. -/
theorem exists_nonzero_smul_of_vectorPoint_eq
    (v : Fin (n + 2) → k) (hv : v ≠ 0) (w : Fin (n + 2) → k) (hw : w ≠ 0)
    (h : vectorPoint k n v hv = vectorPoint k n w hw) :
    ∃ a : k, a ≠ 0 ∧ w = a • v := by
  let j := pivot k n v hv
  have hj : v j ≠ 0 := pivot_ne_zero k n v hv
  have hwj : w j ≠ 0 := by
    intro hz
    apply hw
    ext i
    have hi := vectorPoint_eq_cross_relation k n v hv w hw h i j
    rw [hz, mul_zero] at hi
    exact (mul_eq_zero.mp hi).resolve_left hj
  refine ⟨w j / v j, div_ne_zero hwj hj, ?_⟩
  ext i
  change w i = (w j / v j) * v i
  rw [div_mul_eq_mul_div, eq_div_iff hj]
  exact (mul_comm (w i) (v j)).trans
    ((vectorPoint_eq_cross_relation k n v hv w hw h i j).trans (mul_comm (v i) (w j)))

end Hironaka.Geometry.ProjectiveLinearCoordinates
