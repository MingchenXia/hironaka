import Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalConstant

/-! Multiplication in the actual first normal neighborhood. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
open Hironaka Hironaka
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalJet
  Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalVector
  Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalConstant
  Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalNilpotence
namespace Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalMultiplication
noncomputable section

/-- Products of two arbitrary actual linear normal parts vanish. -/
theorem linear_parts_mul_zero (d a : ℕ) (v w : Fin a → HolGerm (ComplexModel d)) :
    letI := tangentAlgebra d a
    firstOrderNormalLinearEquiv d a (0,v) * firstOrderNormalLinearEquiv d a (0,w) = 0 := by
  classical
  let _ := tangentAlgebra d a
  rw [firstOrderNormalLinearEquiv_vector,firstOrderNormalLinearEquiv_vector]
  rw [Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro j hj
  calc
    (v i • Ideal.Quotient.mk (normalIdeal d a ^ 2) (normalCoordinate d a i)) *
        (w j • Ideal.Quotient.mk (normalIdeal d a ^ 2) (normalCoordinate d a j)) =
      (v i * w j) • ((Ideal.Quotient.mk (normalIdeal d a ^ 2) (normalCoordinate d a i)) *
        (Ideal.Quotient.mk (normalIdeal d a ^ 2) (normalCoordinate d a j))) := by
          simp only [Algebra.smul_def,map_mul]
          ring
    _ = 0 := by rw [normal_coordinate_classes_mul_zero, smul_zero]

end
end Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalMultiplication
