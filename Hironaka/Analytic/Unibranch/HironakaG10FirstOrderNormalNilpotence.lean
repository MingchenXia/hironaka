import Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalJet

/-! The normal coordinate classes in the actual first neighborhood multiply to zero. -/
set_option autoImplicit false
open Hironaka Hironaka
  HironakaRelativeNormalIdeal
namespace Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalNilpotence

/-- Distinct or equal actual normal coordinate germs have zero product in the
whole analytic quotient by the full square of the normal ideal. -/
theorem normal_coordinate_classes_mul_zero (d a : ℕ) (i j : Fin a) :
    (Ideal.Quotient.mk (normalIdeal d a ^ 2) (normalCoordinate d a i)) *
      (Ideal.Quotient.mk (normalIdeal d a ^ 2) (normalCoordinate d a j)) = 0 := by
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  have hi : normalCoordinate d a i ∈ normalIdeal d a := Ideal.subset_span ⟨i,rfl⟩
  have hj : normalCoordinate d a j ∈ normalIdeal d a := Ideal.subset_span ⟨j,rfl⟩
  simpa only [pow_two] using Ideal.mul_mem_mul hi hj
end Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalNilpotence
