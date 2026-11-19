import Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalVector

/-! The constant summand is the actual tangent-germ image. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Hironaka Hironaka
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalJet
  Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalJetApply
namespace Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalConstant
noncomputable section

/-- The constant vector goes to the actual tangent pullback modulo the full normal square. -/
theorem firstOrderNormalLinearEquiv_constant (d a : ℕ) (b : HolGerm (ComplexModel d)) :
    letI := tangentAlgebra d a
    firstOrderNormalLinearEquiv d a (b,0) =
      Ideal.Quotient.mk (normalIdeal d a ^ 2) (tangentPullback d a b) := by
  let _ := tangentAlgebra d a
  have h := firstOrderNormalLinearEquiv_option_single d a none b
  have he : ((firstOrderExponentEquiv a) none).val = 0 := rfl
  have hm : normalExponentMonomial d a 0 = 1 := by simp [normalExponentMonomial]
  rw [he,hm] at h
  rw [Algebra.smul_def, map_one, mul_one, ← Ideal.Quotient.mk_algebraMap] at h
  exact h
end
end Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalConstant
