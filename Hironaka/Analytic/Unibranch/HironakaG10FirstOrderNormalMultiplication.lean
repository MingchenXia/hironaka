import Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalConstant
import Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalLinearProduct

/-! Multiplication in the actual first normal neighborhood. -/
set_option autoImplicit false
set_option maxHeartbeats 750000
open Hironaka Hironaka
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalJet
  Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalVector
  Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalConstant
  Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalNilpotence
namespace Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalMultiplication
noncomputable section

/-- The actual first normal neighborhood has square-zero multiplication in its explicit coordinates. -/
theorem firstOrderNormalLinearEquiv_mul (d a : ℕ)
    (b c : HolGerm (ComplexModel d)) (v w : Fin a → HolGerm (ComplexModel d)) :
    letI := tangentAlgebra d a
    firstOrderNormalLinearEquiv d a (b,v) * firstOrderNormalLinearEquiv d a (c,w) =
      firstOrderNormalLinearEquiv d a (b*c, b • w + c • v) := by
  classical
  letI := tangentAlgebra d a
  let E := firstOrderNormalLinearEquiv d a
  have hsplit (b : HolGerm (ComplexModel d)) (v : Fin a → HolGerm (ComplexModel d)) :
      E (b,v) = E (b,0) + E (0,v) := by
    have hp : (b,0) + (0,v) = (b,v) := by ext <;> simp
    rw [← hp, E.map_add]
  have hcc : E (b,0) * E (c,0) = E (b*c,0) := by
    dsimp [E]
    rw [firstOrderNormalLinearEquiv_constant,firstOrderNormalLinearEquiv_constant,
      firstOrderNormalLinearEquiv_constant]
    exact (map_mul ((Ideal.Quotient.mk (normalIdeal d a ^ 2)).comp
      (tangentPullback d a).toRingHom) b c).symm
  have hcw : E (b,0) * E (0,w) = E (0,b • w) := by
    dsimp [E]
    rw [firstOrderNormalLinearEquiv_constant]
    change algebraMap (HolGerm (ComplexModel d))
      (HolGerm (ComplexModel (d+a)) ⧸ normalIdeal d a ^ 2) b * _ = _
    rw [← Algebra.smul_def, ← map_smul]
    simp
  have hcv : E (0,v) * E (c,0) = E (0,c • v) := by
    rw [mul_comm]
    dsimp [E]
    rw [firstOrderNormalLinearEquiv_constant]
    change algebraMap (HolGerm (ComplexModel d))
      (HolGerm (ComplexModel (d+a)) ⧸ normalIdeal d a ^ 2) c * _ = _
    rw [← Algebra.smul_def, ← map_smul]
    simp
  have hvw : E (0,v) * E (0,w) = 0 := linear_parts_mul_zero d a v w
  rw [hsplit b v,hsplit c w,add_mul,mul_add,mul_add,hcc,hcw,hcv,hvw,add_zero]
  have hp : ((b*c,0) + (0,b • w)) + (0,c • v) = (b*c,b • w+c • v) := by
    ext <;> simp
  rw [← E.map_add,← E.map_add,hp]
end
end Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalMultiplication
