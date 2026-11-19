import Hironaka.Analytic.Unibranch.HironakaG10FlatSquareZeroSplit
import Hironaka.Analytic.Unibranch.HironakaG10SmoothProjectionFlat

/-! Actual matrix-cokernel flatness equals flatness of its analytic square-zero quotient. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Hironaka Hironaka
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  Hironaka.Analytic.Unibranch.HironakaG10ActualSquareZeroMatrixEquiv
  Hironaka.Analytic.Unibranch.HironakaG10FlatSquareZeroSplit
  Hironaka.Analytic.Unibranch.HironakaG10SmoothProjectionFlat
namespace Hironaka.Analytic.Unibranch.HironakaG10ActualSquareZeroFlatEquiv
noncomputable section

/-- The actual explicit analytic quotient and the original matrix cokernel
are flat simultaneously over the actual original smooth parameter germs. -/
theorem actualSquareZeroMatrix_flat_iff (d t a : ℕ) {b : ℕ}
    (F : Matrix (Fin a) (Fin b) (HolGerm (ComplexModel (d+t)))) :
    letI := tangentAlgebra d t
    let B := HolGerm (ComplexModel (d+t))
    let R := HolGerm (ComplexModel d)
    let Q := HolGerm (ComplexModel ((d+t)+a)) ⧸ actualSquareZeroMatrixIdeal (d+t) a F
    let M := (Fin a → B) ⧸ LinearMap.range F.mulVecLin
    letI : Algebra B (HolGerm (ComplexModel ((d+t)+a))) := tangentAlgebra (d+t) a
    letI : Module R Q := Module.compHom Q (tangentPullback d t).toRingHom
    letI : Module R M := Module.compHom M (tangentPullback d t).toRingHom
    Module.Flat R Q ↔ Module.Flat R M := by
  let _ := tangentAlgebra d t
  let B := HolGerm (ComplexModel (d+t))
  let R := HolGerm (ComplexModel d)
  let Q := HolGerm (ComplexModel ((d+t)+a)) ⧸ actualSquareZeroMatrixIdeal (d+t) a F
  let M := (Fin a → B) ⧸ LinearMap.range F.mulVecLin
  let _ : Algebra B (HolGerm (ComplexModel ((d+t)+a))) := tangentAlgebra (d+t) a
  let _ : Module R Q := Module.compHom Q (tangentPullback d t).toRingHom
  let _ : Module R M := Module.compHom M (tangentPullback d t).toRingHom
  change Module.Flat R Q ↔ Module.Flat R M
  let _ : Module R B := Module.compHom B (tangentPullback d t).toRingHom
  let _ : Module.Flat R B := tangentPullback_flat d t
  let e := actualSquareZeroMatrixAlgEquiv (d+t) a F
  let E : Q ≃ₗ[R] TrivSqZeroExt B M := {
    e.toRingEquiv.toAddEquiv with
    map_smul' := by
      intro r x
      change e ((tangentPullback d t r) • x) = (tangentPullback d t r) • e x
      exact e.toLinearEquiv.map_smul (tangentPullback d t r) x
  }
  rw [Module.Flat.equiv_iff E]
  exact flat_squareZero_iff
end
end Hironaka.Analytic.Unibranch.HironakaG10ActualSquareZeroFlatEquiv
