import Hironaka.Analytic.Unibranch.HironakaG10NativeLinearCurveFlat
import Hironaka.Analytic.Unibranch.HironakaG10ActualSquareZeroFlatEquiv
import Hironaka.Analytic.Unibranch.HironakaG10SquareZeroLinearCurve

/-! Actual square-zero analytic quotient flatness along every linear curve. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped Topology
open Hironaka Hironaka
  HolGerm OkaRelationSheaf HironakaRelativeNormalIdeal HironakaActualCentreJointJets
  HironakaG10FlatGermChain HironakaG10FlatResolutionStart HironakaG10SmoothBaseFibreExactness
  HironakaG10LinearCurveMatrixPullback
  Hironaka.Analytic.Unibranch.HironakaG10NativeLinearCurveFlat
  Hironaka.Analytic.Unibranch.HironakaG10ActualSquareZeroMatrixEquiv
  Hironaka.Analytic.Unibranch.HironakaG10ActualSquareZeroFlatEquiv
namespace Hironaka.Analytic.Unibranch.HironakaG10SquareZeroCurveFlat
noncomputable section
local instance (t : ℕ) : Algebra (HolGerm (ComplexModel 1)) (HolGerm (ComplexModel (1+t))) :=
  tangentAlgebra 1 t

/-- Exactness of the original normal fibre makes the actual square-zero
analytic quotient flat on every linear curve, with the nested tangent action. -/
theorem curve_squareZero_quotient_flat {a b c : ℕ} (d t : ℕ)
    (F : Fin a → Fin b → ComplexModel (d+t) → ℂ)
    (G : Fin b → Fin c → ComplexModel (d+t) → ℂ)
    (hF : ∀ i j, HolAt (F i j) 0)
    (hG : ∀ j k, HolAt (G j k) 0)
    (hcomp : ∀ i k, ∀ᶠ x in 𝓝 (0 : ComplexModel (d+t)), ∑ j, F i j x * G j k x = 0)
    (hfib : ∀ v : Fin b → ComplexModel t → ℂ,
      IsRelationAt (fun i j z => F i j (actualJointNormalInclusion d t z)) 0 v →
      IsCombinationAt (columns (fun j k z => G j k (actualJointNormalInclusion d t z))) 0 v)
    (L : ComplexModel 1 →L[ℂ] ComplexModel d) :
    let R := HolGerm (ComplexModel 1)
    let B := HolGerm (ComplexModel (1+t))
    let FM := germMat 0 (curveFamily d t L F)
    let Q := HolGerm (ComplexModel ((1+t)+a)) ⧸ actualSquareZeroMatrixIdeal (1+t) a FM
    letI : Algebra B (HolGerm (ComplexModel ((1+t)+a))) := tangentAlgebra (1+t) a
    letI : Module R Q := Module.compHom Q (tangentPullback 1 t).toRingHom
    Module.Flat R Q := by
  let R := HolGerm (ComplexModel 1)
  let B := HolGerm (ComplexModel (1+t))
  let FM := germMat 0 (curveFamily d t L F)
  let Q := HolGerm (ComplexModel ((1+t)+a)) ⧸ actualSquareZeroMatrixIdeal (1+t) a FM
  let M := (Fin a → B) ⧸ LinearMap.range FM.mulVecLin
  letI : Algebra B (HolGerm (ComplexModel ((1+t)+a))) := tangentAlgebra (1+t) a
  letI : Module R Q := Module.compHom Q (tangentPullback 1 t).toRingHom
  letI : Module R M := Module.compHom M (tangentPullback 1 t).toRingHom
  change Module.Flat R Q
  have hn : Module.Flat R (nativeCokernel 1 t FM) :=
    native_curve_cokernel_flat_of_exact_normal_fibre d t F G hF hG hcomp hfib L
  have hn' : Module.Flat R ((Fin a → B) ⧸ (LinearMap.range FM.mulVecLin).restrictScalars R) := by
    exact hn
  have hm : Module.Flat R M := by
    letI := hn'
    exact Module.Flat.of_linearEquiv (Submodule.Quotient.restrictScalarsEquiv R (LinearMap.range FM.mulVecLin)).symm
  exact (actualSquareZeroMatrix_flat_iff 1 t a FM).mpr hm
end
end Hironaka.Analytic.Unibranch.HironakaG10SquareZeroCurveFlat
