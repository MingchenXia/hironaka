import Hironaka.Resolution.HironakaG10LinearCurveMatrixPullback
import Hironaka.Resolution.HironakaG10OneParameterCokernelFlatness

/-! Actual arbitrary-rank matrix-cokernel flatness along every linear base curve. -/
set_option autoImplicit false
open Filter Set
open scoped Topology
namespace Hironaka.Analytic.Unibranch.HironakaG10HigherRankCurveFlat
open Hironaka Hironaka
  OkaRelationSheaf HironakaRelativeNormalIdeal HironakaActualCentreJointJets
  HironakaG10FlatResolutionStart HironakaG10LinearCurveMatrixPullback
  HironakaG10FibreRegularCriterion HironakaG10OneParameterCokernelFlatness
noncomputable section

/-- Exactness of the original normal fibre makes the actual arbitrary-rank
matrix cokernel flat over the actual parameter ring after every linear curve. -/
theorem curve_cokernel_flat_of_exact_normal_fibre {a b c : ℕ} (d t : ℕ)
    (F : Fin a → Fin b → ComplexModel (d + t) → ℂ)
    (G : Fin b → Fin c → ComplexModel (d + t) → ℂ)
    (hF : ∀ i j, HolAt (F i j) 0)
    (hG : ∀ j k, HolAt (G j k) 0)
    (hcomp : ∀ i k, ∀ᶠ x in 𝓝 (0 : ComplexModel (d + t)),
      ∑ j, F i j x * G j k x = 0)
    (hfib : ∀ v : Fin b → ComplexModel t → ℂ,
      IsRelationAt (fun i j z => F i j (actualJointNormalInclusion d t z)) 0 v →
      IsCombinationAt (columns (fun j k z => G j k (actualJointNormalInclusion d t z))) 0 v)
    (L : ComplexModel 1 →L[ℂ] ComplexModel d) :
    let FM := curveProductFamily d t L F
    letI : Module (HolGerm ℂ) (germCokernel FM (0 : ComplexModel t)) :=
      parameterModule FM (0 : ComplexModel t)
    Module.Flat (HolGerm ℂ) (germCokernel FM (0 : ComplexModel t)) := by
  apply flat_germCokernel_of_regularAt
  · exact holAt_curveProductFamily d t L F hF
  · exact regularAt_of_slice_exact
      (holAt_curveProductFamily d t L F hF)
      (holAt_curveProductFamily d t L G hG)
      (zero_comp_curveProductFamily d t L F G hcomp)
      (fibre_exact_curveProductFamily d t L F G hfib)
end
end Hironaka.Analytic.Unibranch.HironakaG10HigherRankCurveFlat
