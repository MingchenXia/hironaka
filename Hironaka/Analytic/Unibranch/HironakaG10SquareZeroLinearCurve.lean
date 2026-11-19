import Hironaka.Analytic.Unibranch.HironakaG10ActualSquareZeroBaseChange
import Hironaka.Resolution.HironakaG10LinearCurveMatrixPullback

/-! Literal linear-curve naturality of the actual square-zero matrix ideal. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Filter Set
open scoped Topology
open Hironaka Hironaka
  HolGerm OkaGermBridge OkaRelationSheaf HironakaRelativeNormalIdeal
  HironakaActualAnalyticBaseChangeCoefficients HironakaHolomorphicJetChartInvariance
  HironakaG10FlatGermChain HironakaG10LinearCurveMatrixPullback
  Hironaka.Analytic.Unibranch.HironakaG10ActualSquareZeroMatrixEquiv
  Hironaka.Analytic.Unibranch.HironakaG10ActualSquareZeroBaseChange
namespace Hironaka.Analytic.Unibranch.HironakaG10SquareZeroLinearCurve
noncomputable section

/-- Each germ matrix entry after the actual joint linear-curve pullback is the
literal germ of the pulled-back original matrix entry. -/
theorem linearCurve_germMatrix (d t : ℕ) {a b : ℕ}
    (L : ComplexModel 1 →L[ℂ] ComplexModel d)
    (F : Fin a → Fin b → ComplexModel (d+t) → ℂ)
    (hF : ∀ i j, HolAt (F i j) 0) :
    (germMat 0 F).map (jointBasePullback d 1 t L
      (Eventually.of_forall fun _ => L.differentiableAt) L.map_zero) =
      germMat 0 (curveFamily d t L F) := by
  apply Matrix.ext
  intro i j
  exact jointBasePullback_germAt d t L (F i j) (hF i j)

/-- The full explicit analytic square-zero ideal of the original germ matrix
maps exactly to the corresponding ideal of its original pulled-back curve matrix. -/
theorem linearCurve_actualSquareZeroMatrixIdeal (d t a : ℕ) {b : ℕ}
    (L : ComplexModel 1 →L[ℂ] ComplexModel d)
    (F : Fin a → Fin b → ComplexModel (d+t) → ℂ)
    (hF : ∀ i j, HolAt (F i j) 0) :
    let φ := linearJointMap d t L
    let hφ : ∀ᶠ v in 𝓝 (0 : ComplexModel (1+t)), DifferentiableAt ℂ φ v :=
      Eventually.of_forall fun _ => φ.differentiableAt
    let hφ0 : φ 0 = 0 := φ.map_zero
    Ideal.map (jointBasePullback (d+t) (1+t) a φ hφ hφ0).toRingHom
      (actualSquareZeroMatrixIdeal (d+t) a (germMat 0 F)) =
      actualSquareZeroMatrixIdeal (1+t) a (germMat 0 (curveFamily d t L F)) := by
  let φ := linearJointMap d t L
  let hφ : ∀ᶠ v in 𝓝 (0 : ComplexModel (1+t)), DifferentiableAt ℂ φ v :=
    Eventually.of_forall fun _ => φ.differentiableAt
  let hφ0 : φ 0 = 0 := φ.map_zero
  have hmat : (germMat 0 F).map (compAlgHom φ hφ hφ0) = germMat 0 (curveFamily d t L F) := by
    exact linearCurve_germMatrix d t L F hF
  simpa only [hmat] using map_actualSquareZeroMatrixIdeal (d+t) (1+t) a φ hφ hφ0 (germMat 0 F)
end
end Hironaka.Analytic.Unibranch.HironakaG10SquareZeroLinearCurve
