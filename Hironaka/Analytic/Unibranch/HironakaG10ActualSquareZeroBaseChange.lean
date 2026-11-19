import Hironaka.Analytic.Unibranch.HironakaG10ActualSquareZeroMatrixEquiv
import Hironaka.Resolution.HironakaActualAnalyticBaseChangeCoefficients

/-! The whole actual square-zero matrix ideal commutes with analytic base change. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Filter Set
open scoped Topology
open Hironaka Hironaka
  HironakaRelativeNormalIdeal HironakaActualAnalyticBaseChangeCoefficients
  HironakaHolomorphicJetChartInvariance
  Hironaka.Analytic.Unibranch.HironakaG10ActualSquareZeroColumns
  Hironaka.Analytic.Unibranch.HironakaG10ActualSquareZeroMatrixEquiv
namespace Hironaka.Analytic.Unibranch.HironakaG10ActualSquareZeroBaseChange
noncomputable section

/-- Every original square-zero matrix ideal is mapped exactly to the one
built from the entire base-changed original matrix. -/
theorem map_actualSquareZeroMatrixIdeal (d e a : ℕ) {b : ℕ}
    (φ : ComplexModel e → ComplexModel d)
    (hφ : ∀ᶠ v in 𝓝 (0 : ComplexModel e), DifferentiableAt ℂ φ v) (hφ0 : φ 0 = 0)
    (F : Matrix (Fin a) (Fin b) (HolGerm (ComplexModel d))) :
    Ideal.map (jointBasePullback d e a φ hφ hφ0).toRingHom (actualSquareZeroMatrixIdeal d a F) =
      actualSquareZeroMatrixIdeal e a (F.map (compAlgHom φ hφ hφ0)) := by
  unfold actualSquareZeroMatrixIdeal
  rw [Ideal.map_sup, Ideal.map_pow, jointBasePullback_map_normalIdeal]
  congr 1
  rw [Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext j
  simp only [Function.comp_apply, actualMatrixColumn, map_sum, map_mul, Matrix.map_apply]
  apply Finset.sum_congr rfl
  intro i hi
  change jointBasePullback d e a φ hφ hφ0 (tangentPullback d a (F i j)) *
      jointBasePullback d e a φ hφ hφ0 (normalCoordinate d a i) = _
  rw [jointBasePullback_tangentPullback, jointBasePullback_normalCoordinate]
end
end Hironaka.Analytic.Unibranch.HironakaG10ActualSquareZeroBaseChange
