import Hironaka.Analytic.Unibranch.HironakaG10ModelAssociativityBaseChange
import Hironaka.Analytic.Unibranch.HironakaG10ReassociatedSquareZeroIdeal
import Hironaka.Analytic.Unibranch.HironakaG10ActualSquareZeroBaseChange

/-! Whole square-zero ideals under arbitrary analytic base change. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped Topology
open Hironaka Hironaka
  HolGerm OkaGermBridge OkaRelationSheaf HironakaRelativeNormalIdeal
  HironakaActualAnalyticBaseChangeCoefficients HironakaHolomorphicJetChartInvariance
  Hironaka.Analytic.Unibranch.HironakaG10ActualSquareZeroMatrixEquiv
  Hironaka.Analytic.Unibranch.HironakaG10ActualSquareZeroBaseChange
  Hironaka.Analytic.Unibranch.HironakaG10ModelAssociativityGerm
  Hironaka.Analytic.Unibranch.HironakaG10ModelAssociativityBaseChange
  Hironaka.Analytic.Unibranch.HironakaG10ReassociatedSquareZeroIdeal
namespace Hironaka.Analytic.Unibranch.HironakaG10ReassociatedSquareZeroBaseChange
noncomputable section

/-- An arbitrary holomorphic base change maps the entire reassociated
square-zero matrix ideal to that of the actual entrywise pulled-back matrix. -/
theorem map_reassociatedSquareZeroIdeal_baseChange (d e t a : ℕ) {b : ℕ}
    (φ : ComplexModel e → ComplexModel d)
    (hφ : ∀ᶠ v in 𝓝 (0 : ComplexModel e), DifferentiableAt ℂ φ v) (hφ0 : φ 0 = 0)
    (F : Matrix (Fin a) (Fin b) (HolGerm (ComplexModel (d+t)))) :
    Ideal.map (jointBasePullback d e (t+a) φ hφ hφ0).toRingHom
        (reassociatedSquareZeroIdeal d t a F) =
      reassociatedSquareZeroIdeal e t a (F.map
        (jointBasePullback d e t φ hφ hφ0)) := by
  have hmap : (jointBasePullback d e (t+a) φ hφ hφ0).toRingHom.comp
        (assocGermEquiv d t a).toRingHom =
      (assocGermEquiv e t a).toRingHom.comp
        (jointBasePullback (d+t) (e+t) a (jointBaseMap d e t φ)
          (jointBaseMap_holomorphic d e t φ hφ) (jointBaseMap_origin d e t φ hφ0)).toRingHom := by
    apply RingHom.ext
    intro g
    exact assocGermEquiv_baseChange d e t a φ hφ hφ0 g
  unfold reassociatedSquareZeroIdeal
  rw [Ideal.map_map, hmap, ← Ideal.map_map]
  rw [map_actualSquareZeroMatrixIdeal]
  rfl
end
end Hironaka.Analytic.Unibranch.HironakaG10ReassociatedSquareZeroBaseChange
