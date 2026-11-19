import Hironaka.Analytic.Unibranch.HironakaG10ReassociatedSquareZeroBaseChange
import Hironaka.Analytic.Unibranch.HironakaG10ReassociatedSquareZeroFlat
import Hironaka.Analytic.Unibranch.HironakaG10ActualSquareZeroFlatEquiv

/-! A canonical analytic flattener detects all smooth analytic base changes
of an arbitrary finite matrix cokernel. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped Topology
open Hironaka Hironaka
  HolGerm HironakaRelativeNormalIdeal HironakaHolomorphicJetChartInvariance
  HironakaActualAnalyticBaseChangeCoefficients HironakaChowPresentationIndependentFlattener
  HironakaG10HirFlatQuotient HironakaG10HirChartFlattener
  Hironaka.Analytic.Unibranch.HironakaG10ReassociatedSquareZeroIdeal
  Hironaka.Analytic.Unibranch.HironakaG10ReassociatedSquareZeroFlat
  Hironaka.Analytic.Unibranch.HironakaG10ReassociatedSquareZeroBaseChange
  Hironaka.Analytic.Unibranch.HironakaG10ActualSquareZeroFlatEquiv
namespace Hironaka.Analytic.Unibranch.HironakaG10MatrixSmoothBaseFlattener
noncomputable section

/-- The canonical whole-germ ideal associated with the actual square-zero
encoding of a finite matrix. -/
def matrixFlattenerIdeal (d t a : ℕ) {b : ℕ}
    (F : Matrix (Fin a) (Fin b) (HolGerm (ComplexModel (d+t)))) :
    Ideal (HolGerm (ComplexModel d)) :=
  canonicalFlattenerIdeal d (t+a) (reassociatedSquareZeroIdeal d t a F)

/-- The analytic pullback of the canonical ideal vanishes exactly when the
literal pulled-back matrix cokernel is flat over the new smooth base germs. -/
theorem matrixFlattenerIdeal_baseChange_flat_iff (d e t a : ℕ) {b : ℕ}
    (F : Matrix (Fin a) (Fin b) (HolGerm (ComplexModel (d+t))))
    (φ : ComplexModel e → ComplexModel d)
    (hφ : ∀ᶠ v in 𝓝 (0 : ComplexModel e), DifferentiableAt ℂ φ v) (hφ0 : φ 0 = 0) :
    letI := tangentAlgebra e t
    let R := HolGerm (ComplexModel e)
    let B := HolGerm (ComplexModel (e+t))
    let FM := F.map (jointBasePullback d e t φ hφ hφ0)
    let M := (Fin a → B) ⧸ LinearMap.range FM.mulVecLin
    letI : Module R M := Module.compHom M (tangentPullback e t).toRingHom
    Module.Flat R M ↔ Ideal.map (compAlgHom φ hφ hφ0).toRingHom (matrixFlattenerIdeal d t a F) = ⊥ := by
  let FM := F.map (jointBasePullback d e t φ hφ hφ0)
  have hchart : (chartMap e (t+a)
      (reassociatedSquareZeroIdeal e t a FM)).Flat ↔
      Ideal.map (compAlgHom φ hφ hφ0).toRingHom (matrixFlattenerIdeal d t a F) = ⊥ := by
    unfold matrixFlattenerIdeal
    rw [← flat_quotMap_bot_iff, ← map_reassociatedSquareZeroIdeal_baseChange d e t a φ hφ hφ0 F,
      isFlattenerIdeal_chartMap_baseChange d (t+a) _ e φ hφ hφ0, le_bot_iff]
  have hsplit := (chartMap_reassociated_flat_iff_nested e t a FM).trans
    (actualSquareZeroMatrix_flat_iff e t a FM)
  exact hsplit.symm.trans hchart
end
end Hironaka.Analytic.Unibranch.HironakaG10MatrixSmoothBaseFlattener
