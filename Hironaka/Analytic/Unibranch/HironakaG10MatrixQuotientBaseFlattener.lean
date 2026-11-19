import Hironaka.Analytic.Unibranch.HironakaG10MatrixSmoothBaseFlattener
import Hironaka.Analytic.Unibranch.HironakaG10FlatSquareZeroBaseChange

/-! Matrix flattener on arbitrary quotient test bases, including nonreduced ones. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped Topology TensorProduct
open Hironaka Hironaka
  HolGerm HironakaRelativeNormalIdeal HironakaHolomorphicJetChartInvariance
  HironakaActualAnalyticBaseChangeCoefficients HironakaChowPresentationIndependentFlattener
  HironakaG10HirFlatQuotient HironakaG10HirChartFlattener
  Hironaka.Analytic.Unibranch.HironakaG10ModelAssociativityGerm
  Hironaka.Analytic.Unibranch.HironakaG10ActualSquareZeroMatrixEquiv
  Hironaka.Analytic.Unibranch.HironakaG10ReassociatedSquareZeroIdeal
  Hironaka.Analytic.Unibranch.HironakaG10ReassociatedSquareZeroFlat
  Hironaka.Analytic.Unibranch.HironakaG10ReassociatedSquareZeroBaseChange
  Hironaka.Analytic.Unibranch.HironakaG10FlatSquareZeroBaseChange
  Hironaka.Analytic.Unibranch.HironakaG10SmoothProjectionFlat
  Hironaka.Analytic.Unibranch.HironakaG10MatrixSmoothBaseFlattener
namespace Hironaka.Analytic.Unibranch.HironakaG10MatrixQuotientBaseFlattener
noncomputable section

/-- Flatness of the actual square-zero chart after quotienting the base is
flatness of the corresponding tensor-base-changed original matrix cokernel. -/
theorem chartMap_quot_flat_iff_tensor_matrix (d t a : ℕ) {b : ℕ}
    (F : Matrix (Fin a) (Fin b) (HolGerm (ComplexModel (d+t))))
    (I : Ideal (HolGerm (ComplexModel d))) :
    letI := tangentAlgebra d t
    let R := HolGerm (ComplexModel d)
    let B := HolGerm (ComplexModel (d+t))
    let M := (Fin a → B) ⧸ LinearMap.range F.mulVecLin
    letI : Module R M := Module.compHom M (tangentPullback d t).toRingHom
    (quotMap (chartMap d (t+a) (reassociatedSquareZeroIdeal d t a F)) I).Flat ↔
      Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M) := by
  letI := tangentAlgebra d t
  let B := HolGerm (ComplexModel (d+t))
  let R := HolGerm (ComplexModel d)
  let J := actualSquareZeroMatrixIdeal (d+t) a F
  let Q := HolGerm (ComplexModel ((d+t)+a)) ⧸ J
  let M := (Fin a → B) ⧸ LinearMap.range F.mulVecLin
  let C := HolGerm (ComplexModel (d+(t+a))) ⧸ reassociatedSquareZeroIdeal d t a F
  let η : R →+* Q := (Ideal.Quotient.mk J).comp
    ((tangentPullback (d+t) a).toRingHom.comp (tangentPullback d t).toRingHom)
  letI : Algebra B (HolGerm (ComplexModel ((d+t)+a))) := tangentAlgebra (d+t) a
  letI : Module R Q := Module.compHom Q (tangentPullback d t).toRingHom
  letI : Module R M := Module.compHom M (tangentPullback d t).toRingHom
  letI : Algebra R C := (chartMap d (t+a) (reassociatedSquareZeroIdeal d t a F)).toAlgebra
  letI : Module.Flat R B := tangentPullback_flat d t
  let e := Ideal.quotientEquiv J (reassociatedSquareZeroIdeal d t a F) (assocGermEquiv d t a) rfl
  have he : e.toRingHom.comp η = chartMap d (t+a) (reassociatedSquareZeroIdeal d t a F) := by
    apply RingHom.ext
    intro r
    change Ideal.Quotient.mk (reassociatedSquareZeroIdeal d t a F)
      (assocGermEquiv d t a (tangentPullback (d+t) a (tangentPullback d t r))) = _
    rw [assocGermEquiv_tangentPullback]
    rfl
  let E0 : Q ≃ₗ[R] C := {
    e.toAddEquiv with
    map_smul' := by
      intro r x
      change e (η r * x) = (chartMap d (t+a) (reassociatedSquareZeroIdeal d t a F) r) * e x
      rw [map_mul, ← he]
      rfl
  }
  let e2 := actualSquareZeroMatrixAlgEquiv (d+t) a F
  let E2 : Q ≃ₗ[R] B × M := {
    e2.toRingEquiv.toAddEquiv with
    map_smul' := by
      intro r x
      change e2 ((tangentPullback d t r) • x) = (tangentPullback d t r) • e2 x
      exact e2.toLinearEquiv.map_smul (tangentPullback d t r) x
  }
  exact flat_quotMap_iff_tensor_summand (E0.symm.trans E2) I

/-- The same canonical matrix flattener has its full universal property for
every analytic source quotient, including singular and nonreduced quotients. -/
theorem matrixFlattenerIdeal_quotient_baseChange_flat_iff (d e t a : ℕ) {b : ℕ}
    (F : Matrix (Fin a) (Fin b) (HolGerm (ComplexModel (d+t))))
    (φ : ComplexModel e → ComplexModel d)
    (hφ : ∀ᶠ v in 𝓝 (0 : ComplexModel e), DifferentiableAt ℂ φ v) (hφ0 : φ 0 = 0)
    (I : Ideal (HolGerm (ComplexModel e))) :
    letI := tangentAlgebra e t
    let R := HolGerm (ComplexModel e)
    let B := HolGerm (ComplexModel (e+t))
    let FM := F.map (jointBasePullback d e t φ hφ hφ0)
    let M := (Fin a → B) ⧸ LinearMap.range FM.mulVecLin
    letI : Module R M := Module.compHom M (tangentPullback e t).toRingHom
    Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M) ↔
      Ideal.map (compAlgHom φ hφ hφ0).toRingHom (matrixFlattenerIdeal d t a F) ≤ I := by
  let FM := F.map (jointBasePullback d e t φ hφ hφ0)
  have hchart := isFlattenerIdeal_chartMap_baseChange d (t+a)
    (reassociatedSquareZeroIdeal d t a F) e φ hφ hφ0 I
  rw [map_reassociatedSquareZeroIdeal_baseChange] at hchart
  exact (chartMap_quot_flat_iff_tensor_matrix e t a FM I).symm.trans hchart

end
end Hironaka.Analytic.Unibranch.HironakaG10MatrixQuotientBaseFlattener
