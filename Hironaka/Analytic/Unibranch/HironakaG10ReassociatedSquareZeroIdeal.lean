import Hironaka.Analytic.Unibranch.HironakaG10ModelAssociativityGerm

/-! Whole square-zero ideals under reassociated linear curve pullback. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped Topology
open Hironaka Hironaka
  HolGerm OkaGermBridge OkaRelationSheaf HironakaRelativeNormalIdeal
  HironakaActualAnalyticBaseChangeCoefficients HironakaG10FlatGermChain
  HironakaG10LinearCurveMatrixPullback
  Hironaka.Analytic.Unibranch.HironakaG10ActualSquareZeroMatrixEquiv
  Hironaka.Analytic.Unibranch.HironakaG10SquareZeroLinearCurve
  Hironaka.Analytic.Unibranch.HironakaG10ModelAssociativityGerm
namespace Hironaka.Analytic.Unibranch.HironakaG10ReassociatedSquareZeroIdeal
noncomputable section

/-- The whole explicit matrix ideal in the single-base reassociated model. -/
def reassociatedSquareZeroIdeal (d t a : ℕ) {b : ℕ}
    (F : Matrix (Fin a) (Fin b) (HolGerm (ComplexModel (d+t)))) :
    Ideal (HolGerm (ComplexModel (d+(t+a)))) :=
  Ideal.map (assocGermEquiv d t a).toRingHom (actualSquareZeroMatrixIdeal (d+t) a F)

/-- Every actual single-curve pullback carries the whole reassociated ideal
exactly to the reassociated ideal of the literal original curve matrix. -/
theorem map_reassociatedSquareZeroIdeal_linearCurve (d t a : ℕ) {b : ℕ}
    (L : ComplexModel 1 →L[ℂ] ComplexModel d)
    (F : Fin a → Fin b → ComplexModel (d+t) → ℂ)
    (hF : ∀ i j, HolAt (F i j) 0) :
    Ideal.map (jointBasePullback d 1 (t+a) L
      (Eventually.of_forall fun _ => L.differentiableAt) L.map_zero).toRingHom
        (reassociatedSquareZeroIdeal d t a (germMat 0 F)) =
      reassociatedSquareZeroIdeal 1 t a (germMat 0 (curveFamily d t L F)) := by
  let φ := linearJointMap d t L
  let hφ : ∀ᶠ v in 𝓝 (0 : ComplexModel (1+t)), DifferentiableAt ℂ φ v :=
    Eventually.of_forall fun _ => φ.differentiableAt
  let hφ0 : φ 0 = 0 := φ.map_zero
  have hmap : (jointBasePullback d 1 (t+a) L
      (Eventually.of_forall fun _ => L.differentiableAt) L.map_zero).toRingHom.comp
        (assocGermEquiv d t a).toRingHom =
      (assocGermEquiv 1 t a).toRingHom.comp
        (jointBasePullback (d+t) (1+t) a φ hφ hφ0).toRingHom := by
    apply RingHom.ext
    intro g
    change jointBasePullback d 1 (t+a) L (Eventually.of_forall fun _ => L.differentiableAt) L.map_zero
        (assocGermEquiv d t a g) = assocGermEquiv 1 t a
          (jointBasePullback (d+t) (1+t) a φ hφ hφ0 g)
    exact assocGermEquiv_linearCurve d t a L g
  unfold reassociatedSquareZeroIdeal
  rw [Ideal.map_map, hmap, ← Ideal.map_map]
  rw [linearCurve_actualSquareZeroMatrixIdeal d t a L F hF]
end
end Hironaka.Analytic.Unibranch.HironakaG10ReassociatedSquareZeroIdeal
