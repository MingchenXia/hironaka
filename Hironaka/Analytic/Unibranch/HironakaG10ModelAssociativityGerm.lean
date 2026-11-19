import Hironaka.Analytic.Unibranch.HironakaG10ModelAssociativity

/-! The actual whole-germ pullback square for nested model reassociation. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped Topology
open Hironaka Hironaka
  HolGerm HironakaHolomorphicJetChartInvariance HironakaActualAnalyticBaseChangeCoefficients
  HironakaG10LinearCurveMatrixPullback
  Hironaka.Analytic.Unibranch.HironakaG10ModelAssociativity
namespace Hironaka.Analytic.Unibranch.HironakaG10ModelAssociativityGerm
noncomputable section

/-- The actual whole-germ isomorphism induced by coordinate reassociation. -/
def assocGermEquiv (d t a : ℕ) : HolGerm (ComplexModel ((d+t)+a)) ≃+*
    HolGerm (ComplexModel (d+(t+a))) :=
  HolGerm.comapEquiv (assocModel d t a).symm

/-- The original whole germ pulled along the single curve agrees exactly with
nested curve pullback after reassociating source and target models. -/
theorem assocGermEquiv_linearCurve (d t a : ℕ) (L : ComplexModel 1 →L[ℂ] ComplexModel d)
    (g : HolGerm (ComplexModel ((d+t)+a))) :
    let φ := linearJointMap d t L
    let hφ : ∀ᶠ v in 𝓝 (0 : ComplexModel (1+t)), DifferentiableAt ℂ φ v :=
      Eventually.of_forall fun _ => φ.differentiableAt
    let hφ0 : φ 0 = 0 := φ.map_zero
    jointBasePullback d 1 (t+a) L (Eventually.of_forall fun _ => L.differentiableAt) L.map_zero
        (assocGermEquiv d t a g) =
      assocGermEquiv 1 t a (jointBasePullback (d+t) (1+t) a φ hφ hφ0 g) := by
  let φ := linearJointMap d t L
  let hφ : ∀ᶠ v in 𝓝 (0 : ComplexModel (1+t)), DifferentiableAt ℂ φ v :=
    Eventually.of_forall fun _ => φ.differentiableAt
  let hφ0 : φ 0 = 0 := φ.map_zero
  have hpoint (w : ComplexModel (1+(t+a))) :
      (assocModel d t a).symm (jointBaseMap d 1 (t+a) L w) =
        jointBaseMap (d+t) (1+t) a φ ((assocModel 1 t a).symm w) := by
    apply (assocModel d t a).injective
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    simpa [φ] using (assocModel_linearCurve d t a L ((assocModel 1 t a).symm w)).symm
  dsimp only
  induction g using HolGerm.induction_on with
  | h f hf =>
    unfold assocGermEquiv jointBasePullback
    rw [HolGerm.comapEquiv_mk,compAlgHom_mk,compAlgHom_mk,HolGerm.comapEquiv_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun w => congrArg f (hpoint w)
end
end Hironaka.Analytic.Unibranch.HironakaG10ModelAssociativityGerm
