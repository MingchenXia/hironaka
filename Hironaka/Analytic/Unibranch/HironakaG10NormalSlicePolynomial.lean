import Hironaka.Analytic.Unibranch.HironakaG10MovingParameterSlice
import Hironaka.Resolution.HironakaRelativeNormalNormalPowerSpread

/-! # Actual finite normal-polynomial values on the parameter slice -/
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace Hironaka.Analytic.Unibranch.HironakaG10NormalSlicePolynomial
open Hironaka Hironaka
  OkaRelationSheaf HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaActualJointBaseFibre HironakaActualCentreJointJets
  HironakaRelativeNormalNormalPowerSpread HironakaHolomorphicJetMonomialSpan
  HironakaHolomorphicJetChartInvariance

/-- The actual normal slice of a tangential coefficient germ is its value
at the original fibre point, as a constant parameter germ. -/
theorem jointBaseZeroTrace_tangentPullback (t d : ℕ) (c : HolGerm (ComplexModel t)) :
    jointBaseZeroTrace t d (tangentPullback t d c) = HolGerm.constHom (HolGerm.eval c) := by
  induction c using HolGerm.induction_on with
  | h C hC =>
    unfold jointBaseZeroTrace tangentPullback
    rw [compAlgHom_mk,compAlgHom_mk,HolGerm.constHom_apply,HolGerm.eval_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    apply Eventually.of_forall
    intro z
    simp [Function.comp_def,tangentProjection_actualJointNormalInclusion]

/-- Evaluation of the actual finite normal polynomial on the parameter
slice is the finite sum of its original coefficient values times the images
of its actual parameter-coordinate monomials. -/
theorem parameterSlice_actualNormalPolynomial
    {Q : Type*} [CommRing Q] [Algebra ℂ Q] (t d q : ℕ)
    (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Q)
    (C : normalExponentIndex d q → ComplexModel t → ℂ) (hC : ∀ α, HolAt (C α) 0) :
    let := normalExponentFintype d q
    φ (jointBaseZeroTrace t d
      (HolGerm.mk (actualNormalPolynomialFunction t d q C)
        (actualNormalPolynomialFunction_holAt t d q C hC))) =
      ∑ α, (∏ i : Fin d, φ (coordinateGerm i) ^ α.val i) * algebraMap ℂ Q (C α 0) := by
  classical
  let := normalExponentFintype d q
  rw [mk_actualNormalPolynomialFunction t d q C hC]
  simp only [map_sum,map_mul]
  apply Finset.sum_congr rfl
  intro α hα
  rw [jointBaseZeroTrace_tangentPullback,HolGerm.eval_mk]
  have hc : φ (HolGerm.constHom (C α 0)) = algebraMap ℂ Q (C α 0) := φ.commutes _
  rw [hc]
  simp only [normalExponentMonomial,map_prod,map_pow,jointBaseZeroTrace_normalCoordinate]
  exact mul_comm _ _

end Hironaka.Analytic.Unibranch.HironakaG10NormalSlicePolynomial
