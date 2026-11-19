import Hironaka.Resolution.HironakaActualRelativeCoefficientGerms
import Hironaka.Resolution.HironakaActualJointBaseFibre
import Hironaka.Resolution.HironakaChowNormalSupportProjection

/-! Actual different-dimension analytic base change of ALL normal coefficients.
Only genuine phi:C^e→C^d, holomorphicity near0 and phi0=0 are input.
BP FIRST: hironaka-actual-analytic-base-change-coefficients.tex.
No extended-I/tensor=analytic/flattener assertion. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualAnalyticBaseChangeCoefficients
noncomputable section
open HolGerm HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaActualRelativeCoefficientGerms HironakaHolomorphicJetChartInvariance
  HironakaActualCentreJointJets HironakaActualJointBaseFibre HironakaChowNormalSupportProjection

/-- Literal joint (v,z)↦(phi(v),z), with SAME original normal labels. -/
def jointBaseMap (d e t : ℕ) (φ : ComplexModel e→ComplexModel d)
    (w : ComplexModel (e+t)) : ComplexModel (d+t) :=
  tangentInclusion d t (φ (tangentProjection e t w)) +
    actualJointNormalInclusion d t (actualJointNormalProjection e t w)

private theorem tangentProjection_jointBaseMap (d e t : ℕ)
    (φ : ComplexModel e→ComplexModel d) (w : ComplexModel (e+t)) :
    tangentProjection d t (jointBaseMap d e t φ w)=φ (tangentProjection e t w) := by
  simp only [jointBaseMap,map_add,tangentProjection_tangentInclusion,
    tangentProjection_actualJointNormalInclusion,add_zero]

private theorem jointBaseMap_normal (d e t : ℕ)
    (φ : ComplexModel e→ComplexModel d) (w : ComplexModel (e+t)) (i : Fin t) :
    jointBaseMap d e t φ w (i.natAdd d)=w (i.natAdd e) := by
  simp only [jointBaseMap,PiLp.add_apply,tangentInclusion_normal,
    actualJointNormalInclusion_normal,actualJointNormalProjection_apply,zero_add]

private theorem holomorphic_jointBaseMap (d e t : ℕ)
    (φ : ComplexModel e→ComplexModel d)
    (hφ : ∀ᶠ v in 𝓝 (0 : ComplexModel e),DifferentiableAt ℂ φ v) :
    ∀ᶠ w in 𝓝 (0 : ComplexModel (e+t)),DifferentiableAt ℂ (jointBaseMap d e t φ) w := by
  have hp : Tendsto (tangentProjection e t) (𝓝 (0 : ComplexModel (e+t)))
      (𝓝 (0 : ComplexModel e)) := by
    simpa only [map_zero] using (tangentProjection e t).continuous.tendsto 0
  filter_upwards [hp.eventually hφ] with w hw
  exact ((tangentInclusion d t).differentiableAt.comp w
    (hw.comp w (tangentProjection e t).differentiableAt)).add
      ((actualJointNormalInclusion d t).differentiableAt.comp w
        (actualJointNormalProjection e t).differentiableAt)

private theorem jointBaseMap_zero (d e t : ℕ) (φ : ComplexModel e→ComplexModel d)
    (hφ0 : φ 0=0) : jointBaseMap d e t φ 0=0 := by
  simp only [jointBaseMap,map_zero,hφ0,zero_add]

/-- Actual original analytic composition S_(d,t)→S_(e,t). -/
def jointBasePullback (d e t : ℕ) (φ : ComplexModel e→ComplexModel d)
    (hφ : ∀ᶠ v in 𝓝 (0 : ComplexModel e),DifferentiableAt ℂ φ v) (hφ0 : φ 0=0) :
    HolGerm (ComplexModel (d+t)) →ₐ[ℂ] HolGerm (ComplexModel (e+t)) :=
  compAlgHom (jointBaseMap d e t φ) (holomorphic_jointBaseMap d e t φ hφ)
    (jointBaseMap_zero d e t φ hφ0)

/-- Full tangent scalar square with the SAME original base pullback. -/
theorem jointBasePullback_tangentPullback (d e t : ℕ)
    (φ : ComplexModel e→ComplexModel d)
    (hφ : ∀ᶠ v in 𝓝 (0 : ComplexModel e),DifferentiableAt ℂ φ v) (hφ0 : φ 0=0)
    (a : HolGerm (ComplexModel d)) :
    jointBasePullback d e t φ hφ hφ0 (tangentPullback d t a)=
      tangentPullback e t (compAlgHom φ hφ hφ0 a) := by
  induction a using HolGerm.induction_on with
  | h f hf =>
    unfold jointBasePullback tangentPullback
    rw [compAlgHom_mk,compAlgHom_mk,compAlgHom_mk,compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun w=>congrArg f (tangentProjection_jointBaseMap d e t φ w)

/-- Every actual normal coordinate keeps its ORIGINAL label. -/
theorem jointBasePullback_normalCoordinate (d e t : ℕ)
    (φ : ComplexModel e→ComplexModel d)
    (hφ : ∀ᶠ v in 𝓝 (0 : ComplexModel e),DifferentiableAt ℂ φ v) (hφ0 : φ 0=0)
    (i : Fin t) :
    jointBasePullback d e t φ hφ hφ0 (normalCoordinate d t i)=normalCoordinate e t i := by
  unfold jointBasePullback normalCoordinate HironakaHolomorphicJetMonomialSpan.coordinateGerm
  rw [compAlgHom_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun w=>jointBaseMap_normal d e t φ w i

/-- Whole normal ideals are mapped exactly, including t=0. -/
theorem jointBasePullback_map_normalIdeal (d e t : ℕ)
    (φ : ComplexModel e→ComplexModel d)
    (hφ : ∀ᶠ v in 𝓝 (0 : ComplexModel e),DifferentiableAt ℂ φ v) (hφ0 : φ 0=0) :
    Ideal.map (jointBasePullback d e t φ hφ hφ0).toRingHom (normalIdeal d t)=normalIdeal e t := by
  unfold normalIdeal
  rw [Ideal.map_span,←Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  exact jointBasePullback_normalCoordinate d e t φ hφ hφ0 i

/-- Every ENTIRE actual normal power is preserved. -/
theorem jointBasePullback_mem_normalIdeal_pow (d e t : ℕ)
    (φ : ComplexModel e→ComplexModel d)
    (hφ : ∀ᶠ v in 𝓝 (0 : ComplexModel e),DifferentiableAt ℂ φ v) (hφ0 : φ 0=0)
    (q : ℕ) (F : HolGerm (ComplexModel (d+t))) (hF : F∈normalIdeal d t^q) :
    jointBasePullback d e t φ hφ hφ0 F∈normalIdeal e t^q := by
  have hm:=Ideal.mem_map_of_mem (jointBasePullback d e t φ hφ hφ0).toRingHom hF
  rwa [Ideal.map_pow,jointBasePullback_map_normalIdeal d e t φ hφ hφ0] at hm

private theorem jointBaseMap_normalInclusion (d e t : ℕ)
    (φ : ComplexModel e→ComplexModel d) (hφ0 : φ 0=0) (z : ComplexModel t) :
    jointBaseMap d e t φ (actualJointNormalInclusion e t z)=actualJointNormalInclusion d t z := by
  simp only [jointBaseMap,tangentProjection_actualJointNormalInclusion,hφ0,map_zero,
    actualJointNormalProjection_inclusion,zero_add]

/-- SAME actual zero-base fibre trace, without reselecting a fibre ideal. -/
theorem jointBaseZeroTrace_jointBasePullback (d e t : ℕ)
    (φ : ComplexModel e→ComplexModel d)
    (hφ : ∀ᶠ v in 𝓝 (0 : ComplexModel e),DifferentiableAt ℂ φ v) (hφ0 : φ 0=0)
    (F : HolGerm (ComplexModel (d+t))) :
    jointBaseZeroTrace e t (jointBasePullback d e t φ hφ hφ0 F)=jointBaseZeroTrace d t F := by
  induction F using HolGerm.induction_on with
  | h f hf =>
    unfold jointBaseZeroTrace jointBasePullback
    rw [compAlgHom_mk,compAlgHom_mk,compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z=>congrArg f (jointBaseMap_normalInclusion d e t φ hφ0 z)

private theorem normalPolynomialEval_C (d t : ℕ) (a : HolGerm (ComplexModel d)) :
    normalPolynomialEval d t (MvPolynomial.C a)=tangentPullback d t a := by
  let := tangentAlgebra d t
  rw [normalPolynomialEval,MvPolynomial.aeval_C]
  rfl

private theorem normalPolynomialEval_X (d t : ℕ) (i : Fin t) :
    normalPolynomialEval d t (MvPolynomial.X i)=normalCoordinate d t i := by
  simp only [normalPolynomialEval,MvPolynomial.aeval_X]

/-- Actual finite polynomial evaluation commutes with original coefficient pullback. -/
theorem jointBasePullback_normalPolynomialEval (d e t : ℕ)
    (φ : ComplexModel e→ComplexModel d)
    (hφ : ∀ᶠ v in 𝓝 (0 : ComplexModel e),DifferentiableAt ℂ φ v) (hφ0 : φ 0=0)
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) :
    jointBasePullback d e t φ hφ hφ0 (normalPolynomialEval d t P)=
      normalPolynomialEval e t (MvPolynomial.map (compAlgHom φ hφ hφ0).toRingHom P) := by
  let := tangentAlgebra d t
  let := tangentAlgebra e t
  induction P using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.map_C,normalPolynomialEval_C,normalPolynomialEval_C]
    exact jointBasePullback_tangentPullback d e t φ hφ hφ0 a
  | add P Q hP hQ => simp only [map_add,hP,hQ]
  | mul_X P i hP =>
    simp only [map_mul,MvPolynomial.map_X]
    rw [hP]
    congr 1
    rw [normalPolynomialEval_X,normalPolynomialEval_X]
    exact jointBasePullback_normalCoordinate d e t φ hφ hφ0 i

/-- Real finite normal remainder and TRUE new-source uniqueness, EVERY q including0. -/
theorem actualNormalTaylorPolynomial_jointBasePullback (d e t : ℕ)
    (φ : ComplexModel e→ComplexModel d)
    (hφ : ∀ᶠ v in 𝓝 (0 : ComplexModel e),DifferentiableAt ℂ φ v) (hφ0 : φ 0=0)
    (q : ℕ) (F : HolGerm (ComplexModel (d+t))) :
    MvPolynomial.map (compAlgHom φ hφ hφ0).toRingHom (actualNormalTaylorPolynomial d t q F)=
      actualNormalTaylorPolynomial e t q (jointBasePullback d e t φ hφ hφ0 F) := by
  apply actualNormalTaylorPolynomial_unique e t q
    (jointBasePullback d e t φ hφ hφ0 F)
    (MvPolynomial.map (compAlgHom φ hφ hφ0).toRingHom (actualNormalTaylorPolynomial d t q F))
  · intro γ hγ
    rw [MvPolynomial.coeff_map,actualNormalTaylorPolynomial_coefficient_high d t q F γ hγ,map_zero]
  · have hm:=jointBasePullback_mem_normalIdeal_pow d e t φ hφ hφ0 q _
      (actualNormalTaylorPolynomial_remainder d t q F)
    rwa [map_sub,jointBasePullback_normalPolynomialEval] at hm

/-- EVERY original A-valued normal coefficient commutes with true analytic pullback. -/
theorem actualNormalAnalyticCoefficientGerm_jointBasePullback (d e t : ℕ)
    (φ : ComplexModel e→ComplexModel d)
    (hφ : ∀ᶠ v in 𝓝 (0 : ComplexModel e),DifferentiableAt ℂ φ v) (hφ0 : φ 0=0)
    (F : HolGerm (ComplexModel (d+t))) (γ : Fin t→₀ℕ) :
    actualNormalAnalyticCoefficientGerm e t (jointBasePullback d e t φ hφ hφ0 F) γ=
      compAlgHom φ hφ hφ0 (actualNormalAnalyticCoefficientGerm d t F γ) := by
  unfold actualNormalAnalyticCoefficientGerm
  rw [←actualNormalTaylorPolynomial_jointBasePullback d e t φ hφ hφ0
    (normalExponentDegree γ+1) F,MvPolynomial.coeff_map]
  rfl

/-- Any SAME actual normal-support region is preserved under the native base actions. -/
theorem jointBasePullback_mem_normalSupportSubmodule (d e t : ℕ)
    (φ : ComplexModel e→ComplexModel d)
    (hφ : ∀ᶠ v in 𝓝 (0 : ComplexModel e),DifferentiableAt ℂ φ v) (hφ0 : φ 0=0)
    (Δ : Set (Fin t→₀ℕ)) (F : HolGerm (ComplexModel (d+t)))
    (hF : F∈normalSupportSubmodule d t Δ) :
    jointBasePullback d e t φ hφ hφ0 F∈normalSupportSubmodule e t Δ := by
  apply (mem_normalSupportSubmodule_iff e t Δ _).mpr
  intro γ hγ
  rw [actualNormalAnalyticCoefficientGerm_jointBasePullback,
    (mem_normalSupportSubmodule_iff d t Δ F).mp hF γ hγ,map_zero]

end
end Hironaka.HironakaActualAnalyticBaseChangeCoefficients
