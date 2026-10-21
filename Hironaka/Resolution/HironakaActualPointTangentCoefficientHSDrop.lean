/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualPointNormalizedSaturation
import Hironaka.Resolution.HironakaActualCommonMarkPersistentCosupport

/-!
# A literal tangent-cone coefficient forces finite strict point-HS progress

The source minimum is internally the infimum of the actual canonical vertex
degrees. A low pure coefficient of a literal dehomogenized original initial
polynomial forces strict finite-jet HS decrease for the entire normalized ideal
and, in dimension at least two, the entire actual geometric strict ideal.
No initial-diagram inclusion or transformed standardness is presumed.
Blueprint: `hironaka-actual-point-tangent-coefficient-hs-drop-extension.tex`.
-/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualPointTangentCoefficientHSDrop
noncomputable section
open HolGerm HironakaActualOriginalTaylorPolynomial
  HironakaActualOriginalFormalTaylor HironakaActualOriginalReducedVertexBasis
  HironakaActualFormalInitialDiagram HironakaActualReducedFormalStandardBasis
  HironakaActualPointNormalizedSaturation HironakaActualPointDehomogenizedInitial
  HironakaActualPointExceptionalInitialForm HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalIdeal HironakaRelativeNormalActualBaseJetDimension
  HironakaActualAnalyticStrictGenerators HironakaActualAnalyticBlowupTaylor
  HironakaActualCoefficientPresentationCentrePower HironakaActualCommonMarkPersistentCosupport
  HironakaActualPointInitialIdealInclusion HironakaHolomorphicPointJets HironakaHolomorphicJetMonomialSpan
variable {n : ℕ}

private theorem taylor_polynomial (p : MvPolynomial (Fin n) ℂ) :
    originalTaylorAlgHom n (originalPolynomialEval n p)=(p : MvPowerSeries (Fin n) ℂ) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      rw [originalPolynomialEval,MvPolynomial.aeval_C,MvPolynomial.coe_C]
      exact (originalTaylorAlgHom n).commutes c
  | add p q hp hq => simpa only [map_add,MvPolynomial.coe_add] using congrArg₂ (·+·) hp hq
  | mul_X p i hp =>
      simp only [map_mul,MvPolynomial.coe_mul,hp]
      rw [show originalPolynomialEval n (MvPolynomial.X i)=normalCoordinate 0 n i from MvPolynomial.aeval_X _ i,
        originalTaylorAlgHom_coordinate,MvPolynomial.coe_X]

private theorem canonical_point_power
    (J : Ideal (HolGerm (ComplexModel (0+n))))
    (a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n)) (Ideal.map (originalTaylorAlgHom n).toRingHom J)) :
    originalReducedVertexBasis J a∈normalIdeal 0 n^(normalExponentDegree a.val) := by
  rw [zeroTangentNormalIdeal_eq_maximalIdeal]
  apply (mem_original_maximal_pow_iff_formal_coefficients_zero n _ _).mpr
  intro α hα
  rw [originalReducedVertexBasis_taylor]
  apply actualReducedVertexSeries_coefficient_lower MonomialOrder.degLex _ a α
  apply MonomialOrder.degLex_lt_iff.mpr
  apply Finsupp.DegLex.lt_iff.mpr
  left
  simpa only [ofDegLex_toDegLex,Finsupp.degree_eq_sum,normalExponentDegree] using hα

/-- Every pure coefficient of the SAME canonical quotient is its literal
source homogeneous-polynomial dehomogenization coefficient. -/
theorem canonical_point_quotient_pure_coefficient
    (J : Ideal (HolGerm (ComplexModel (0+n))))
    (a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n)) (Ideal.map (originalTaylorAlgHom n).toRingHom J))
    (j : Fin n) (b : Fin (0+n) → ℂ) (H : HolGerm (ComplexModel (0+n)))
    (hH : (coordinateGerm (j.natAdd 0))^(normalExponentDegree a.val)*H=
      actualAnalyticBlowupPullback (actualTangentCentreVariables 0 n) (j.natAdd 0) b (originalReducedVertexBasis J a))
    (γ : Fin n →₀ ℕ) (hγ : γ j=0) :
    MvPowerSeries.coeff γ (originalTaylorAlgHom n H)=
      MvPolynomial.coeff γ (actualPointDehomogenization j (fun i => b (i.natAdd 0))
        (actualPointHomogeneousPolynomial (normalExponentDegree a.val)
          (originalTaylorAlgHom n (originalReducedVertexBasis J a)))) := by
  let p := actualPointDehomogenization j (fun i => b (i.natAdd 0))
    (actualPointHomogeneousPolynomial (normalExponentDegree a.val)
      (originalTaylorAlgHom n (originalReducedVertexBasis J a)))
  have hcong := canonical_point_quotient_initial_congruence J a j b H hH
  change H-originalPolynomialEval n p∈Ideal.span {coordinateGerm (j.natAdd 0)} at hcong
  obtain ⟨K,hK⟩ := Ideal.mem_span_singleton.mp hcong
  have hdiv : (MvPowerSeries.X j : MvPowerSeries (Fin n) ℂ)^1 ∣
      originalTaylorAlgHom n H-(p : MvPowerSeries (Fin n) ℂ) := by
    refine ⟨originalTaylorAlgHom n K,?_⟩
    rw [pow_one,←taylor_polynomial p,←map_sub,hK,map_mul]
    change originalTaylorAlgHom n (normalCoordinate 0 n j)*_= _
    rw [originalTaylorAlgHom_coordinate]
  have hz := MvPowerSeries.X_pow_dvd_iff.mp hdiv γ (by omega)
  rw [map_sub,MvPolynomial.coeff_coe,sub_eq_zero] at hz
  exact hz

private theorem canonical_span_le_point_power
    (J : Ideal (HolGerm (ComplexModel (0+n)))) (q : ℕ)
    (hdeg : ∀ a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
      (Ideal.map (originalTaylorAlgHom n).toRingHom J), q≤normalExponentDegree a.val) :
    J≤IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n)))^q := by
  rw [←originalReducedVertexBasis_span J]
  apply Ideal.span_le.mpr
  rintro _ ⟨a,rfl⟩
  have h := canonical_point_power J a
  rw [zeroTangentNormalIdeal_eq_maximalIdeal] at h
  exact Ideal.pow_le_pow_right (hdeg a) h

/-- A computable low dehomogenized coefficient below the INTERNALLY measured
source minimum forces strict progress of the ENTIRE actual normalized ideal. -/
theorem hilbertSamuelValue_point_normalized_lt_of_low_dehom_coefficient
    (J : Ideal (HolGerm (ComplexModel (0+n))))
    (a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n)) (Ideal.map (originalTaylorAlgHom n).toRingHom J))
    (j : Fin n) (b : Fin (0+n) → ℂ) (γ : Fin n →₀ ℕ) (hγ : γ j=0)
    (hdeg : normalExponentDegree γ < sInf (range (fun c : actualInitialVertices
      (MonomialOrder.degLex (σ := Fin n)) (Ideal.map (originalTaylorAlgHom n).toRingHom J) => normalExponentDegree c.val)))
    (hc : MvPolynomial.coeff γ (actualPointDehomogenization j (fun i => b (i.natAdd 0))
      (actualPointHomogeneousPolynomial (normalExponentDegree a.val)
        (originalTaylorAlgHom n (originalReducedVertexBasis J a))))≠0) :
    hilbertSamuelValue
      (actualAnalyticNormalizedMemberIdeal J (actualTangentCentreVariables 0 n) (j.natAdd 0) b)
      (normalExponentDegree γ) < hilbertSamuelValue J (normalExponentDegree γ) := by
  let r := normalExponentDegree γ
  let N := actualAnalyticNormalizedMemberIdeal J (actualTangentCentreVariables 0 n) (j.natAdd 0) b
  have hJ : J≤IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n)))^(r+1) := by
    apply canonical_span_le_point_power
    intro c
    have hmin : sInf (range (fun c : actualInitialVertices
        (MonomialOrder.degLex (σ := Fin n)) (Ideal.map (originalTaylorAlgHom n).toRingHom J) => normalExponentDegree c.val))≤normalExponentDegree c.val :=
      csInf_le' ⟨c,rfl⟩
    dsimp only [r]
    omega
  have hJHS := (le_maximal_pow_iff_hilbertSamuelValue_eq_bot J r).mp hJ
  obtain ⟨H,hH,_hreg⟩ := exists_original_point_exceptional_regular_canonical_family J j b
  have hHa : H a∈N := by
    apply Ideal.subset_span
    refine ⟨normalExponentDegree a.val,originalReducedVertexBasis J a,
      originalReducedVertexBasis_mem J a,?_,hH a⟩
    rw [actualAnalyticCoordinateIdeal_normal]
    exact canonical_point_power J a
  have hN : ¬ N≤IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n)))^(r+1) := by
    intro h
    have hz := (mem_original_maximal_pow_iff_formal_coefficients_zero n (r+1) (H a)).mp (h hHa) γ (by omega)
    rw [canonical_point_quotient_pure_coefficient J a j b (H a) (hH a) γ hγ] at hz
    exact hc hz
  have hne : hilbertSamuelValue N r≠hilbertSamuelValue (⊥ : Ideal (HolGerm (ComplexModel (0+n)))) r :=
    fun h => hN ((le_maximal_pow_iff_hilbertSamuelValue_eq_bot N r).mpr h)
  have hle : hilbertSamuelValue N r≤hilbertSamuelValue (⊥ : Ideal (HolGerm (ComplexModel (0+n)))) r :=
    hilbertSamuelValue_antitone_original_ideal _ _ bot_le r
  change hilbertSamuelValue N r<hilbertSamuelValue J r
  rw [hJHS]
  exact lt_of_le_of_ne hle hne


open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaRelativeNormalDeformationInitialRelations

/-- The original source coefficient witness gives strict progress of the
WHOLE independently defined geometric strict ideal, for the SAME actual map. -/
theorem hilbertSamuelValue_geometric_strict_lt_of_low_dehom_coefficient
    (hn : 2≤n) (j : Fin n) (b : Fin (0+n) → ℂ)
    (W : Set (ComplexModel (0+n))) (hW : IsComplexAnalyticSubset (n := 0+n) W) :
    let J := originalCoherentOriginIdeal (vanishingIdeal (n := 0+n) W)
    ∀ (a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
        (Ideal.map (originalTaylorAlgHom n).toRingHom J))
      (γ : Fin n →₀ ℕ) (_hγ : γ j=0)
      (_hdeg : normalExponentDegree γ < sInf (range (fun c : actualInitialVertices
        (MonomialOrder.degLex (σ := Fin n)) (Ideal.map (originalTaylorAlgHom n).toRingHom J) => normalExponentDegree c.val))),
      MvPolynomial.coeff γ (actualPointDehomogenization j (fun i => b (i.natAdd 0))
        (actualPointHomogeneousPolynomial (normalExponentDegree a.val)
          (originalTaylorAlgHom n (originalReducedVertexBasis J a))))≠0 →
      hilbertSamuelValue (originalCoherentOriginIdeal (vanishingIdeal (n := 0+n)
        (strictTransform (0+n) (actualAnalyticBlowupMap (actualTangentCentreVariables 0 n) (j.natAdd 0) b) W)))
        (normalExponentDegree γ) < hilbertSamuelValue J (normalExponentDegree γ) := by
  dsimp only
  intro a γ hγ hdeg hc
  rw [←actual_point_normalized_eq_geometric_strict hn j b W hW]
  exact hilbertSamuelValue_point_normalized_lt_of_low_dehom_coefficient _ a j b γ hγ hdeg hc

/-- Actual entire point-HS persistence kills EVERY literal pure dehomogenized
coefficient below the internally measured source minimum. -/
theorem dehom_coefficient_eq_zero_of_entire_point_hs_persistence
    (J : Ideal (HolGerm (ComplexModel (0+n)))) (j : Fin n) (b : Fin (0+n) → ℂ)
    (hHS : ∀ ℓ, hilbertSamuelValue
      (actualAnalyticNormalizedMemberIdeal J (actualTangentCentreVariables 0 n) (j.natAdd 0) b) ℓ=
        hilbertSamuelValue J ℓ)
    (a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
      (Ideal.map (originalTaylorAlgHom n).toRingHom J))
    (γ : Fin n →₀ ℕ) (hγ : γ j=0)
    (hdeg : normalExponentDegree γ < sInf (range (fun c : actualInitialVertices
      (MonomialOrder.degLex (σ := Fin n)) (Ideal.map (originalTaylorAlgHom n).toRingHom J) => normalExponentDegree c.val))) :
    MvPolynomial.coeff γ (actualPointDehomogenization j (fun i => b (i.natAdd 0))
      (actualPointHomogeneousPolynomial (normalExponentDegree a.val)
        (originalTaylorAlgHom n (originalReducedVertexBasis J a))))=0 := by
  by_contra hc
  have hlt := hilbertSamuelValue_point_normalized_lt_of_low_dehom_coefficient J a j b γ hγ hdeg hc
  rw [hHS (normalExponentDegree γ)] at hlt
  exact lt_irrefl _ hlt

end
end Hironaka.HironakaActualPointTangentCoefficientHSDrop
