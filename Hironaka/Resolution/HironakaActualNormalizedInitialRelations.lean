/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualOwnerAnalyticDivision
import Hironaka.Resolution.HironakaActualNormalAxisDehomogenization

/-!
# Whole analytic lifts of canonical initial relations in actual point charts

For one original ideal the canonical analytic family has one actual normalized
family fixed before every homogeneous initial relation. Genuine source analytic
syzygy lifting and actual exceptional division give whole normalized relations.
For literal homogeneous polynomial coefficients the lifted coefficients equal
exactly their actual chart dehomogenizations plus an exceptional multiple.
No target relation, convergence, exceptional regularity or saturation certificate
is supplied. Completion/generation of arbitrary exceptional-fibre relations and
normalized-ideal saturation remain separate.

Blueprint: `hironaka-actual-normalized-initial-relations-extension.tex`.
-/
set_option autoImplicit false
open Set Classical
open scoped BigOperators
namespace Hironaka.HironakaActualNormalizedInitialRelations
noncomputable section
open HolGerm HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalActualBaseJetDimension HironakaHolomorphicJetMonomialSpan
  HironakaActualFormalInitialDiagram HironakaActualOriginalFormalTaylor
  HironakaActualOriginalReducedVertexBasis HironakaActualOwnerAnalyticDivision
  HironakaActualCoefficientPresentationCentrePower HironakaActualAnalyticBlowupTaylor
  HironakaActualNormalHomogeneousComponents HironakaActualNormalQuotientExceptionalRestriction
  HironakaActualReducedFormalStandardBasis HironakaActualNormalAxisDehomogenization
  HironakaActualOriginalTaylorPolynomial
variable {n : ℕ}

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- Actual point powers, genuine exceptional quotients and analytic-domain cancellation transport a whole weighted source syzygy. -/
theorem exists_actual_normalized_syzygy {ι : Type*} [Fintype ι]
    (G C H : ι → HolGerm (ComplexModel (0+n))) (d : ι → ℕ) (D : ℕ)
    (hd : ∀ a,d a≤D)
    (hC : ∀ a,C a∈normalIdeal 0 n^(D-d a))
    (hRel : (∑ a,G a*C a)=0)
    (j : Fin n) (b : Fin (0+n) → ℂ)
    (hH : ∀ a,(coordinateGerm (j.natAdd 0))^(d a)*H a=
      actualAnalyticBlowupPullback (actualTangentCentreVariables 0 n) (j.natAdd 0) b (G a)) :
    ∃ L : ι → HolGerm (ComplexModel (0+n)),
      (∀ a,(coordinateGerm (j.natAdd 0))^(D-d a)*L a=
        actualAnalyticBlowupPullback (actualTangentCentreVariables 0 n) (j.natAdd 0) b (C a)) ∧
      (∑ a,H a*L a)=0 := by
  have hq (a : ι) := exists_actualAnalyticBlowup_quotient (actualTangentCentreVariables 0 n)
    (j.natAdd 0) (show j.natAdd 0∈actualTangentCentreVariables 0 n from ⟨j,rfl⟩) b (D-d a) (C a)
    (by rw [actualAnalyticCoordinateIdeal_normal];exact hC a)
  choose L hL using hq
  refine ⟨L,fun a => (hL a).1,?_⟩
  have he0 : (coordinateGerm (j.natAdd 0) : HolGerm (ComplexModel (0+n)))≠0 :=
    HolomorphicGermReducednessBridge.coordinate_germ_ne_zero (j.natAdd 0)
  apply mul_left_cancel₀ (pow_ne_zero D he0)
  rw [mul_zero,Finset.mul_sum]
  calc
    _=(∑ a,actualAnalyticBlowupPullback (actualTangentCentreVariables 0 n) (j.natAdd 0) b (G a*C a)) := by
      apply Finset.sum_congr rfl
      intro a _
      have hdeg : d a+(D-d a)=D := Nat.add_sub_of_le (hd a)
      calc
        _=(coordinateGerm (j.natAdd 0))^(d a+(D-d a))*(H a*L a) := by rw [hdeg]
        _=((coordinateGerm (j.natAdd 0))^(d a)*H a)*
            ((coordinateGerm (j.natAdd 0))^(D-d a)*L a) := by rw [pow_add];ring
        _=_ := by rw [hH a,(hL a).1,map_mul]
    _=0 := by rw [←map_sum,hRel,map_zero]



attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- One actual normalized canonical family, fixed before EVERY genuine homogeneous initial relation, admits whole analytic target relation lifts with their literal polynomial exceptional restrictions. -/
theorem exists_original_point_normalized_initial_relation_lifts
    (J : Ideal (HolGerm (ComplexModel (0+n)))) (j : Fin n) (b : Fin (0+n) → ℂ) :
    ∃ H : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
        (Ideal.map (originalTaylorAlgHom n).toRingHom J) → HolGerm (ComplexModel (0+n)),
      (∀ a,(coordinateGerm (j.natAdd 0))^(normalExponentDegree a.val)*H a=
        actualAnalyticBlowupPullback (actualTangentCentreVariables 0 n) (j.natAdd 0) b
          (originalReducedVertexBasis J a)) ∧
      ∀ (D : ℕ) (P : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
          (Ideal.map (originalTaylorAlgHom n).toRingHom J) → HolGerm (ComplexModel (0+n))),
        (∀ a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
          (Ideal.map (originalTaylorAlgHom n).toRingHom J),normalExponentDegree a.val≤D) →
        (∀ a,(originalTaylorAlgHom n (P a)).IsHomogeneous (D-normalExponentDegree a.val)) →
        (∑ a,originalTaylorAlgHom n (P a)*MvPowerSeries.homogeneousComponent (normalExponentDegree a.val)
          (originalTaylorAlgHom n (originalReducedVertexBasis J a)))=0 →
        ∃ L V R : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
            (Ideal.map (originalTaylorAlgHom n).toRingHom J) → HolGerm (ComplexModel (0+n)),
          (∑ a,H a*L a)=0 ∧
          (∀ a,(coordinateGerm (j.natAdd 0))^(D-normalExponentDegree a.val)*V a=
            actualAnalyticBlowupPullback (actualTangentCentreVariables 0 n) (j.natAdd 0) b (P a)) ∧
          (∀ a,L a=V a+coordinateGerm (j.natAdd 0)*R a) ∧
          ∀ a,L a-actualDehomogenizedNormalPolynomialEval 0 n j b
            (actualNormalHomogeneousPolynomial 0 n (D-normalExponentDegree a.val) (P a)) ∈
              Ideal.span {coordinateGerm (j.natAdd 0)} := by
  have hG (a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
      (Ideal.map (originalTaylorAlgHom n).toRingHom J)) :
      originalReducedVertexBasis J a∈normalIdeal 0 n^(normalExponentDegree a.val) := by
    rw [zeroTangentNormalIdeal_eq_maximalIdeal]
    apply (mem_original_maximal_pow_iff_formal_coefficients_zero n _ _).mpr
    intro β hβ
    rw [originalReducedVertexBasis_taylor]
    apply actualReducedVertexSeries_coefficient_lower MonomialOrder.degLex _ a β
    apply MonomialOrder.degLex_lt_iff.mpr
    apply Finsupp.DegLex.lt_iff.mpr
    left
    simpa only [ofDegLex_toDegLex,Finsupp.degree_eq_sum,normalExponentDegree] using hβ
  have hq (a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
      (Ideal.map (originalTaylorAlgHom n).toRingHom J)) :=
    exists_actualAnalyticBlowup_quotient (actualTangentCentreVariables 0 n) (j.natAdd 0)
      (show j.natAdd 0∈actualTangentCentreVariables 0 n from ⟨j,rfl⟩) b
      (normalExponentDegree a.val) (originalReducedVertexBasis J a)
      (by rw [actualAnalyticCoordinateIdeal_normal];exact hG a)
  choose H hH using hq
  refine ⟨H,fun a => (hH a).1,?_⟩
  intro D P hD hP hRel
  obtain ⟨C,hC,hInitial,hCorr⟩ := exists_original_initial_syzygy_lift J P D hD hP hRel
  have hPa (a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
      (Ideal.map (originalTaylorAlgHom n).toRingHom J)) :
      P a∈normalIdeal 0 n^(D-normalExponentDegree a.val) := by
    rw [zeroTangentNormalIdeal_eq_maximalIdeal]
    apply (mem_original_maximal_pow_iff_formal_coefficients_zero n _ _).mpr
    intro β hβ
    apply MvPowerSeries.IsHomogeneous.coeff_eq_zero (hP a)
    simpa only [Finsupp.degree_eq_sum,normalExponentDegree] using Nat.ne_of_lt hβ
  have hCorr' (a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
      (Ideal.map (originalTaylorAlgHom n).toRingHom J)) :
      P a-C a∈normalIdeal 0 n^((D-normalExponentDegree a.val)+1) := by
    rw [zeroTangentNormalIdeal_eq_maximalIdeal]
    have he : D+1-normalExponentDegree a.val=(D-normalExponentDegree a.val)+1 := by have := hD a;omega
    rw [←he]
    exact hCorr a
  have hCa (a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
      (Ideal.map (originalTaylorAlgHom n).toRingHom J)) :
      C a∈normalIdeal 0 n^(D-normalExponentDegree a.val) := by
    have hc := Ideal.pow_le_pow_right (Nat.le_succ (D-normalExponentDegree a.val)) (hCorr' a)
    convert (normalIdeal 0 n^(D-normalExponentDegree a.val)).sub_mem (hPa a) hc using 1
    ring
  obtain ⟨L,hL,hLRel⟩ := exists_actual_normalized_syzygy (originalReducedVertexBasis J) C H
    (fun a => normalExponentDegree a.val) D hD hCa hC j b (fun a => (hH a).1)
  have hVq (a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
      (Ideal.map (originalTaylorAlgHom n).toRingHom J)) :=
    exists_actualAnalyticBlowup_quotient (actualTangentCentreVariables 0 n) (j.natAdd 0)
      (show j.natAdd 0∈actualTangentCentreVariables 0 n from ⟨j,rfl⟩) b
      (D-normalExponentDegree a.val) (P a) (by rw [actualAnalyticCoordinateIdeal_normal];exact hPa a)
  choose V hV using hVq
  have hRq (a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
      (Ideal.map (originalTaylorAlgHom n).toRingHom J)) :=
    exists_actualAnalyticBlowup_quotient (actualTangentCentreVariables 0 n) (j.natAdd 0)
      (show j.natAdd 0∈actualTangentCentreVariables 0 n from ⟨j,rfl⟩) b
      ((D-normalExponentDegree a.val)+1) (C a-P a)
      (by rw [actualAnalyticCoordinateIdeal_normal];simpa only [neg_sub] using (normalIdeal 0 n^_).neg_mem (hCorr' a))
  choose R hR using hRq
  have he0 : (coordinateGerm (j.natAdd 0) : HolGerm (ComplexModel (0+n)))≠0 :=
    HolomorphicGermReducednessBridge.coordinate_germ_ne_zero (j.natAdd 0)
  have hLV (a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
      (Ideal.map (originalTaylorAlgHom n).toRingHom J)) : L a=V a+coordinateGerm (j.natAdd 0)*R a := by
    apply mul_left_cancel₀ (pow_ne_zero (D-normalExponentDegree a.val) he0)
    rw [mul_add,hL a,(hV a).1,←mul_assoc,←pow_succ,(hR a).1,map_sub]
    ring
  refine ⟨L,V,R,hLRel,fun a => (hV a).1,hLV,?_⟩
  intro a
  have hv := actual_analytic_normal_quotient_initial_restriction 0 n j b
    (D-normalExponentDegree a.val) (P a) (V a) (hPa a) (hV a).1
  change V a-actualDehomogenizedNormalPolynomialEval 0 n j b
    (actualNormalHomogeneousPolynomial 0 n (D-normalExponentDegree a.val) (P a))∈_ at hv
  rw [hLV a]
  have heR : coordinateGerm (j.natAdd 0)*R a∈Ideal.span {coordinateGerm (j.natAdd 0)} :=
    Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self (coordinateGerm (j.natAdd 0)))
  convert (Ideal.span {coordinateGerm (j.natAdd 0)}).add_mem hv heR using 1
  ring



private theorem originalTaylor_polynomial (p : MvPolynomial (Fin n) ℂ) :
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

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- EVERY literal homogeneous polynomial initial relation lifts to a whole analytic relation of the SAME prechosen normalized family, with exact polynomial dehomogenization plus an exceptional multiple. -/
theorem exists_original_point_polynomial_relation_lifts
    (J : Ideal (HolGerm (ComplexModel (0+n)))) (j : Fin n) (b : Fin (0+n) → ℂ) :
    ∃ H : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
        (Ideal.map (originalTaylorAlgHom n).toRingHom J) → HolGerm (ComplexModel (0+n)),
      (∀ a,(coordinateGerm (j.natAdd 0))^(normalExponentDegree a.val)*H a=
        actualAnalyticBlowupPullback (actualTangentCentreVariables 0 n) (j.natAdd 0) b
          (originalReducedVertexBasis J a)) ∧
      ∀ (D : ℕ) (p : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
          (Ideal.map (originalTaylorAlgHom n).toRingHom J) → MvPolynomial (Fin n) ℂ),
        (∀ a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
          (Ideal.map (originalTaylorAlgHom n).toRingHom J),normalExponentDegree a.val≤D) →
        (∀ a,(p a).IsHomogeneous (D-normalExponentDegree a.val)) →
        (∑ a,(p a : MvPowerSeries (Fin n) ℂ)*MvPowerSeries.homogeneousComponent (normalExponentDegree a.val)
          (originalTaylorAlgHom n (originalReducedVertexBasis J a)))=0 →
        ∃ L R : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
            (Ideal.map (originalTaylorAlgHom n).toRingHom J) → HolGerm (ComplexModel (0+n)),
          (∑ a,H a*L a)=0 ∧
          ∀ a,L a=actualDehomogenizedNormalPolynomialEval 0 n j b
            ((p a).map (HolGerm.constHom : ℂ →+* HolGerm (ComplexModel 0)))+
              coordinateGerm (j.natAdd 0)*R a := by
  obtain ⟨H,hH,hLift⟩ := exists_original_point_normalized_initial_relation_lifts J j b
  refine ⟨H,hH,?_⟩
  intro D p hD hp hRel
  let P := fun a => originalPolynomialEval n (p a)
  have hPT (a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
      (Ideal.map (originalTaylorAlgHom n).toRingHom J)) :
      originalTaylorAlgHom n (P a)=(p a : MvPowerSeries (Fin n) ℂ) := originalTaylor_polynomial (p a)
  have hP (a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
      (Ideal.map (originalTaylorAlgHom n).toRingHom J)) :
      (originalTaylorAlgHom n (P a)).IsHomogeneous (D-normalExponentDegree a.val) := by
    rw [hPT]
    intro α hα
    apply hp a
    simpa only [MvPolynomial.coeff_coe] using hα
  have hRel' : (∑ a,originalTaylorAlgHom n (P a)*MvPowerSeries.homogeneousComponent (normalExponentDegree a.val)
      (originalTaylorAlgHom n (originalReducedVertexBasis J a)))=0 := by
    simpa only [hPT] using hRel
  obtain ⟨L,V,R,hL,hV,hLV,_hRestriction⟩ := hLift D P hD hP hRel'
  have hVPoly (a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
      (Ideal.map (originalTaylorAlgHom n).toRingHom J)) :
      V a=actualDehomogenizedNormalPolynomialEval 0 n j b
        ((p a).map (HolGerm.constHom : ℂ →+* HolGerm (ComplexModel 0))) := by
    have hmap : ((p a).map (HolGerm.constHom : ℂ →+* HolGerm (ComplexModel 0))).IsHomogeneous
        (D-normalExponentDegree a.val) := by
      intro α hα
      apply hp a
      intro hz
      apply hα
      rw [MvPolynomial.coeff_map,hz,map_zero]
    have hfactor := actualAnalyticBlowupPullback_normalPolynomial_homogeneous 0 n j b
      ((p a).map (HolGerm.constHom : ℂ →+* HolGerm (ComplexModel 0)))
      (D-normalExponentDegree a.val) hmap
    rw [normalPolynomialEval_original_coefficient_lift] at hfactor
    have he0 : (coordinateGerm (j.natAdd 0) : HolGerm (ComplexModel (0+n)))≠0 :=
      HolomorphicGermReducednessBridge.coordinate_germ_ne_zero (j.natAdd 0)
    apply mul_left_cancel₀ (pow_ne_zero (D-normalExponentDegree a.val) he0)
    exact (hV a).trans hfactor
  exact ⟨L,R,hL,fun a => (hLV a).trans (congrArg (fun v => v+coordinateGerm (j.natAdd 0)*R a) (hVPoly a))⟩

end
end Hironaka.HironakaActualNormalizedInitialRelations
