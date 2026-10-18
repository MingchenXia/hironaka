/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualNormalHomogeneousComponents
import Hironaka.Resolution.HironakaActualAnalyticBlowupTaylor
import Hironaka.Analytic.HolomorphicGermReducednessBridge
import Hironaka.Analytic.HolomorphicZeroSetThin

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualNormalQuotientExceptionalRestriction
noncomputable section
open HolGerm HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalAssociatedGraded HironakaActualRelativeCoefficientGerms
  HironakaActualNormalHomogeneousComponents HironakaActualCoefficientPresentationCentrePower
  HironakaActualAnalyticBlowupTaylor HironakaHolomorphicJetChartInvariance
  HironakaHolomorphicJetMonomialSpan

/-- True low/high coefficient separation forces the SAME actual truncation to be homogeneous. -/
theorem actualNormalTaylorPolynomial_isHomogeneous_of_mem_normal_pow (d t q : ℕ)
    (g : HolGerm (ComplexModel (d+t))) (hg : g ∈ normalIdeal d t ^ q) :
    (actualNormalTaylorPolynomial d t (q+1) g).IsHomogeneous q := by
  have hr := actualNormalTaylorPolynomial_remainder d t (q+1) g
  have hrq := Ideal.pow_le_pow_right (Nat.le_succ q) hr
  have heval : normalPolynomialEval d t (actualNormalTaylorPolynomial d t (q+1) g) ∈
      normalIdeal d t ^ q := by
    convert (normalIdeal d t ^ q).sub_mem hg hrq using 1
    ring
  intro α hα
  have hd : normalExponentDegree α=q := by
    by_contra hne
    by_cases hlo : normalExponentDegree α < q
    · exact hα (coefficient_eq_zero_of_normalPolynomialEval_mem d t q _ α hlo heval)
    · exact hα (actualNormalTaylorPolynomial_coefficient_high d t (q+1) g α (by omega))
  change Finsupp.weight (1 : Fin t → ℕ) α=q
  simp only [Pi.one_def]
  rw [← Finsupp.degree_eq_weight_one]
  exact (normalExponentDegree_eq_degree t α).symm.trans hd

/-- The root-owned actual canonical component is this SAME genuine original truncation under normal-power membership. -/
theorem actualNormalHomogeneousPolynomial_eq_truncation_of_mem_normal_pow (d t q : ℕ)
    (g : HolGerm (ComplexModel (d+t))) (hg : g ∈ normalIdeal d t ^ q) :
    actualNormalHomogeneousPolynomial d t q g=actualNormalTaylorPolynomial d t (q+1) g :=
  MvPolynomial.homogeneousComponent_eq_self
    (actualNormalTaylorPolynomial_isHomogeneous_of_mem_normal_pow d t q g hg)

/-- The canonical ACTUAL normal component has the true entire next-power remainder. -/
theorem actual_normal_homogeneousComponent_remainder (d t q : ℕ)
    (g : HolGerm (ComplexModel (d+t))) (hg : g ∈ normalIdeal d t ^ q) :
    g-normalPolynomialEval d t (actualNormalHomogeneousPolynomial d t q g) ∈ normalIdeal d t ^ (q+1) := by
  rw [actualNormalHomogeneousPolynomial_eq_truncation_of_mem_normal_pow d t q g hg]
  exact actualNormalTaylorPolynomial_remainder d t (q+1) g

/-- The actual blowup, independently of the unit coordinate map, fixes EVERY genuine tangent germ. -/
theorem actualAnalyticBlowupPullback_tangentPullback (d t : ℕ) (j : Fin t)
    (b : Fin (d+t) → ℂ) (a : HolGerm (ComplexModel d)) :
    actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b
        (tangentPullback d t a)=tangentPullback d t a := by
  induction a using HolGerm.induction_on with
  | h f hf =>
    unfold tangentPullback actualAnalyticBlowupPullback
    rw [compAlgHom_mk,compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    apply Eventually.of_forall
    intro z
    apply congrArg f
    ext i
    have hiA : i.castAdd t ∉ actualTangentCentreVariables d t := by
      rintro ⟨k,hk⟩
      have hv := congrArg Fin.val hk
      simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
      omega
    simp [tangentProjection_apply,actualAnalyticBlowupMap_apply,actualAnalyticBlowupCoordinate,hiA]

/-- True finite normal-homogeneous factorization keeps EVERY original analytic tangent coefficient. -/
theorem actualAnalyticBlowupPullback_normalPolynomial_homogeneous (d t : ℕ) (j : Fin t)
    (b : Fin (d+t) → ℂ) (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d)))
    (q : ℕ) (hP : P.IsHomogeneous q) :
    actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b
        (normalPolynomialEval d t P)=
      (coordinateGerm (j.natAdd d))^q*
        MvPolynomial.eval₂ (tangentPullback d t).toRingHom
          (fun i => if i=j then 1 else
            (algebraMap ℂ (HolGerm (ComplexModel (d+t)))) (b (i.natAdd d))+normalCoordinate d t i) P := by
  let B := actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b
  change B.toRingHom (MvPolynomial.eval₂Hom (tangentPullback d t).toRingHom
    (normalCoordinate d t) P)=_
  rw [MvPolynomial.map_eval₂Hom]
  have hcoef : B.toRingHom.comp (tangentPullback d t).toRingHom=(tangentPullback d t).toRingHom := by
    apply RingHom.ext
    intro a
    exact actualAnalyticBlowupPullback_tangentPullback d t j b a
  rw [hcoef]
  have hx : (fun i => B.toRingHom (normalCoordinate d t i))=
      (fun i => coordinateGerm (j.natAdd d)*(if i=j then 1 else
        (algebraMap ℂ (HolGerm (ComplexModel (d+t)))) (b (i.natAdd d))+normalCoordinate d t i)) := by
    funext i
    have hiA : i.natAdd d ∈ actualTangentCentreVariables d t := ⟨i,rfl⟩
    change actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b
      (coordinateGerm (i.natAdd d))=_
    rw [actualAnalyticBlowupPullback_coordinate,if_pos hiA]
    by_cases hi : i=j
    · subst i
      simp
    · have hie : i.natAdd d ≠ j.natAdd d := by
        intro h
        apply hi
        apply Fin.ext
        have hv := congrArg Fin.val h
        simp only [Fin.val_natAdd] at hv
        omega
      simp only [if_neg hie,if_neg hi,normalCoordinate]
      rfl
  rw [hx]
  change MvPolynomial.eval₂Hom _ _ P=(coordinateGerm (j.natAdd d))^q*MvPolynomial.eval₂Hom _ _ P
  rw [← P.support_sum_monomial_coeff,map_sum,map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α hα
  simp only [MvPolynomial.eval₂Hom_monomial,Finsupp.prod,mul_pow,
    Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
  rw [← hP.degree_eq_sum_deg_support hα]
  ac_rfl

/-- The canonical whole analytic normal exceptional restriction follows from the TRUE original product. -/
theorem actual_analytic_normal_quotient_initial_restriction (d t : ℕ) (j : Fin t)
    (b : Fin (d+t) → ℂ) (q : ℕ) (g H : HolGerm (ComplexModel (d+t)))
    (hg : g ∈ normalIdeal d t ^ q)
    (hH : (coordinateGerm (j.natAdd d))^q*H=
      actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b g) :
    H-MvPolynomial.eval₂ (tangentPullback d t).toRingHom
      (fun i => if i=j then 1 else
        (algebraMap ℂ (HolGerm (ComplexModel (d+t)))) (b (i.natAdd d))+normalCoordinate d t i)
      (actualNormalHomogeneousPolynomial d t q g) ∈ Ideal.span {coordinateGerm (j.natAdd d)} := by
  let P := actualNormalHomogeneousPolynomial d t q g
  let D := MvPolynomial.eval₂ (tangentPullback d t).toRingHom
    (fun i => if i=j then 1 else
      (algebraMap ℂ (HolGerm (ComplexModel (d+t)))) (b (i.natAdd d))+normalCoordinate d t i) P
  let B := actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b
  have hr := actual_normal_homogeneousComponent_remainder d t q g hg
  rw [← actualAnalyticCoordinateIdeal_normal d t] at hr
  have hm := Ideal.mem_map_of_mem B.toRingHom hr
  rw [map_actualAnalyticCoordinateIdeal_pow_blowup (actualTangentCentreVariables d t)
    (j.natAdd d) (show j.natAdd d ∈ actualTangentCentreVariables d t from ⟨j,rfl⟩) b (q+1)] at hm
  obtain ⟨K,hK⟩ := Ideal.mem_span_singleton'.mp hm
  have hfactor : B (normalPolynomialEval d t P)=(coordinateGerm (j.natAdd d))^q*D :=
    actualAnalyticBlowupPullback_normalPolynomial_homogeneous d t j b P q
      (actualNormalHomogeneousPolynomial_isHomogeneous d t q g)
  have hproduct : (coordinateGerm (j.natAdd d))^q*(H-D)=
      (coordinateGerm (j.natAdd d))^q*(coordinateGerm (j.natAdd d)*K) := by
    calc
      _ = B (g-normalPolynomialEval d t P) := by rw [map_sub,← hH,hfactor]; ring
      _ = K*(coordinateGerm (j.natAdd d))^(q+1) := hK.symm
      _ = _ := by rw [pow_succ]; ring
  have he0 : (coordinateGerm (j.natAdd d) : HolGerm (ComplexModel (d+t))) ≠ 0 :=
    HolomorphicGermReducednessBridge.coordinate_germ_ne_zero (j.natAdd d)
  have heq : H-D=coordinateGerm (j.natAdd d)*K := mul_left_cancel₀ (pow_ne_zero _ he0) hproduct
  change H-D ∈ _
  rw [heq]
  exact Ideal.mem_span_singleton'.mpr ⟨K,mul_comm K _⟩

/-- ONLY original normal-power membership internally supplies the genuine quotient and canonical restriction. -/
theorem exists_actual_analytic_normal_initial_quotient (d t : ℕ) (j : Fin t)
    (b : Fin (d+t) → ℂ) (q : ℕ) (g : HolGerm (ComplexModel (d+t)))
    (hg : g ∈ normalIdeal d t ^ q) :
    ∃ H : HolGerm (ComplexModel (d+t)),
      (coordinateGerm (j.natAdd d))^q*H=
        actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b g ∧
      H-MvPolynomial.eval₂ (tangentPullback d t).toRingHom
        (fun i => if i=j then 1 else
          (algebraMap ℂ (HolGerm (ComplexModel (d+t)))) (b (i.natAdd d))+normalCoordinate d t i)
        (actualNormalHomogeneousPolynomial d t q g) ∈ Ideal.span {coordinateGerm (j.natAdd d)} := by
  have hgA : g ∈ actualAnalyticCoordinateIdeal (actualTangentCentreVariables d t)^q := by
    rwa [actualAnalyticCoordinateIdeal_normal]
  obtain ⟨H,hH,_⟩ := exists_actualAnalyticBlowup_quotient (actualTangentCentreVariables d t)
    (j.natAdd d) (show j.natAdd d ∈ actualTangentCentreVariables d t from ⟨j,rfl⟩) b q g hgA
  exact ⟨H,hH,actual_analytic_normal_quotient_initial_restriction d t j b q g H hg hH⟩

end
end Hironaka.HironakaActualNormalQuotientExceptionalRestriction
