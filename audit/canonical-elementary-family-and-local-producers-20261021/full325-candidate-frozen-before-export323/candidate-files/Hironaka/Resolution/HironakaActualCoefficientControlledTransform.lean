/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualWeightedGeneratorTransformJets
import Hironaka.Resolution.HironakaActualAnalyticFormalNormalPowers
import Hironaka.Resolution.HironakaActualWeightedCoefficientCompression
/-!
# Actual normal coefficients under controlled base-pivot transforms

Literal zero normal chart directions give an exact entire analytic relative
coefficient formula. Actual exceptional division then gives the retained
low-coefficient difference marks. For one prescribed analytic vertex family,
genuine original local coefficient cosupport supplies actual quotients whose
literal extracted coefficients generate the whole controlled coefficient ideal.

Blueprint: `hironaka-actual-coefficient-controlled-transform-extension.tex`.
-/

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff BigOperators
namespace Hironaka.HironakaActualCoefficientControlledTransform
noncomputable section
open HolGerm OkaRelationSheaf GermIdealOrder HironakaHolomorphicJetMonomialSpan HironakaRelativeNormalIdeal
  HironakaRelativeNormalMonomialBasis HironakaActualRelativeCoefficientGerms
  HironakaActualCoefficientPresentationCentrePower HironakaActualAnalyticBlowupTaylor
  HironakaRelativeNormalPolynomialJetAlgebra HironakaSmoothCentreCoherentDomain
  HironakaActualAnalyticFormalNormalPowers HironakaActualRelativeTaylorCoefficients
  HironakaActualAnalyticVertexCoefficientData HironakaActualWeightedCoefficientCompression
  HironakaActualCoefficientReducedStrictGenerators HironakaActualFormalInitialDiagram
  HironakaActualCoefficientAnalyticBlowup HironakaActualFiniteCoefficientIdeals
  HironakaActualLocalCoefficientStrictGenerators Hironaka.HolomorphicIdealSheaves
  HironakaActualTaylorCoordinateNaturality HironakaHolomorphicJetChartInvariance

/-- Literal zero normal chart direction, with arbitrary unchanged base directions. -/
def coefficientChartParameters (d t : ℕ) (b : Fin d → ℂ) : Fin (d+t) → ℂ :=
  Fin.addCases b (fun _ => 0)

theorem blowup_tangentPullback (d t : ℕ) (A : Set (Fin d)) (e : Fin d) (b : Fin d → ℂ)
    (a : HolGerm (ComplexModel d)) :
    actualAnalyticBlowupPullback (actualPresentationCentreVariables (t := t) A) (e.castAdd t)
        (coefficientChartParameters d t b) (tangentPullback d t a)=
      tangentPullback d t (actualAnalyticBlowupPullback A e b a) := by
  induction a using HolGerm.induction_on with
  | h f hf =>
    unfold tangentPullback actualAnalyticBlowupPullback
    rw [compAlgHom_mk,compAlgHom_mk,compAlgHom_mk,compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    apply Eventually.of_forall
    intro z
    apply congrArg f
    ext i
    simp [tangentProjection_apply,actualAnalyticBlowupMap_apply,actualAnalyticBlowupCoordinate,
      actualPresentationCentreVariables,coefficientChartParameters]

theorem blowup_normalCoordinate (d t : ℕ) (A : Set (Fin d)) (e : Fin d) (b : Fin d → ℂ)
    (i : Fin t) :
    actualAnalyticBlowupPullback (actualPresentationCentreVariables (t := t) A) (e.castAdd t)
        (coefficientChartParameters d t b) (normalCoordinate d t i)=
      coordinateGerm (e.castAdd t)*normalCoordinate d t i := by
  have hie : i.natAdd d ≠ e.castAdd t := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    omega
  simp [normalCoordinate,actualAnalyticBlowupPullback_coordinate,actualPresentationCentreVariables,
    coefficientChartParameters,hie]

theorem blowup_normal_power (d t : ℕ) (A : Set (Fin d)) (e : Fin d) (b : Fin d → ℂ)
    (q : ℕ) (g : HolGerm (ComplexModel (d+t))) (hg : g ∈ normalIdeal d t^q) :
    actualAnalyticBlowupPullback (actualPresentationCentreVariables (t := t) A) (e.castAdd t)
        (coefficientChartParameters d t b) g ∈ normalIdeal d t^q := by
  let B := actualAnalyticBlowupPullback (actualPresentationCentreVariables (t := t) A) (e.castAdd t)
    (coefficientChartParameters d t b)
  have hle : Ideal.map B.toRingHom (normalIdeal d t) ≤ normalIdeal d t := by
    apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro g ⟨i,rfl⟩
    change B (normalCoordinate d t i) ∈ normalIdeal d t
    rw [blowup_normalCoordinate]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i,rfl⟩)
  have hm := Ideal.mem_map_of_mem B.toRingHom hg
  rw [Ideal.map_pow] at hm
  exact (pow_le_pow_left' hle q) hm

private theorem normalTaylorPolynomial_tangent_mul (d t q : ℕ)
    (a : HolGerm (ComplexModel d)) (g : HolGerm (ComplexModel (d+t))) :
    actualNormalTaylorPolynomial d t q (tangentPullback d t a*g)=
      MvPolynomial.C a*actualNormalTaylorPolynomial d t q g := by
  apply Eq.symm
  apply actualNormalTaylorPolynomial_unique
  · intro γ hγ
    rw [MvPolynomial.coeff_C_mul,actualNormalTaylorPolynomial_coefficient_high d t q g γ hγ,mul_zero]
  · have hr := Ideal.mul_mem_left (normalIdeal d t^q) (tangentPullback d t a)
      (actualNormalTaylorPolynomial_remainder d t q g)
    change tangentPullback d t a*g-normalPolynomialEval d t (MvPolynomial.C a*actualNormalTaylorPolynomial d t q g) ∈ _
    rw [map_mul]
    have hC : normalPolynomialEval d t (MvPolynomial.C a)=tangentPullback d t a := by
      let := tangentAlgebra d t
      exact MvPolynomial.aeval_C (normalCoordinate d t) a
    rw [hC]
    simpa only [mul_sub] using hr

theorem coefficient_tangent_mul (d t : ℕ) (a : HolGerm (ComplexModel d))
    (g : HolGerm (ComplexModel (d+t))) (γ : Fin t →₀ ℕ) :
    actualNormalAnalyticCoefficientGerm d t (tangentPullback d t a*g) γ=
      a*actualNormalAnalyticCoefficientGerm d t g γ := by
  unfold actualNormalAnalyticCoefficientGerm
  rw [normalTaylorPolynomial_tangent_mul,MvPolynomial.coeff_C_mul]


private def coefficientTransformPolynomial (d t : ℕ) (A : Set (Fin d)) (e : Fin d) (b : Fin d → ℂ)
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) :
    MvPolynomial (Fin t) (HolGerm (ComplexModel d)) :=
  ∑ γ ∈ P.support, MvPolynomial.monomial γ
    ((coordinateGerm e)^normalExponentDegree γ*actualAnalyticBlowupPullback A e b (MvPolynomial.coeff γ P))

private theorem coefficientTransformPolynomial_coeff (d t : ℕ) (A : Set (Fin d)) (e : Fin d) (b : Fin d → ℂ)
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) (γ : Fin t →₀ ℕ) :
    MvPolynomial.coeff γ (coefficientTransformPolynomial d t A e b P)=
      (coordinateGerm e)^normalExponentDegree γ*actualAnalyticBlowupPullback A e b (MvPolynomial.coeff γ P) := by
  by_cases hγ : γ ∈ P.support
  · simp [coefficientTransformPolynomial,MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial,hγ]
  · have hz : MvPolynomial.coeff γ P=0 := by
      simpa only [MvPolynomial.mem_support_iff,not_not] using hγ
    simp [coefficientTransformPolynomial,MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial,hγ,hz]

private theorem blowup_normalMonomial (d t : ℕ) (A : Set (Fin d)) (e : Fin d) (b : Fin d → ℂ)
    (γ : Fin t →₀ ℕ) :
    actualAnalyticBlowupPullback (actualPresentationCentreVariables (t := t) A) (e.castAdd t)
        (coefficientChartParameters d t b) (normalExponentMonomial d t γ)=
      (coordinateGerm (e.castAdd t))^normalExponentDegree γ*normalExponentMonomial d t γ := by
  unfold normalExponentMonomial
  simp only [map_prod,map_pow,blowup_normalCoordinate,mul_pow]
  rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
  rfl

private theorem blowup_normalPolynomial (d t : ℕ) (A : Set (Fin d)) (e : Fin d) (b : Fin d → ℂ)
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) :
    actualAnalyticBlowupPullback (actualPresentationCentreVariables (t := t) A) (e.castAdd t)
        (coefficientChartParameters d t b) (normalPolynomialEval d t P)=
      normalPolynomialEval d t (coefficientTransformPolynomial d t A e b P) := by
  rw [coefficientTransformPolynomial,map_sum]
  conv_lhs => rw [P.as_sum]
  rw [map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro γ hγ
  rw [normalPolynomialEval_monomial,map_mul,blowup_tangentPullback,blowup_normalMonomial,
    normalPolynomialEval_monomial,map_mul,map_pow,tangentPullback_coordinateGerm]
  ring

private theorem normalTaylorPolynomial_blowup (d t q : ℕ) (A : Set (Fin d)) (e : Fin d) (b : Fin d → ℂ)
    (g : HolGerm (ComplexModel (d+t))) :
    actualNormalTaylorPolynomial d t q
        (actualAnalyticBlowupPullback (actualPresentationCentreVariables (t := t) A) (e.castAdd t)
          (coefficientChartParameters d t b) g)=
      coefficientTransformPolynomial d t A e b (actualNormalTaylorPolynomial d t q g) := by
  apply Eq.symm
  apply actualNormalTaylorPolynomial_unique
  · intro γ hγ
    rw [coefficientTransformPolynomial_coeff,actualNormalTaylorPolynomial_coefficient_high d t q g γ hγ,
      map_zero,mul_zero]
  · have hr := blowup_normal_power d t A e b q _ (actualNormalTaylorPolynomial_remainder d t q g)
    rw [map_sub,blowup_normalPolynomial] at hr
    exact hr

theorem coefficient_blowup (d t : ℕ) (A : Set (Fin d)) (e : Fin d) (b : Fin d → ℂ)
    (g : HolGerm (ComplexModel (d+t))) (γ : Fin t →₀ ℕ) :
    actualNormalAnalyticCoefficientGerm d t
        (actualAnalyticBlowupPullback (actualPresentationCentreVariables (t := t) A) (e.castAdd t)
          (coefficientChartParameters d t b) g) γ=
      (coordinateGerm e)^normalExponentDegree γ*
        actualAnalyticBlowupPullback A e b (actualNormalAnalyticCoefficientGerm d t g γ) := by
  unfold actualNormalAnalyticCoefficientGerm
  rw [normalTaylorPolynomial_blowup,coefficientTransformPolynomial_coeff]


private theorem coefficient_quotient_product (d t : ℕ) (A : Set (Fin d)) (e : Fin d) (b : Fin d → ℂ)
    (m : ℕ) (g H : HolGerm (ComplexModel (d+t)))
    (hH : (coordinateGerm (e.castAdd t))^m*H=
      actualAnalyticBlowupPullback (actualPresentationCentreVariables (t := t) A) (e.castAdd t)
        (coefficientChartParameters d t b) g) (γ : Fin t →₀ ℕ) :
    (coordinateGerm e)^m*actualNormalAnalyticCoefficientGerm d t H γ=
      (coordinateGerm e)^normalExponentDegree γ*
        actualAnalyticBlowupPullback A e b (actualNormalAnalyticCoefficientGerm d t g γ) := by
  calc
    _ = actualNormalAnalyticCoefficientGerm d t
        (tangentPullback d t ((coordinateGerm e)^m)*H) γ := (coefficient_tangent_mul d t _ H γ).symm
    _ = _ := by rw [map_pow,tangentPullback_coordinateGerm,hH,coefficient_blowup]

theorem coefficient_controlled_quotient (d t : ℕ) (A : Set (Fin d)) (e : Fin d) (b : Fin d → ℂ)
    (m : ℕ) (g H : HolGerm (ComplexModel (d+t)))
    (hH : (coordinateGerm (e.castAdd t))^m*H=
      actualAnalyticBlowupPullback (actualPresentationCentreVariables (t := t) A) (e.castAdd t)
        (coefficientChartParameters d t b) g) (γ : Fin t →₀ ℕ) (hγ : normalExponentDegree γ≤m) :
    (coordinateGerm e)^(m-normalExponentDegree γ)*actualNormalAnalyticCoefficientGerm d t H γ=
      actualAnalyticBlowupPullback A e b (actualNormalAnalyticCoefficientGerm d t g γ) := by
  have he0 : (coordinateGerm e : HolGerm (ComplexModel d)) ≠ 0 :=
    HolomorphicGermReducednessBridge.coordinate_germ_ne_zero e
  apply mul_left_cancel₀ (pow_ne_zero (normalExponentDegree γ) he0)
  calc
    _ = (coordinateGerm e)^m*actualNormalAnalyticCoefficientGerm d t H γ := by
      rw [← mul_assoc,← pow_add,Nat.add_sub_of_le hγ]
    _ = _ := coefficient_quotient_product d t A e b m g H hH γ

theorem coefficient_controlled_quotient_high (d t : ℕ) (A : Set (Fin d)) (e : Fin d) (b : Fin d → ℂ)
    (m : ℕ) (g H : HolGerm (ComplexModel (d+t)))
    (hH : (coordinateGerm (e.castAdd t))^m*H=
      actualAnalyticBlowupPullback (actualPresentationCentreVariables (t := t) A) (e.castAdd t)
        (coefficientChartParameters d t b) g) (γ : Fin t →₀ ℕ) (hγ : m≤normalExponentDegree γ) :
    actualNormalAnalyticCoefficientGerm d t H γ=
      (coordinateGerm e)^(normalExponentDegree γ-m)*
        actualAnalyticBlowupPullback A e b (actualNormalAnalyticCoefficientGerm d t g γ) := by
  have he0 : (coordinateGerm e : HolGerm (ComplexModel d)) ≠ 0 :=
    HolomorphicGermReducednessBridge.coordinate_germ_ne_zero e
  apply mul_left_cancel₀ (pow_ne_zero m he0)
  calc
    _ = (coordinateGerm e)^normalExponentDegree γ*
        actualAnalyticBlowupPullback A e b (actualNormalAnalyticCoefficientGerm d t g γ) :=
      coefficient_quotient_product d t A e b m g H hH γ
    _ = _ := by rw [← mul_assoc,← pow_add,Nat.add_sub_of_le hγ]

theorem exists_actual_family_controlled_coefficient_quotients (d t : ℕ) (A : Set (Fin d))
    (e : Fin d) (he : e ∈ A) (b : Fin d → ℂ) {ι : Type*}
    (g : ι → HolGerm (ComplexModel (d+t))) (m : ι → ℕ)
    (hg : ∀ i, g i ∈ actualAnalyticCoordinateIdeal (actualPresentationCentreVariables (t := t) A)^(m i)) :
    ∃ H : ι → HolGerm (ComplexModel (d+t)),
      (∀ i, (coordinateGerm (e.castAdd t))^(m i)*H i=
        actualAnalyticBlowupPullback (actualPresentationCentreVariables (t := t) A) (e.castAdd t)
          (coefficientChartParameters d t b) (g i)) ∧
      (∀ i γ, normalExponentDegree γ≤m i →
        (coordinateGerm e)^(m i-normalExponentDegree γ)*actualNormalAnalyticCoefficientGerm d t (H i) γ=
          actualAnalyticBlowupPullback A e b (actualNormalAnalyticCoefficientGerm d t (g i) γ)) ∧
      ∀ i γ, m i≤normalExponentDegree γ →
        actualNormalAnalyticCoefficientGerm d t (H i) γ=
          (coordinateGerm e)^(normalExponentDegree γ-m i)*
            actualAnalyticBlowupPullback A e b (actualNormalAnalyticCoefficientGerm d t (g i) γ) := by
  have heFull : e.castAdd t ∈ actualPresentationCentreVariables (t := t) A := by
    simpa [actualPresentationCentreVariables] using he
  choose H hH hTaylor using fun i => exists_actualAnalyticBlowup_quotient
    (actualPresentationCentreVariables (t := t) A) (e.castAdd t) heFull
      (coefficientChartParameters d t b) (m i) (g i) (hg i)
  exact ⟨H,hH,(fun i γ hγ => coefficient_controlled_quotient d t A e b (m i) (g i) (H i) (hH i) γ hγ),
    fun i γ hγ => coefficient_controlled_quotient_high d t A e b (m i) (g i) (H i) (hH i) γ hγ⟩


local instance (t q : ℕ) : Fintype (normalExponentIndex t q) := normalExponentFintype t q

theorem vertex_coefficient_eq_analytic_germ (k s t : ℕ)
    (I : Ideal (HolGerm (ComplexModel ((k+s)+t)))) (P : ActualAnalyticVertexCoefficientData k s t I)
    (a : actualInitialVertices MonomialOrder.degLex
      (Ideal.map (actualUnshiftedTaylorAlgHom ((k+s)+t)).toRingHom I)) (γ : Fin t →₀ ℕ) :
    actualNormalAnalyticCoefficientGerm (k+s) t (P.generator a) γ=
      HolGerm.mk (P.coefficient a γ) (P.holomorphic a γ) := by
  apply actualUnshiftedTaylorAlgHom_injective (k+s)
  rw [← actualFormalNormalCoefficient_actualTaylor]
  exact P.coefficient_eq a γ

theorem exists_actual_vertex_controlled_coefficient_ideals (k s t : ℕ)
    (I : Ideal (HolGerm (ComplexModel ((k+s)+t)))) (P : ActualAnalyticVertexCoefficientData k s t I)
    (hcosupp : ∀ i : weightedCoefficientIndex k s t I,
      P.domain ∩ complexCoordinatePlane (k+s) k ⊆
        cosupport (k+s) univ (actualPrincipalCoefficientIdeal (k+s) (P.coefficient i.1 i.2.val))
          (coefficientWeight i))
    (e : Fin (k+s)) (he : e ∈ actualTangentCentreVariables k s) (b : Fin (k+s) → ℂ) :
    ∃ H : actualInitialVertices MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom ((k+s)+t)).toRingHom I) → HolGerm (ComplexModel ((k+s)+t)),
      (∀ a, (coordinateGerm (e.castAdd t))^(actualCoefficientCentreVertexWeight k s t a.val)*H a=
        actualAnalyticBlowupPullback
          (actualPresentationCentreVariables (t := t) (actualTangentCentreVariables k s)) (e.castAdd t)
          (coefficientChartParameters (k+s) t b) (P.generator a)) ∧
      (∀ i : weightedCoefficientIndex k s t I,
        (coordinateGerm e)^(coefficientWeight i)*actualNormalAnalyticCoefficientGerm (k+s) t (H i.1) i.2.val=
          actualAnalyticBlowupPullback (actualTangentCentreVariables k s) e b (vertexCoefficientGerm P i)) ∧
      Ideal.map (actualAnalyticBlowupPullback (actualTangentCentreVariables k s) e b).toRingHom
          (weightedCompression coefficientWeight (vertexCoefficientGerm P))=
        Ideal.span {(coordinateGerm e)^weightedCommonMark (coefficientWeight (k := k) (s := s) (t := t) (I := I))}*
          weightedCompression coefficientWeight
            (fun i : weightedCoefficientIndex k s t I => actualNormalAnalyticCoefficientGerm (k+s) t (H i.1) i.2.val) ∧
      (Ideal.map (actualAnalyticBlowupPullback (actualTangentCentreVariables k s) e b).toRingHom
          (weightedCompression coefficientWeight (vertexCoefficientGerm P))).colon
            {(coordinateGerm e)^weightedCommonMark (coefficientWeight (k := k) (s := s) (t := t) (I := I))}=
        weightedCompression coefficientWeight
          (fun i : weightedCoefficientIndex k s t I => actualNormalAnalyticCoefficientGerm (k+s) t (H i.1) i.2.val) := by
  have hg (a : actualInitialVertices MonomialOrder.degLex
      (Ideal.map (actualUnshiftedTaylorAlgHom ((k+s)+t)).toRingHom I)) :
      P.generator a ∈ actualAnalyticCoordinateIdeal
        (actualPresentationCentreVariables (t := t) (actualTangentCentreVariables k s))^
          actualCoefficientCentreVertexWeight k s t a.val := by
    apply mem_analyticPresentationCentre_pow_of_local_coefficient_cosupport k s t _ _
      P.domain P.isOpen_domain P.zero_mem_domain (P.coefficient a) (P.holomorphic a)
      (fun γ => actualPrincipalCoefficientIdeal (k+s) (P.coefficient a γ))
      (P.coherent a) (P.coefficient_member a)
    · intro γ hγ
      exact hcosupp ⟨a,⟨γ,hγ⟩⟩
    · intro γ _
      exact vertex_coefficient_eq_analytic_germ k s t I P a γ
  obtain ⟨H,hH,hLow,_hHigh⟩ := exists_actual_family_controlled_coefficient_quotients (k+s) t
    (actualTangentCentreVariables k s) e he b P.generator
      (fun a => actualCoefficientCentreVertexWeight k s t a.val) hg
  have hc (i : weightedCoefficientIndex k s t I) :
      (coordinateGerm e)^(coefficientWeight i)*actualNormalAnalyticCoefficientGerm (k+s) t (H i.1) i.2.val=
        actualAnalyticBlowupPullback (actualTangentCentreVariables k s) e b (vertexCoefficientGerm P i) := by
    have hh := hLow i.1 i.2.val (Nat.le_of_lt i.2.property)
    rwa [vertex_coefficient_eq_analytic_germ] at hh
  have hmem (i : weightedCoefficientIndex k s t I) :
      vertexCoefficientGerm P i ∈ actualAnalyticCoordinateIdeal (actualTangentCentreVariables k s)^coefficientWeight i := by
    rw [actualAnalyticCoordinateIdeal_normal]
    exact mk_mem_normalIdeal_pow_of_local_cosupport k s (coefficientWeight i)
      (actualPrincipalCoefficientIdeal (k+s) (P.coefficient i.1 i.2.val))
      P.domain P.isOpen_domain P.zero_mem_domain (P.coherent i.1 i.2.val i.2.property)
      (hcosupp i) (P.holomorphic i.1 i.2.val) (P.coefficient_member i.1 i.2.val i.2.property)
  obtain ⟨_,c,hcprod,_hcTaylor,hmap,hcolon⟩ := exists_actual_weighted_compression_blowup
    (actualTangentCentreVariables k s) e he b coefficientWeight coefficientWeight_pos (vertexCoefficientGerm P) hmem
  have hcEq : c=(fun i : weightedCoefficientIndex k s t I => actualNormalAnalyticCoefficientGerm (k+s) t (H i.1) i.2.val) := by
    funext i
    exact mul_left_cancel₀ (pow_ne_zero _ (HolomorphicGermReducednessBridge.coordinate_germ_ne_zero e))
      ((hcprod i).trans (hc i).symm)
  rw [hcEq] at hmap hcolon
  exact ⟨H,hH,hc,hmap,hcolon⟩

end
end Hironaka.HironakaActualCoefficientControlledTransform
