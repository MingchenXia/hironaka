/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualPersistentDirectionalConeDerivatives
import Hironaka.Resolution.HironakaActualCoefficientCosupportSpread
import Hironaka.Resolution.HironakaActualCanonicalNormalCoefficientData
import Hironaka.Resolution.HironakaActualWeightedCoordinatePowerReflection

/-!
# The same canonical weighted coefficients through an actual point chart

Actual finite normal coefficients detect whole current point powers, and the
unchanged positive common-mark compression tracks the entire source/current
normalized point HS profile. Original-only canonical data are fixed once before
all base-pivot point charts with literal zero normal directions. This is whole
germ-ideal tracking; no controlled sheaf dictionary or arbitrary maximal-contact
chart/history compatibility is asserted.
Blueprint: `hironaka-actual-point-weighted-coefficient-tracking-extension.tex`.
-/
set_option autoImplicit false
open Set Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualPointWeightedCoefficientTracking
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm GermIdealOrder
  HironakaRelativeNormalMonomialBasis HironakaRelativeNormalIdeal
  HironakaActualFormalCoordinatePowerDivision HironakaActualCoefficientPresentationCentrePower
  HironakaActualCoefficientAnalyticBlowup HironakaActualAnalyticBlowupTaylor
  HironakaActualRelativeCoefficientGerms HironakaActualRelativeTaylorCoefficients
  HironakaActualAnalyticVertexCoefficientData HironakaActualWeightedCoefficientCompression
  HironakaActualWeightedCoordinatePowerReflection HironakaActualCoefficientCosupportSpread
  HironakaActualCoefficientControlledTransform HironakaActualCanonicalNormalCoefficientData
  HironakaRelativeNormalActualBaseJetDimension HironakaHolomorphicPointJets
  HironakaActualCoefficientReducedStrictGenerators HironakaActualFormalInitialDiagram
  HironakaActualOriginalFormalTaylor HironakaActualOriginalReducedVertexBasis
  HironakaActualReducedFormalStandardBasis HironakaActualPersistentDirectionalConeDerivatives
  HironakaHolomorphicJetMonomialSpan HironakaActualAnalyticStrictGenerators
  HironakaActualPointCentreStrictGenerators

private theorem tangent_point_variables (n : ℕ) : actualTangentCentreVariables 0 n=univ := by
  ext i
  simp only [actualTangentCentreVariables,mem_range,mem_univ,iff_true]
  exact ⟨Fin.cast (Nat.zero_add n) i,Fin.ext (by simp)⟩

private theorem zero_tail (n : ℕ) : {i : Fin n | 0 ≤ i.val}=(univ : Set (Fin n)) := by
  ext i
  simp

private theorem point_coordinate_ideal_eq_maximal (n : ℕ) :
    actualAnalyticCoordinateIdeal (univ : Set (Fin n))=IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) := by
  let P (m : ℕ) := actualAnalyticCoordinateIdeal (univ : Set (Fin m))=
    IsLocalRing.maximalIdeal (HolGerm (ComplexModel m))
  have h : P (0+n) := by
    change actualAnalyticCoordinateIdeal (univ : Set (Fin (0+n)))=
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n)))
    rw [←tangent_point_variables n,actualAnalyticCoordinateIdeal_normal,zeroTangentNormalIdeal_eq_maximalIdeal]
  exact (congrArg P (Nat.zero_add n)).mp h

private theorem point_power_taylor_iff (n q : ℕ) (g : HolGerm (ComplexModel n)) :
    g∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^q ↔
      actualUnshiftedTaylorAlgHom n g∈actualFormalCoordinateIdeal n univ^q := by
  have h := mem_analytic_tail_pow_iff_actualTaylor_mem n 0 q (Nat.zero_le n) g
  rw [zero_tail n,point_coordinate_ideal_eq_maximal n] at h
  exact h

private theorem presentation_point_variables (d t : ℕ) :
    actualPresentationCentreVariables (t := t) (univ : Set (Fin d))=univ := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [actualPresentationCentreVariables]

/-- The finite literal low normal coefficients detect the WHOLE actual point
power, in both analytic directions and with no normality/order certificate. -/
theorem mem_point_power_iff_low_normal_coefficients (d t q : ℕ)
    (g : HolGerm (ComplexModel (d+t))) :
    g∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t)))^q ↔
      ∀ γ : Fin t →₀ ℕ,actualNormalDegree γ<q →
        actualNormalAnalyticCoefficientGerm d t g γ∈
          IsLocalRing.maximalIdeal (HolGerm (ComplexModel d))^(q-actualNormalDegree γ) := by
  rw [point_power_taylor_iff]
  have h := mem_actualPresentationCentre_power_iff (d := d) (t := t) univ q
    (actualUnshiftedTaylorAlgHom (d+t) g)
  rw [presentation_point_variables] at h
  rw [h]
  apply forall_congr'
  intro γ
  apply imp_congr_right
  intro _hγ
  rw [point_power_taylor_iff,←actualFormalNormalCoefficient_actualTaylor]

local instance (t q : ℕ) : Fintype (normalExponentIndex t q) := normalExponentFintype t q

/-- Literal common-mark compression of the SAME finite low coefficients
exactly detects all actual current generator point powers. -/
theorem compressed_coefficients_point_power_iff (s t : ℕ)
    (I : Ideal (HolGerm (ComplexModel ((0+s)+t))))
    (H : actualInitialVertices MonomialOrder.degLex
      (Ideal.map (actualUnshiftedTaylorAlgHom ((0+s)+t)).toRingHom I) → HolGerm (ComplexModel ((0+s)+t))) :
    weightedCompression coefficientWeight
        (fun i : weightedCoefficientIndex 0 s t I => actualNormalAnalyticCoefficientGerm (0+s) t (H i.1) i.2.val)≤
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+s)))^
        weightedCommonMark (coefficientWeight (k := 0) (s := s) (t := t) (I := I)) ↔
      ∀ a,H a∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel ((0+s)+t)))^
        actualCoefficientCentreVertexWeight 0 s t a.val := by
  have hc := weightedCompression_le_normal_power_iff 0 s coefficientWeight coefficientWeight_pos
    (fun i : weightedCoefficientIndex 0 s t I => actualNormalAnalyticCoefficientGerm (0+s) t (H i.1) i.2.val)
  rw [zeroTangentNormalIdeal_eq_maximalIdeal] at hc
  rw [hc]
  constructor
  · intro h a
    apply (mem_point_power_iff_low_normal_coefficients (0+s) t _ (H a)).mpr
    intro γ hγ
    exact h ⟨a,⟨γ,hγ⟩⟩
  · intro h i
    exact (mem_point_power_iff_low_normal_coefficients (0+s) t _ (H i.1)).mp (h i.1) i.2.val i.2.property

private theorem unshiftedTaylor_property (n : ℕ)
    (P : (m : ℕ) → (HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) → Prop)
    (h : P (0+n) (originalTaylorAlgHom n)) : P n (actualUnshiftedTaylorAlgHom n) := by
  have hc {m : ℕ} (hm : m=n)
      (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) (hf : P m f) :
      P n (cast (congrArg (fun j => HolGerm (ComplexModel j) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) hm) f) := by
    subst m
    exact hf
  exact hc (Nat.zero_add n) (originalTaylorAlgHom n) h

private theorem prescribed_canonical_point_family (n : ℕ)
    (I : Ideal (HolGerm (ComplexModel n))) (e : Fin n) (b : Fin n → ℂ)
    (G H : actualInitialVertices MonomialOrder.degLex
      (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) → HolGerm (ComplexModel n))
    (hG : ∀ a,actualUnshiftedTaylorAlgHom n (G a)=actualReducedVertexSeries MonomialOrder.degLex
      (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) a)
    (hH : ∀ a,(coordinateGerm e)^(normalExponentDegree a.val)*H a=actualAnalyticBlowupPullback univ e b (G a)) :
    actualAnalyticNormalizedMemberIdeal I univ e b=Ideal.span (range H) ∧
      ((∀ ℓ,hilbertSamuelValue (actualAnalyticNormalizedMemberIdeal I univ e b) ℓ=hilbertSamuelValue I ℓ) ↔
        ∀ a,H a∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^(normalExponentDegree a.val)) := by
  let P (m : ℕ) (τ : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) :=
    ∀ (J : Ideal (HolGerm (ComplexModel m))) (j : Fin m) (b : Fin m → ℂ)
      (G H : actualInitialVertices MonomialOrder.degLex (Ideal.map τ.toRingHom J) → HolGerm (ComplexModel m)),
      (∀ a,τ (G a)=actualReducedVertexSeries MonomialOrder.degLex (Ideal.map τ.toRingHom J) a) →
      (∀ a,(coordinateGerm j)^(normalExponentDegree a.val)*H a=actualAnalyticBlowupPullback univ j b (G a)) →
      actualAnalyticNormalizedMemberIdeal J univ j b=Ideal.span (range H) ∧
        ((∀ ℓ,hilbertSamuelValue (actualAnalyticNormalizedMemberIdeal J univ j b) ℓ=hilbertSamuelValue J ℓ) ↔
          ∀ a,H a∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel m))^(normalExponentDegree a.val))
  have h : P (0+n) (originalTaylorAlgHom n) := by
    intro J e b G H hG hH
    let j : Fin n := Fin.cast (Nat.zero_add n) e
    have he : j.natAdd 0=e := by apply Fin.ext;simp [j]
    obtain ⟨H₀,hH₀,hSpan,hIff⟩ := exists_original_point_hs_iff_orders_family J j b
    have hGeq (a : actualInitialVertices MonomialOrder.degLex (Ideal.map (originalTaylorAlgHom n).toRingHom J)) :
        G a=originalReducedVertexBasis J a := by
      apply originalTaylorAlgHom_injective n
      rw [hG,originalReducedVertexBasis_taylor]
    have hEq : H=H₀ := by
      funext a
      apply mul_left_cancel₀ (pow_ne_zero (normalExponentDegree a.val)
        (HolomorphicGermReducednessBridge.coordinate_germ_ne_zero e))
      change (coordinateGerm e)^(normalExponentDegree a.val)*H a=
        (coordinateGerm e)^(normalExponentDegree a.val)*H₀ a
      rw [hH a,hGeq a]
      simpa only [he,tangent_point_variables] using (hH₀ a).symm
    rw [hEq]
    exact ⟨by simpa only [he,tangent_point_variables] using hSpan,
      by simpa only [he,tangent_point_variables] using hIff⟩
  exact unshiftedTaylor_property n P h I e b G H hG hH

private theorem point_coefficient_vertex_weight (s t : ℕ) (a : Fin ((0+s)+t) →₀ ℕ) :
    actualCoefficientCentreVertexWeight 0 s t a=normalExponentDegree a := by
  rw [actualCoefficientCentreVertexWeight,actualCoefficientCentreVariables,tangent_point_variables,
    presentation_point_variables]
  simp [Finsupp.weight_eq_sum,actualCoordinateWeight,normalExponentDegree]

/-- For prescribed exact canonical original data and genuine SAME quotients,
the whole current weighted coefficient ideal detects the actual HS profile. -/
theorem prescribed_canonical_coefficient_compression_hs_iff (s t : ℕ)
    (I : Ideal (HolGerm (ComplexModel ((0+s)+t)))) (P : ActualAnalyticVertexCoefficientData 0 s t I)
    (hP : ∀ a,actualUnshiftedTaylorAlgHom ((0+s)+t) (P.generator a)=actualReducedVertexSeries MonomialOrder.degLex
      (Ideal.map (actualUnshiftedTaylorAlgHom ((0+s)+t)).toRingHom I) a)
    (e : Fin (0+s)) (b : Fin (0+s) → ℂ)
    (H : actualInitialVertices MonomialOrder.degLex
      (Ideal.map (actualUnshiftedTaylorAlgHom ((0+s)+t)).toRingHom I) → HolGerm (ComplexModel ((0+s)+t)))
    (hH : ∀ a,(coordinateGerm (e.castAdd t))^(actualCoefficientCentreVertexWeight 0 s t a.val)*H a=
      actualAnalyticBlowupPullback (actualPresentationCentreVariables (t := t) (actualTangentCentreVariables 0 s))
        (e.castAdd t) (coefficientChartParameters (0+s) t b) (P.generator a)) :
    actualAnalyticNormalizedMemberIdeal I univ (e.castAdd t) (coefficientChartParameters (0+s) t b)=Ideal.span (range H) ∧
      (weightedCompression coefficientWeight
          (fun i : weightedCoefficientIndex 0 s t I => actualNormalAnalyticCoefficientGerm (0+s) t (H i.1) i.2.val)≤
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+s)))^
          weightedCommonMark (coefficientWeight (k := 0) (s := s) (t := t) (I := I)) ↔
        ∀ ℓ,hilbertSamuelValue (actualAnalyticNormalizedMemberIdeal I univ (e.castAdd t)
          (coefficientChartParameters (0+s) t b)) ℓ=hilbertSamuelValue I ℓ) := by
  have hH' := hH
  simp_rw [point_coefficient_vertex_weight,tangent_point_variables,presentation_point_variables] at hH'
  obtain ⟨hNamed,hIff⟩ := prescribed_canonical_point_family ((0+s)+t) I (e.castAdd t)
    (coefficientChartParameters (0+s) t b) P.generator H hP hH'
  refine ⟨hNamed,?_⟩
  rw [compressed_coefficients_point_power_iff]
  simp_rw [point_coefficient_vertex_weight]
  exact hIff.symm

/-- ONE exact original canonical datum precedes ALL actual base-pivot point
charts. Whole weighted controlled-colon tracking retains the original positive
marks and is exactly equivalent to genuine current/source point HS persistence. -/
theorem exists_original_point_weighted_coefficient_tracking (s t : ℕ)
    (I : Ideal (HolGerm (ComplexModel ((0+s)+t)))) :
    ∃ P : ActualAnalyticVertexCoefficientData 0 s t I,
      (∀ a,actualUnshiftedTaylorAlgHom ((0+s)+t) (P.generator a)=actualReducedVertexSeries MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom ((0+s)+t)).toRingHom I) a) ∧
      (∀ i : weightedCoefficientIndex 0 s t I,
        P.domain ∩ complexCoordinatePlane (0+s) 0 ⊆
          cosupport (0+s) univ
            (HironakaActualFiniteCoefficientIdeals.actualPrincipalCoefficientIdeal (0+s) (P.coefficient i.1 i.2.val))
            (coefficientWeight i)) ∧
      0<weightedCommonMark (coefficientWeight (k := 0) (s := s) (t := t) (I := I)) ∧
      ∀ (e : Fin (0+s)) (b : Fin (0+s) → ℂ),
        ∃ H : actualInitialVertices MonomialOrder.degLex
            (Ideal.map (actualUnshiftedTaylorAlgHom ((0+s)+t)).toRingHom I) → HolGerm (ComplexModel ((0+s)+t)),
          (∀ a,(coordinateGerm (e.castAdd t))^(actualCoefficientCentreVertexWeight 0 s t a.val)*H a=
            actualAnalyticBlowupPullback (actualPresentationCentreVariables (t := t) (actualTangentCentreVariables 0 s))
              (e.castAdd t) (coefficientChartParameters (0+s) t b) (P.generator a)) ∧
          actualAnalyticNormalizedMemberIdeal I univ (e.castAdd t) (coefficientChartParameters (0+s) t b)=Ideal.span (range H) ∧
          (∀ i : weightedCoefficientIndex 0 s t I,
            (coordinateGerm e)^(coefficientWeight i)*actualNormalAnalyticCoefficientGerm (0+s) t (H i.1) i.2.val=
              actualAnalyticBlowupPullback (actualTangentCentreVariables 0 s) e b (vertexCoefficientGerm P i)) ∧
          Ideal.map (actualAnalyticBlowupPullback (actualTangentCentreVariables 0 s) e b).toRingHom
              (weightedCompression coefficientWeight (vertexCoefficientGerm P))=
            Ideal.span {(coordinateGerm e)^weightedCommonMark (coefficientWeight (k := 0) (s := s) (t := t) (I := I))}*
              weightedCompression coefficientWeight
                (fun i : weightedCoefficientIndex 0 s t I => actualNormalAnalyticCoefficientGerm (0+s) t (H i.1) i.2.val) ∧
          (Ideal.map (actualAnalyticBlowupPullback (actualTangentCentreVariables 0 s) e b).toRingHom
              (weightedCompression coefficientWeight (vertexCoefficientGerm P))).colon
                {(coordinateGerm e)^weightedCommonMark (coefficientWeight (k := 0) (s := s) (t := t) (I := I))}=
            weightedCompression coefficientWeight
              (fun i : weightedCoefficientIndex 0 s t I => actualNormalAnalyticCoefficientGerm (0+s) t (H i.1) i.2.val) ∧
          ((Ideal.map (actualAnalyticBlowupPullback (actualTangentCentreVariables 0 s) e b).toRingHom
              (weightedCompression coefficientWeight (vertexCoefficientGerm P))).colon
                {(coordinateGerm e)^weightedCommonMark (coefficientWeight (k := 0) (s := s) (t := t) (I := I))}≤
              IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+s)))^
                weightedCommonMark (coefficientWeight (k := 0) (s := s) (t := t) (I := I)) ↔
            ∀ ℓ,hilbertSamuelValue (actualAnalyticNormalizedMemberIdeal I univ (e.castAdd t)
              (coefficientChartParameters (0+s) t b)) ℓ=hilbertSamuelValue I ℓ) := by
  obtain ⟨P,hP⟩ := exists_canonical_reduced_coefficient_data 0 s t I
  have hPower (a : actualInitialVertices MonomialOrder.degLex
      (Ideal.map (actualUnshiftedTaylorAlgHom ((0+s)+t)).toRingHom I)) :
      P.generator a∈actualAnalyticCoordinateIdeal (actualCoefficientCentreVariables 0 s t)^
        actualCoefficientCentreVertexWeight 0 s t a.val := by
    rw [actualCoefficientCentreVariables,tangent_point_variables,presentation_point_variables,
      point_coordinate_ideal_eq_maximal,point_coefficient_vertex_weight,point_power_taylor_iff,hP]
    have h := actualReducedVertexSeries_mem_point_power ((0+s)+t)
      (Ideal.map (actualUnshiftedTaylorAlgHom ((0+s)+t)).toRingHom I) a
    simpa [Finsupp.weight_eq_sum,actualCoordinateWeight,normalExponentDegree] using h
  obtain ⟨Q,hGen,_hCoeff,_hDom,hCos⟩ := exists_actual_vertex_cosupport_shrink 0 s t I P hPower
  have hQ (a : actualInitialVertices MonomialOrder.degLex
      (Ideal.map (actualUnshiftedTaylorAlgHom ((0+s)+t)).toRingHom I)) :
      actualUnshiftedTaylorAlgHom ((0+s)+t) (Q.generator a)=actualReducedVertexSeries MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom ((0+s)+t)).toRingHom I) a := by
    rw [hGen]
    exact hP a
  refine ⟨Q,hQ,hCos,weightedCommonMark_pos _ coefficientWeight_pos,?_⟩
  intro e b
  have he : e∈actualTangentCentreVariables 0 s := by rw [tangent_point_variables];exact mem_univ e
  obtain ⟨H,hH,hLow,hMap,hColon⟩ := exists_actual_vertex_controlled_coefficient_ideals 0 s t I Q hCos e he b
  obtain ⟨hNamed,hHS⟩ := prescribed_canonical_coefficient_compression_hs_iff s t I Q hQ e b H hH
  refine ⟨H,hH,hNamed,hLow,hMap,hColon,?_⟩
  rw [hColon]
  exact hHS

end
end Hironaka.HironakaActualPointWeightedCoefficientTracking
