/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualBlowupConeInverse
import Hironaka.Resolution.HironakaActualRelativePointChartFactorization

/-!
# Actual tangent scaling identifies normal and total filtrations

The true inserted exponent has target NORMAL weight equal to source TOTAL
degree. This proves whole formal comap powers and the literal cone inverse
filtration. Genuine analytic Taylor naturality and whole power contraction
then give the ENTIRE original analytic normal/maximal power equivalence.
No normal homogeneity is substituted for total homogeneity.
Blueprint: `hironaka-actual-tangent-scaling-filtration-extension.tex`.
-/

set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualTangentScalingFiltration
noncomputable section
open HolGerm HironakaActualFormalCoordinatePowerDivision
 HironakaActualFormalBlowupMemberGeneration HironakaActualFormalMonomialBlowupReflection
 HironakaActualSignedConeDivision HironakaActualBlowupConeInverse
 HironakaActualRelativePointChartFactorization HironakaActualAnalyticBlowupTaylor
 HironakaActualCoefficientPresentationCentrePower HironakaActualAnalyticFormalNormalPowers
 HironakaActualOriginalFormalTaylor HironakaRelativeNormalIdeal
variable {n : ℕ}

private theorem point_weight (a : Fin n →₀ ℕ) :
    Finsupp.weight (actualCoordinateWeight (univ : Set (Fin n))) a=a.degree := by
  rw [Finsupp.weight_eq_sum,Finsupp.degree_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [actualCoordinateWeight]

/-- The literal inserted exponent's NORMAL weight is exactly the source TOTAL degree. -/
theorem actualTangentScalingExponent_normal_weight (S : Set (Fin n)) (e : Fin n)
    (he : e∈S) (a : Fin n →₀ ℕ) :
    Finsupp.weight (actualCoordinateWeight S)
      (actualMonomialBlowupExponent (actualTangentScalingVariables S e) e a)=a.degree := by
  have hset : actualTangentScalingVariables S e\{e}=Sᶜ := by
    ext i
    by_cases hi : i=e
    · subst i;simp [actualTangentScalingVariables,he]
    · simp [actualTangentScalingVariables,hi]
  change Finsupp.weight (actualCoordinateWeight S)
    (a+Finsupp.single e (Finsupp.weight (actualCoordinateWeight (actualTangentScalingVariables S e\{e})) a))=_
  rw [hset,map_add,Finsupp.weight_single]
  simp only [actualCoordinateWeight,if_pos he,smul_eq_mul,mul_one]
  rw [Finsupp.weight_eq_sum,Finsupp.weight_eq_sum,Finsupp.degree_eq_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i∈S <;> simp [actualCoordinateWeight,hi]

private theorem map_pointIdeal_le_normal (S : Set (Fin n)) (e : Fin n) (he : e∈S) :
    Ideal.map (actualFormalBlowup (actualTangentScalingVariables S e) e (fun _ => 0)).toRingHom
      (actualFormalCoordinateIdeal n univ)≤actualFormalCoordinateIdeal n S := by
  rw [actualFormalCoordinateIdeal,Ideal.map_span]
  apply Ideal.span_le.mpr
  rintro _ ⟨g,⟨i,_hi,rfl⟩,rfl⟩
  change actualFormalBlowup (actualTangentScalingVariables S e) e (fun _ => 0) (MvPowerSeries.X i)∈_
  rw [actualFormalBlowup_X]
  have hx : (MvPowerSeries.X e : MvPowerSeries (Fin n) ℂ)∈actualFormalCoordinateIdeal n S :=
    Ideal.subset_span ⟨e,he,rfl⟩
  by_cases hie : i=e
  · subst i
    simpa [actualFormalBlowupCoordinates,actualTangentScalingVariables] using hx
  · by_cases hi : i∈S
    · have hz : (MvPowerSeries.X i : MvPowerSeries (Fin n) ℂ)∈actualFormalCoordinateIdeal n S :=
        Ideal.subset_span ⟨i,hi,rfl⟩
      simpa [actualFormalBlowupCoordinates,actualTangentScalingVariables,hi,hie] using hz
    · simpa [actualFormalBlowupCoordinates,actualTangentScalingVariables,hi,hie] using
        (actualFormalCoordinateIdeal n S).mul_mem_right (MvPowerSeries.X i) hx

theorem mem_normal_pow_tangentScaling_iff_point_pow (S : Set (Fin n)) (e : Fin n) (he : e∈S)
    (q : ℕ) (F : MvPowerSeries (Fin n) ℂ) :
    actualFormalBlowup (actualTangentScalingVariables S e) e (fun _ => 0) F∈
      actualFormalCoordinateIdeal n S^q ↔ F∈actualFormalCoordinateIdeal n univ^q := by
  constructor
  · intro hF
    apply (mem_actualFormalCoordinateIdeal_pow_iff univ q F).mpr
    intro a ha
    rw [point_weight] at ha
    have hc := (mem_actualFormalCoordinateIdeal_pow_iff S q _).mp hF
      (actualMonomialBlowupExponent (actualTangentScalingVariables S e) e a)
      (by rwa [actualTangentScalingExponent_normal_weight S e he])
    rwa [actualFormalBlowup_zero_coefficient] at hc
  · intro hF
    have hm := Ideal.mem_map_of_mem
      (actualFormalBlowup (actualTangentScalingVariables S e) e (fun _ => 0)).toRingHom hF
    rw [Ideal.map_pow] at hm
    exact (pow_le_pow_left' (map_pointIdeal_le_normal S e he) q) hm

theorem comap_normal_pow_tangentScaling (S : Set (Fin n)) (e : Fin n) (he : e∈S) (q : ℕ) :
    Ideal.comap (actualFormalBlowup (actualTangentScalingVariables S e) e (fun _ => 0)).toRingHom
      (actualFormalCoordinateIdeal n S^q)=actualFormalCoordinateIdeal n univ^q := by
  ext F
  exact mem_normal_pow_tangentScaling_iff_point_pow S e he q F

theorem coefficientInverse_point_pow_iff_normal_pow (S : Set (Fin n)) (e : Fin n) (he : e∈S)
    (q : ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (hCone : ∀ β,actualBlowupConeWeight (actualTangentScalingVariables S e) e β<0→
      MvPowerSeries.coeff β F=0) :
    actualBlowupCoefficientInverse (actualTangentScalingVariables S e) e F∈
      actualFormalCoordinateIdeal n univ^q ↔ F∈actualFormalCoordinateIdeal n S^q := by
  have hh := mem_normal_pow_tangentScaling_iff_point_pow S e he q
    (actualBlowupCoefficientInverse (actualTangentScalingVariables S e) e F)
  rw [actualFormalBlowup_coefficientInverse _ _ F hCone] at hh
  exact hh.symm


private theorem unshiftedTaylor_property (n : ℕ)
    (P : (m : ℕ) → (HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) → Prop)
    (h : P (0+n) (originalTaylorAlgHom n)) : P n (actualUnshiftedTaylorAlgHom n) := by
  have hc {m : ℕ} (hm : m=n)
      (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) (hf : P m f) :
      P n (cast (congrArg (fun j => HolGerm (ComplexModel j) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) hm) f) := by
    subst m
    exact hf
  exact hc (Nat.zero_add n) (originalTaylorAlgHom n) h

private theorem point_pow_iff_actualTaylor (n q : ℕ) (g : HolGerm (ComplexModel n)) :
    g∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^q ↔
      actualUnshiftedTaylorAlgHom n g∈actualFormalCoordinateIdeal n univ^q := by
  have hh : ∀ g : HolGerm (ComplexModel n),
      g∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^q ↔
        actualUnshiftedTaylorAlgHom n g∈actualFormalCoordinateIdeal n univ^q := by
    apply unshiftedTaylor_property n (fun m τ => ∀ g : HolGerm (ComplexModel m),
      g∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel m))^q ↔τ g∈actualFormalCoordinateIdeal n univ^q)
    intro g
    rw [mem_original_maximal_pow_iff_formal_coefficients_zero,mem_actualFormalCoordinateIdeal_pow_iff]
    simp only [point_weight,HironakaRelativeNormalMonomialBasis.normalExponentDegree,Finsupp.degree_eq_sum]
  exact hh g

/-- ENTIRE genuine analytic normal powers contract to actual source maximal powers. -/
theorem mem_normal_pow_analytic_tangentScaling_iff_maximal_pow (d t : ℕ) (j : Fin t)
    (q : ℕ) (g : HolGerm (ComplexModel (d+t))) :
    actualAnalyticBlowupPullback
      (actualTangentScalingVariables (actualTangentCentreVariables d t) (j.natAdd d))
      (j.natAdd d) (fun _ => 0) g∈normalIdeal d t^q ↔
      g∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t)))^q := by
  rw [mem_normalIdeal_pow_iff_actualTaylor_mem_formal_normal_pow]
  have hn := AlgHom.congr_fun (actualTaylor_analyticBlowupPullback
    (actualTangentScalingVariables (actualTangentCentreVariables d t) (j.natAdd d))
    (j.natAdd d) (fun _ => 0)) g
  change actualUnshiftedTaylorAlgHom (d+t) (actualAnalyticBlowupPullback
    (actualTangentScalingVariables (actualTangentCentreVariables d t) (j.natAdd d))
    (j.natAdd d) (fun _ => 0) g)=actualFormalBlowup
      (actualTangentScalingVariables (actualTangentCentreVariables d t) (j.natAdd d))
      (j.natAdd d) (fun _ => 0) (actualUnshiftedTaylorAlgHom (d+t) g) at hn
  rw [hn,mem_normal_pow_tangentScaling_iff_point_pow _ _ (show j.natAdd d∈actualTangentCentreVariables d t from ⟨j,rfl⟩)]
  exact (point_pow_iff_actualTaylor (d+t) q g).symm

theorem comap_analytic_normal_pow_tangentScaling (d t : ℕ) (j : Fin t) (q : ℕ) :
    Ideal.comap (actualAnalyticBlowupPullback
      (actualTangentScalingVariables (actualTangentCentreVariables d t) (j.natAdd d))
      (j.natAdd d) (fun _ => 0)).toRingHom (normalIdeal d t^q)=
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t)))^q := by
  ext g
  exact mem_normal_pow_analytic_tangentScaling_iff_maximal_pow d t j q g

end
end Hironaka.HironakaActualTangentScalingFiltration
