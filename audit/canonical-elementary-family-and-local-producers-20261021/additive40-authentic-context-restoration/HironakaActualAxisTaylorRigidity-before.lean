/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualExceptionalJetRigidity

/-!
# Actual analytic axis specialization forces whole exceptional jet rigidity

Actual finite Taylor remainders and genuine coordinate-ideal powers prove
whole Taylor commutation with the literal analytic coordinate-zero map.
The independently defined full ideal images then commute. Original point
source/current HS persistence internally supplies all exceptional initial
colons and actual full finite-jet multiplication injectivity, without
assuming a shadow profile or graded-regularity certificate.
All-vertex order retention and the relative/history criteria remain separate.
Blueprint: `hironaka-actual-axis-taylor-rigidity-extension.tex`.
-/

set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualAxisTaylorRigidity
noncomputable section
open HolGerm HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalActualBaseJetDimension HironakaHolomorphicJetMonomialSpan
  HironakaActualOriginalTaylorPolynomial HironakaActualOriginalFormalTaylor
  HironakaActualFormalIdealContraction HironakaActualOriginalFormalHSTransfer
  HironakaActualFormalCoordinatePowerDivision HironakaActualExceptionalFilteredDivision
  HironakaActualAxisContraction HironakaActualCoefficientPresentationCentrePower
variable {n : ℕ}

private theorem projection_X (e i : Fin n) :
    pivotZeroProjection e (MvPowerSeries.X i : MvPowerSeries (Fin n) ℂ)=
      if i=e then 0 else MvPowerSeries.X i := by
  by_cases hi : i=e
  · rw [if_pos hi,hi]
    exact (pivotZeroProjection_eq_zero_iff e _).mpr (dvd_refl _)
  · rw [if_neg hi]
    change MvPowerSeries.rename (Function.Embedding.subtype (fun i : Fin n => i≠e))
      (MvPowerSeries.killCompl (Function.Embedding.subtype (fun i : Fin n => i≠e))
        (MvPowerSeries.X ((Function.Embedding.subtype (fun i : Fin n => i≠e)) ⟨i,hi⟩)))=_
    rw [MvPowerSeries.killCompl_X,MvPowerSeries.rename_X]
    rfl

private theorem axis_zero_preserves_original_power (e : Fin n) (q : ℕ)
    (g : HolGerm (ComplexModel (0+n)))
    (hg : g∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n)))^q) :
    actualAxisContractionGerm (e.natAdd 0) 0 g∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n)))^q := by
  have hmap : Ideal.map (actualAxisContractionGerm (e.natAdd 0) 0).toRingHom (normalIdeal 0 n)≤normalIdeal 0 n := by
    rw [normalIdeal,Ideal.map_span,←range_comp]
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change actualAxisContractionGerm (e.natAdd 0) 0 (coordinateGerm (i.natAdd 0))∈normalIdeal 0 n
    rw [actualAxisContractionGerm_coordinate]
    by_cases hi : i=e
    · simp [hi]
    · rw [if_neg (by simpa using hi)]
      exact Ideal.mem_span_range_self (x := i)
  rw [zeroTangentNormalIdeal_eq_maximalIdeal] at hmap
  have h := Ideal.mem_map_of_mem (actualAxisContractionGerm (e.natAdd 0) 0).toRingHom hg
  rw [Ideal.map_pow] at h
  exact (pow_le_pow_left' hmap q) h

private theorem originalTaylor_axis_polynomial (e : Fin n) (p : MvPolynomial (Fin n) ℂ) :
    originalTaylorAlgHom n (actualAxisContractionGerm (e.natAdd 0) 0 (originalPolynomialEval n p))=
      pivotZeroProjection e (originalTaylorAlgHom n (originalPolynomialEval n p)) := by
  have h : ((originalTaylorAlgHom n).comp (actualAxisContractionGerm (e.natAdd 0) 0)).comp (originalPolynomialEval n)=
      (pivotZeroProjection e).comp ((originalTaylorAlgHom n).comp (originalPolynomialEval n)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply,originalPolynomialEval,MvPolynomial.aeval_X]
    change originalTaylorAlgHom n (actualAxisContractionGerm (e.natAdd 0) 0 (coordinateGerm (i.natAdd 0)))=_
    rw [actualAxisContractionGerm_coordinate,originalTaylorAlgHom_coordinate,projection_X]
    by_cases hi : i=e
    · simp [hi]
    · rw [if_neg hi,if_neg (by simpa using hi)]
      exact originalTaylorAlgHom_coordinate n i
  exact DFunLike.congr_fun h p

/-- Every genuine original whole Taylor series commutes with actual axis-zero contraction. -/
theorem originalTaylor_axis_zero (e : Fin n) (g : HolGerm (ComplexModel (0+n))) :
    originalTaylorAlgHom n (actualAxisContractionGerm (e.natAdd 0) 0 g)=
      pivotZeroProjection e (originalTaylorAlgHom n g) := by
  apply MvPowerSeries.ext
  intro β
  let q := normalExponentDegree β
  let p := originalTaylorPolynomial n q g
  have hR := originalTaylorPolynomial_remainder n q g
  have hL := (mem_original_maximal_pow_iff_formal_coefficients_zero n (q+1) _).mp
    (axis_zero_preserves_original_power e (q+1) _ hR) β (by dsimp [q];omega)
  have hRF : originalTaylorAlgHom n (g-originalPolynomialEval n p)∈actualFormalCoordinateIdeal n univ^(q+1) := by
    have he : actualFormalCoordinateIdeal n univ=genuineFormalVariables n := by
      simp [actualFormalCoordinateIdeal,genuineFormalVariables]
    rw [he]
    apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n (q+1) _).mpr
    exact (mem_original_maximal_pow_iff_formal_coefficients_zero n (q+1) _).mp hR
  have hProj := pivotZeroProjection_mem_point_power e _ _ hRF
  have he : actualFormalCoordinateIdeal n univ=genuineFormalVariables n := by
    simp [actualFormalCoordinateIdeal,genuineFormalVariables]
  rw [he] at hProj
  have hRight := (mem_genuineFormalVariables_pow_iff_coefficients_zero n (q+1) _).mp hProj β (by dsimp [q];omega)
  change MvPowerSeries.coeff β (originalTaylorAlgHom n (actualAxisContractionGerm (e.natAdd 0) 0
    (g-originalPolynomialEval n p)))=0 at hL
  simp only [map_sub] at hL hRight
  exact (sub_eq_zero.mp hL).trans ((congrArg (MvPowerSeries.coeff β) (originalTaylor_axis_polynomial e p)).trans
    (sub_eq_zero.mp hRight).symm)

private theorem unshiftedTaylor_property (n : ℕ)
    (P : (m : ℕ) → (HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) → Prop)
    (h : P (0+n) (originalTaylorAlgHom n)) : P n (actualUnshiftedTaylorAlgHom n) := by
  have hc {m : ℕ} (hm : m=n)
      (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) (hf : P m f) :
      P n (cast (congrArg (fun j => HolGerm (ComplexModel j) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) hm) f) := by
    subst m
    exact hf
  exact hc (Nat.zero_add n) (originalTaylorAlgHom n) h

/-- Actual dimension transport retains the entire genuine unshifted axis dictionary. -/
theorem unshiftedTaylor_axis_zero (e : Fin n) (g : HolGerm (ComplexModel n)) :
    actualUnshiftedTaylorAlgHom n (actualAxisContractionGerm e 0 g)=
      pivotZeroProjection e (actualUnshiftedTaylorAlgHom n g) := by
  let P (m : ℕ) (τ : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) : Prop :=
    ∀ (hm : m=n) (i : Fin m) (G : HolGerm (ComplexModel m)),
      τ (actualAxisContractionGerm i 0 G)=pivotZeroProjection (Fin.cast hm i) (τ G)
  have h : P (0+n) (originalTaylorAlgHom n) := by
    intro hm i G
    have hi : (Fin.cast hm i).natAdd 0=i := Fin.ext (by simp)
    have h := originalTaylor_axis_zero (Fin.cast hm i) G
    rwa [hi] at h
  exact unshiftedTaylor_property n P h rfl e g

/-- The ENTIRE independent ideal images commute under the actual whole maps. -/
theorem map_unshiftedTaylor_axis_zero (I : Ideal (HolGerm (ComplexModel n))) (e : Fin n) :
    Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom
      (Ideal.map (actualAxisContractionGerm e 0).toRingHom I)=
      Ideal.map (pivotZeroProjection e).toRingHom (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) := by
  have hc : (actualUnshiftedTaylorAlgHom n).toRingHom.comp (actualAxisContractionGerm e 0).toRingHom=
      (pivotZeroProjection e).toRingHom.comp (actualUnshiftedTaylorAlgHom n).toRingHom := by
    apply RingHom.ext
    intro g
    exact unshiftedTaylor_axis_zero e g
  simp only [Ideal.map_map,hc]

open HironakaHolomorphicPointJets HironakaActualPointCentreStrictGenerators
  HironakaActualAnalyticStrictGenerators HironakaActualUnshiftedInitialHSTransfer
  HironakaActualExceptionalJetHSComparison HironakaActualExceptionalJetRigidity

/-- Original source/current point HS persistence INTERNALLY supplies every
true current exceptional initial-colon identity and full jet injectivity. -/
theorem original_point_persistent_hs_initial_colons
    (I : Ideal (HolGerm (ComplexModel n))) (e : Fin n) (b : Fin n → ℂ)
    (hPersist : ∀ ℓ,hilbertSamuelValue (actualAnalyticNormalizedMemberIdeal I univ e b) ℓ=hilbertSamuelValue I ℓ) :
    let F := Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom (actualAnalyticNormalizedMemberIdeal I univ e b)
    ∀ q,Function.Injective (exceptionalJetMul F e q) ∧
      (F ⊔ actualFormalCoordinateIdeal n univ^(q+1)).colon {MvPowerSeries.X e}=
        F ⊔ actualFormalCoordinateIdeal n univ^q := by
  let N := actualAnalyticNormalizedMemberIdeal I univ e b
  obtain ⟨H,hN,_hFormal⟩ := exists_actual_point_normalized_member_generators n I e b
  have hSpan : Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom N=
      Ideal.span (range (fun a => actualUnshiftedTaylorAlgHom n (H a))) := by
    rw [show N=Ideal.span (range H) from hN,Ideal.map_span,←range_comp]
    rfl
  have hShadow : Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom
      (Ideal.map (actualAxisContractionGerm e 0).toRingHom N)=
      Ideal.span (range (fun a => pivotZeroProjection e (actualUnshiftedTaylorAlgHom n (H a)))) := by
    rw [map_unshiftedTaylor_axis_zero,hSpan,Ideal.map_span,←range_comp]
    rfl
  have hAxis := normalized_entire_hs_eq_axis_of_original_persistence I e b hPersist
  have hHS : ∀ ℓ,genuineFormalHilbertSamuelValue n
        (Ideal.span (range (fun a => actualUnshiftedTaylorAlgHom n (H a)))) ℓ=
      genuineFormalHilbertSamuelValue n
        (Ideal.span (range (fun a => pivotZeroProjection e (actualUnshiftedTaylorAlgHom n (H a))))) ℓ := by
    intro ℓ
    calc
      _=hilbertSamuelValue N ℓ := by rw [hilbertSamuelValue_eq_actual_unshifted_formal_extension,hSpan]
      _=hilbertSamuelValue (Ideal.map (actualAxisContractionGerm e 0).toRingHom N) ℓ := hAxis ℓ
      _=_ := by rw [hilbertSamuelValue_eq_actual_unshifted_formal_extension,hShadow]
  have hCol := (exceptional_colons_iff_entire_shadow_hs (fun a => actualUnshiftedTaylorAlgHom n (H a)) e).mpr hHS
  rw [←hSpan] at hCol
  dsimp only
  intro q
  exact ⟨exceptionalJetMul_injective _ e q (hCol q),hCol q⟩

end
end Hironaka.HironakaActualAxisTaylorRigidity
