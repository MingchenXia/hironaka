/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualAxisSpecializationHS
import Hironaka.Resolution.HironakaActualAnalyticPointInitialRestriction
import Hironaka.Resolution.HironakaActualAnalyticStrictGenerators
import Hironaka.Resolution.HironakaActualFiniteInitialGeneration
import Hironaka.Resolution.HironakaActualFormalIdealIntersections

/-! Actual finite initial polynomials lie in the entire analytic axis-zero normalized image. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualPointInitialIdealInclusion
noncomputable section
open HolGerm HironakaHolomorphicPointJets HironakaHolomorphicJetMonomialSpan HironakaRelativeNormalMonomialBasis
  HironakaActualOriginalFormalTaylor HironakaActualFormalIdealIntersections
  HironakaActualAnalyticVertexBasis HironakaActualFormalCoordinatePowerDivision
  HironakaActualCoefficientPresentationCentrePower HironakaActualAnalyticBlowupTaylor
  HironakaActualAnalyticStrictGenerators HironakaActualAnalyticPointInitialRestriction
  HironakaActualPointExceptionalInitialForm HironakaActualPointDehomogenizedInitial
  HironakaActualAxisContraction HironakaActualFormalInitialDiagram HironakaActualFormalVertexDivision
  HironakaActualFormalWeightedDivision HironakaActualHomogeneousInitialHS HironakaActualFiniteInitialGeneration
variable {n : ℕ}

private theorem unshiftedTaylor_property (n : ℕ)
    (P : (m : ℕ) → (HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) → Prop)
    (h : P (0+n) (originalTaylorAlgHom n)) : P n (actualUnshiftedTaylorAlgHom n) := by
  have hc {m : ℕ} (hm : m=n)
      (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) (hf : P m f) :
      P n (cast (congrArg (fun j => HolGerm (ComplexModel j) →ₐ[ℂ]
        MvPowerSeries (Fin n) ℂ) hm) f) := by
    subst m
    exact hf
  exact hc (Nat.zero_add n) (originalTaylorAlgHom n) h

private theorem unshifted_ideal_jet_lift (n : ℕ)
    (I : Ideal (HolGerm (ComplexModel n))) (F : MvPowerSeries (Fin n) ℂ)
    (hF : F ∈ Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) (q : ℕ) :
    ∃ g ∈ I, ∀ α : Fin n →₀ ℕ, normalExponentDegree α<q →
      MvPowerSeries.coeff α (actualUnshiftedTaylorAlgHom n g)=MvPowerSeries.coeff α F := by
  let P (m : ℕ) (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) : Prop :=
    ∀ (J : Ideal (HolGerm (ComplexModel m))) (H : MvPowerSeries (Fin n) ℂ),
      H ∈ Ideal.map f.toRingHom J → ∀ q : ℕ, ∃ g ∈ J,
        ∀ α : Fin n →₀ ℕ,normalExponentDegree α<q → MvPowerSeries.coeff α (f g)=MvPowerSeries.coeff α H
  exact unshiftedTaylor_property n P (exists_original_ideal_member_jet_lift n) I F hF q

private theorem unshifted_map_inf (n : ℕ) (I J : Ideal (HolGerm (ComplexModel n))) :
    Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom (I⊓J)=
      Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I ⊓
        Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom J := by
  let P (m : ℕ) (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) : Prop :=
    ∀ K L : Ideal (HolGerm (ComplexModel m)),
      Ideal.map f.toRingHom (K⊓L)=Ideal.map f.toRingHom K⊓Ideal.map f.toRingHom L
  exact unshiftedTaylor_property n P (map_inf_originalTaylorAlgHom n) I J

/-- Genuine finite approximation in the whole original intersection retains the exact full initial polynomial. -/
theorem exists_actual_original_point_initial_polynomial_lift (n : ℕ)
    (I : Ideal (HolGerm (ComplexModel n))) (d : ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (hI : F ∈ Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I)
    (hF : F ∈ actualFormalCoordinateIdeal n Set.univ ^ d) :
    ∃ g ∈ I, g ∈ actualAnalyticCoordinateIdeal Set.univ ^ d ∧
      actualPointHomogeneousPolynomial d (actualUnshiftedTaylorAlgHom n g)=actualPointHomogeneousPolynomial d F := by
  have hmem : F ∈ Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom
      (I⊓actualAnalyticCoordinateIdeal Set.univ ^ d) := by
    rw [unshifted_map_inf,Ideal.map_pow,map_actualAnalyticCoordinateIdeal_taylor]
    exact ⟨hI,hF⟩
  obtain ⟨g,hg,hjet⟩ := unshifted_ideal_jet_lift n _ F hmem (d+1)
  refine ⟨g,hg.1,hg.2,?_⟩
  apply MvPolynomial.coe_injective
  rw [actualPointHomogeneousPolynomial_coe,actualPointHomogeneousPolynomial_coe]
  apply MvPowerSeries.ext
  intro a
  rw [MvPowerSeries.coeff_homogeneousComponent,MvPowerSeries.coeff_homogeneousComponent]
  split_ifs with ha
  · apply hjet a
    have hd : normalExponentDegree a=d := by
      simpa only [normalExponentDegree,Finsupp.degree_eq_sum] using ha
    omega
  · rfl

/-- Every actual extended point-power component gives a member of the true whole specialized analytic ideal. -/
theorem actual_dehomogenized_component_mem_axis_normalized_image (n : ℕ)
    (I : Ideal (HolGerm (ComplexModel n))) (e : Fin n) (b : Fin n → ℂ)
    (d : ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (hI : F ∈ Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I)
    (hF : F ∈ actualFormalCoordinateIdeal n Set.univ ^ d) :
    MvPolynomial.aeval (coordinateGerm : Fin n → HolGerm (ComplexModel n))
        (actualPointDehomogenization e b (actualPointHomogeneousPolynomial d F)) ∈
      Ideal.map (actualAxisContractionGerm e 0).toRingHom (actualAnalyticNormalizedMemberIdeal I Set.univ e b) := by
  obtain ⟨g,hgI,hgp,hpol⟩ := exists_actual_original_point_initial_polynomial_lift n I d F hI hF
  obtain ⟨H,hH,hR⟩ := exists_actual_analytic_point_initial_quotient n e b d g hgp
  rw [hpol] at hR
  have hk : Ideal.map (actualAxisContractionGerm e 0).toRingHom
      (Ideal.span {coordinateGerm e})=⊥ := by
    rw [Ideal.map_span,Set.image_singleton]
    simp [actualAxisContractionGerm_coordinate]
  have hz := Ideal.mem_map_of_mem (actualAxisContractionGerm e 0).toRingHom hR
  rw [hk,Ideal.mem_bot] at hz
  change actualAxisContractionGerm e 0
    (H-MvPolynomial.aeval (coordinateGerm : Fin n → HolGerm (ComplexModel n))
      (actualPointDehomogenization e b (actualPointHomogeneousPolynomial d F)))=0 at hz
  rw [map_sub,actualAxisContractionGerm_dehomogenization,sub_eq_zero] at hz
  rw [← hz]
  apply Ideal.mem_map_of_mem
  exact Ideal.subset_span ⟨d,g,hgI,hgp,hH⟩

/-- The actual original analytic span of the unchanged finite dehomogenized initial vertex polynomials. -/
def actualDehomogenizedInitialIdeal (K : Ideal (MvPowerSeries (Fin n) ℂ))
    (e : Fin n) (b : Fin n → ℂ) : Ideal (HolGerm (ComplexModel n)) :=
  Ideal.span (range fun a : actualInitialVertices MonomialOrder.degLex K =>
    MvPolynomial.aeval (coordinateGerm : Fin n → HolGerm (ComplexModel n))
      (actualPointDehomogenization e b (actualInitialVertexPolynomial K a)))

/-- The entire genuine finite initial ideal lies in the whole actual coordinate-zero normalized image. -/
theorem actualDehomogenizedInitialIdeal_le_axis_normalized_image (n : ℕ)
    (I : Ideal (HolGerm (ComplexModel n))) (e : Fin n) (b : Fin n → ℂ) :
    actualDehomogenizedInitialIdeal (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) e b ≤
      Ideal.map (actualAxisContractionGerm e 0).toRingHom (actualAnalyticNormalizedMemberIdeal I Set.univ e b) := by
  apply Ideal.span_le.mpr
  rintro f ⟨a,rfl⟩
  let K := Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I
  have hF : actualVertexSeries MonomialOrder.degLex K a ∈
      actualFormalCoordinateIdeal n Set.univ ^ normalExponentDegree a.val := by
    apply (mem_actualFormalCoordinateIdeal_pow_iff Set.univ _ _).mpr
    intro c hc
    apply actualVertexSeries_total_degree_compatible K a c
    simpa [Finsupp.weight_eq_sum,actualCoordinateWeight,actualWeight_one,normalExponentDegree] using hc
  have h := actual_dehomogenized_component_mem_axis_normalized_image n I e b _
    (actualVertexSeries MonomialOrder.degLex K a) (actualVertexSeries_spec MonomialOrder.degLex K a).1 hF
  have hp : actualPointHomogeneousPolynomial (normalExponentDegree a.val)
      (actualVertexSeries MonomialOrder.degLex K a)=actualInitialVertexPolynomial K a := by
    apply MvPolynomial.coe_injective
    rw [actualPointHomogeneousPolynomial_coe,actualInitialVertexPolynomial_coe,
      actualHomogeneousInitialForm,actualHomogeneousInitialDegree,
      (actualVertexSeries_spec MonomialOrder.degLex K a).2.choose_spec.1]
  rwa [hp] at h

/-- Actual whole original ideal inclusion reverses every genuine quotient dimension. -/
theorem hilbertSamuelValue_antitone_original_ideal
    (I J : Ideal (HolGerm (ComplexModel n))) (hIJ : I ≤ J) (ℓ : ℕ) :
    hilbertSamuelValue J ℓ ≤ hilbertSamuelValue I ℓ := by
  let := finiteDimensional_quotient_sup_maximalIdeal_pow n (ℓ+1) I
  have hle : I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ (ℓ+1) ≤
      J ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ (ℓ+1) := sup_le_sup_right hIJ _
  let f := Ideal.Quotient.factorₐ ℂ hle
  exact LinearMap.finrank_le_finrank_of_surjective
    (show Function.Surjective f.toLinearMap from Ideal.Quotient.factor_surjective hle)

/-- Every actual point-normalized HS value is bounded by the genuine finite dehomogenized initial ideal value. -/
theorem hilbertSamuelValue_actual_point_normalized_le_dehomogenized_initial (n : ℕ)
    (I : Ideal (HolGerm (ComplexModel n))) (e : Fin n) (b : Fin n → ℂ) (ℓ : ℕ) :
    hilbertSamuelValue (actualAnalyticNormalizedMemberIdeal I Set.univ e b) ℓ ≤
      hilbertSamuelValue (actualDehomogenizedInitialIdeal
        (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) e b) ℓ := by
  apply (HironakaActualAxisSpecializationHS.hilbertSamuelValue_actual_axis_specialization e _ ℓ).trans
  exact hilbertSamuelValue_antitone_original_ideal _ _
    (actualDehomogenizedInitialIdeal_le_axis_normalized_image n I e b) ℓ

end
end Hironaka.HironakaActualPointInitialIdealInclusion
