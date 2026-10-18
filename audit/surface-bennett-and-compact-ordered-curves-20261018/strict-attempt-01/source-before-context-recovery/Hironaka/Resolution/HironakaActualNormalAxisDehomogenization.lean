/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualNormalQuotientExceptionalRestriction
import Hironaka.Resolution.HironakaActualNormalScalingRays
import Hironaka.Resolution.HironakaActualPointInitialIdealInclusion

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualNormalAxisDehomogenization
noncomputable section
open HolGerm OkaRelationSheaf HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaActualCoefficientPresentationCentrePower HironakaActualAnalyticBlowupTaylor
  HironakaActualAnalyticStrictGenerators HironakaActualNormalHomogeneousComponents
  HironakaActualNormalQuotientExceptionalRestriction HironakaActualNormalUnitCoordinateChange
  HironakaActualNormalUnitAnalyticCoefficients HironakaActualNormalScalingRays
  HironakaActualAxisContraction HironakaActualAxisSpecializationHS
  HironakaActualPointInitialIdealInclusion HironakaActualPointUnitCoordinateChange
  HironakaHolomorphicJetMonomialSpan HironakaHolomorphicPointJets HironakaHolomorphicJetChartInvariance

/-- Actual finite normal-polynomial dehomogenization, with genuine whole tangent-germ coefficients. -/
def actualDehomogenizedNormalPolynomialEval (d t : ℕ) (j : Fin t) (b : Fin (d+t) → ℂ) :
    MvPolynomial (Fin t) (HolGerm (ComplexModel d)) →+* HolGerm (ComplexModel (d+t)) :=
  MvPolynomial.eval₂Hom (tangentPullback d t).toRingHom
    (fun i => if i=j then 1 else algebraMap ℂ (HolGerm (ComplexModel (d+t))) (b (i.natAdd d))+normalCoordinate d t i)

/-- The entire original ideal spanned by the actual dehomogenized finite family. -/
def actualDehomogenizedNormalFamilyIdeal (d t : ℕ) {ι : Type*}
    (P : ι → MvPolynomial (Fin t) (HolGerm (ComplexModel d))) (j : Fin t) (b : Fin (d+t) → ℂ) :
    Ideal (HolGerm (ComplexModel (d+t))) :=
  Ideal.span (range fun i => actualDehomogenizedNormalPolynomialEval d t j b (P i))

/-- The genuine axis contraction fixes EVERY original tangent germ, even at its actual zero parameter. -/
theorem actualAxisContractionGerm_tangentPullback (d t : ℕ) (j : Fin t) (c : ℂ)
    (a : HolGerm (ComplexModel d)) :
    actualAxisContractionGerm (j.natAdd d) c (tangentPullback d t a)=tangentPullback d t a := by
  induction a using HolGerm.induction_on with
  | h f hf =>
    unfold actualAxisContractionGerm tangentPullback
    rw [compAlgHom_mk,compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    apply Eventually.of_forall
    intro z
    apply congrArg f
    ext i
    have hie : i.castAdd t ≠ j.natAdd d := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
      omega
    simp [tangentProjection_apply,actualAxisContraction_apply,hie]

/-- True contraction fixes each WHOLE actual dehomogenized polynomial, not only its finite jets. -/
theorem actualAxisContractionGerm_dehomogenizedNormalPolynomial (d t : ℕ) (j : Fin t)
    (b : Fin (d+t) → ℂ) (c : ℂ) (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) :
    actualAxisContractionGerm (j.natAdd d) c (actualDehomogenizedNormalPolynomialEval d t j b P)=
      actualDehomogenizedNormalPolynomialEval d t j b P := by
  let ρ := actualAxisContractionGerm (j.natAdd d) c
  change ρ.toRingHom (MvPolynomial.eval₂Hom (tangentPullback d t).toRingHom _ P)=_
  rw [MvPolynomial.map_eval₂Hom]
  have hcoef : ρ.toRingHom.comp (tangentPullback d t).toRingHom=(tangentPullback d t).toRingHom := by
    apply RingHom.ext
    intro a
    exact actualAxisContractionGerm_tangentPullback d t j c a
  rw [hcoef]
  change MvPolynomial.eval₂Hom (tangentPullback d t).toRingHom
    (fun i => ρ (if i=j then 1 else
      algebraMap ℂ (HolGerm (ComplexModel (d+t))) (b (i.natAdd d))+normalCoordinate d t i)) P=_
  have hx : (fun i : Fin t => ρ (if i=j then 1 else
      algebraMap ℂ (HolGerm (ComplexModel (d+t))) (b (i.natAdd d))+normalCoordinate d t i))=
      (fun i => if i=j then 1 else
        algebraMap ℂ (HolGerm (ComplexModel (d+t))) (b (i.natAdd d))+normalCoordinate d t i) := by
    funext i
    by_cases hi : i=j
    · simp [hi]
    · have hie : i.natAdd d ≠ j.natAdd d := by
        intro h
        apply hi
        apply Fin.ext
        have hv := congrArg Fin.val h
        simp only [Fin.val_natAdd] at hv
        omega
      simp [ρ,hi,normalCoordinate,actualAxisContractionGerm_coordinate,hie]
  rw [hx]
  rfl

/-- ONLY genuine original numerator and normal-power membership give actual canonical component membership in the zero image. -/
theorem actual_dehomogenized_normal_component_mem_axis_normalized_image (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (j : Fin t) (b : Fin (d+t) → ℂ)
    (q : ℕ) (g : HolGerm (ComplexModel (d+t))) (hgI : g ∈ I) (hgN : g ∈ normalIdeal d t ^ q) :
    actualDehomogenizedNormalPolynomialEval d t j b (actualNormalHomogeneousPolynomial d t q g) ∈
      Ideal.map (actualAxisContractionGerm (j.natAdd d) 0).toRingHom
        (actualAnalyticNormalizedMemberIdeal I (actualTangentCentreVariables d t) (j.natAdd d) b) := by
  obtain ⟨H,hH,hR⟩ := exists_actual_analytic_normal_initial_quotient d t j b q g hgN
  have hk : Ideal.map (actualAxisContractionGerm (j.natAdd d) 0).toRingHom
      (Ideal.span {coordinateGerm (j.natAdd d)})=⊥ := by
    rw [Ideal.map_span,Set.image_singleton]
    simp [actualAxisContractionGerm_coordinate]
  have hz := Ideal.mem_map_of_mem (actualAxisContractionGerm (j.natAdd d) 0).toRingHom hR
  rw [hk,Ideal.mem_bot] at hz
  change actualAxisContractionGerm (j.natAdd d) 0
    (H-actualDehomogenizedNormalPolynomialEval d t j b (actualNormalHomogeneousPolynomial d t q g))=0 at hz
  rw [map_sub,actualAxisContractionGerm_dehomogenizedNormalPolynomial,sub_eq_zero] at hz
  rw [← hz]
  apply Ideal.mem_map_of_mem
  apply Ideal.subset_span
  have hgA : g ∈ actualAnalyticCoordinateIdeal (actualTangentCentreVariables d t)^q := by
    rwa [actualAnalyticCoordinateIdeal_normal]
  exact ⟨q,g,hgI,hgA,hH⟩

/-- Every actual component of an ordinary normal-compatible family gives the ENTIRE correct ideal inclusion. -/
theorem actualDehomogenizedNormalFamilyIdeal_le_axis_normalized_image (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) {ι : Type*}
    (g : ι → HolGerm (ComplexModel (d+t))) (q : ι → ℕ)
    (hgI : ∀ i,g i ∈ I) (hgN : ∀ i,g i ∈ normalIdeal d t ^ q i)
    (j : Fin t) (b : Fin (d+t) → ℂ) :
    actualDehomogenizedNormalFamilyIdeal d t (fun i => actualNormalHomogeneousPolynomial d t (q i) (g i)) j b ≤
      Ideal.map (actualAxisContractionGerm (j.natAdd d) 0).toRingHom
        (actualAnalyticNormalizedMemberIdeal I (actualTangentCentreVariables d t) (j.natAdd d) b) := by
  apply Ideal.span_le.mpr
  rintro f ⟨i,rfl⟩
  exact actual_dehomogenized_normal_component_mem_axis_normalized_image d t I j b (q i) (g i) (hgI i) (hgN i)

/-- BOTH whole ideal image directions use true variable-degree inverse unit powers in the original germ ring. -/
theorem map_actualNormalUnit_dehomogenizedFamily (d t : ℕ) {ι : Type*}
    (P : ι → MvPolynomial (Fin t) (HolGerm (ComplexModel d))) (q : ι → ℕ)
    (hP : ∀ i,(P i).IsHomogeneous (q i)) (j : Fin t) (b : Fin (d+t) → ℂ) :
    Ideal.map (actualNormalUnitGermEquiv (actualTangentCentreVariables d t) (j.natAdd d) b).toRingEquiv.toRingHom
      (actualDehomogenizedNormalFamilyIdeal d t P j b)=
        actualTranslatedNormalFamilyIdeal d t P (fun i => if i=j then 1 else b (i.natAdd d)) := by
  have hpoly (i : ι) :
      actualNormalUnitGermEquiv (actualTangentCentreVariables d t) (j.natAdd d) b
          (actualDehomogenizedNormalPolynomialEval d t j b (P i))=
        (actualPointUnitReciprocal (j.natAdd d))^(q i)*actualTranslatedNormalPolynomialEval d t
          (fun k => if k=j then 1 else b (k.natAdd d)) (P i) :=
    actualNormalUnitGermEquiv_analytic_dehomogenization d t j b (P i) (q i) (hP i)
  rw [actualDehomogenizedNormalFamilyIdeal,Ideal.map_span,← Set.range_comp]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro f ⟨i,rfl⟩
    change actualNormalUnitGermEquiv (actualTangentCentreVariables d t) (j.natAdd d) b
      (actualDehomogenizedNormalPolynomialEval d t j b (P i)) ∈ _
    rw [hpoly]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i,rfl⟩)
  · apply Ideal.span_le.mpr
    rintro f ⟨i,rfl⟩
    have hg : actualNormalUnitGermEquiv (actualTangentCentreVariables d t) (j.natAdd d) b
        (actualDehomogenizedNormalPolynomialEval d t j b (P i)) ∈
      Ideal.span (range fun k => actualNormalUnitGermEquiv (actualTangentCentreVariables d t) (j.natAdd d) b
        (actualDehomogenizedNormalPolynomialEval d t j b (P k))) := Ideal.subset_span ⟨i,rfl⟩
    rw [hpoly] at hg
    have hh := Ideal.mul_mem_left _ ((1+coordinateGerm (j.natAdd d))^(q i)) hg
    have hu : (1+coordinateGerm (j.natAdd d))^(q i)*(actualPointUnitReciprocal (j.natAdd d))^(q i)=1 := by
      rw [← mul_pow,actualPointUnit_mul_reciprocal,one_pow]
    rw [← mul_assoc,hu,one_mul] at hh
    exact hh

/-- Genuine whole-image equality gives equality of EVERY unchanged original HS value. -/
theorem hilbertSamuelValue_dehomogenizedNormalFamily_eq_translated (d t : ℕ) {ι : Type*}
    (P : ι → MvPolynomial (Fin t) (HolGerm (ComplexModel d))) (q : ι → ℕ)
    (hP : ∀ i,(P i).IsHomogeneous (q i)) (j : Fin t) (b : Fin (d+t) → ℂ) (ℓ : ℕ) :
    hilbertSamuelValue (actualDehomogenizedNormalFamilyIdeal d t P j b) ℓ=
      hilbertSamuelValue (actualTranslatedNormalFamilyIdeal d t P (fun i => if i=j then 1 else b (i.natAdd d))) ℓ := by
  have h := hilbertSamuelValue_actualNormalUnitGermEquiv (actualTangentCentreVariables d t) (j.natAdd d) b
    (actualDehomogenizedNormalFamilyIdeal d t P j b) ℓ
  rw [map_actualNormalUnit_dehomogenizedFamily d t P q hP j b] at h
  exact h.symm

/-- All original normalized HS orders are bounded by the actual canonical dehomogenized family under ordinary source compatibility. -/
theorem hilbertSamuelValue_actual_normal_normalized_le_dehomogenized (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) {ι : Type*}
    (g : ι → HolGerm (ComplexModel (d+t))) (q : ι → ℕ)
    (hgI : ∀ i,g i ∈ I) (hgN : ∀ i,g i ∈ normalIdeal d t ^ q i)
    (j : Fin t) (b : Fin (d+t) → ℂ) (ℓ : ℕ) :
    hilbertSamuelValue (actualAnalyticNormalizedMemberIdeal I (actualTangentCentreVariables d t) (j.natAdd d) b) ℓ ≤
      hilbertSamuelValue (actualDehomogenizedNormalFamilyIdeal d t
        (fun i => actualNormalHomogeneousPolynomial d t (q i) (g i)) j b) ℓ := by
  apply (hilbertSamuelValue_actual_axis_specialization (j.natAdd d) _ ℓ).trans
  exact hilbertSamuelValue_antitone_original_ideal _ _
    (actualDehomogenizedNormalFamilyIdeal_le_axis_normalized_image d t I g q hgI hgN j b) ℓ

/-- The same actual normalized values are bounded by the genuine translated canonical family, with no supplied HS certificate. -/
theorem hilbertSamuelValue_actual_normal_normalized_le_translated (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) {ι : Type*}
    (g : ι → HolGerm (ComplexModel (d+t))) (q : ι → ℕ)
    (hgI : ∀ i,g i ∈ I) (hgN : ∀ i,g i ∈ normalIdeal d t ^ q i)
    (j : Fin t) (b : Fin (d+t) → ℂ) (ℓ : ℕ) :
    hilbertSamuelValue (actualAnalyticNormalizedMemberIdeal I (actualTangentCentreVariables d t) (j.natAdd d) b) ℓ ≤
      hilbertSamuelValue (actualTranslatedNormalFamilyIdeal d t
        (fun i => actualNormalHomogeneousPolynomial d t (q i) (g i))
        (fun i => if i=j then 1 else b (i.natAdd d))) ℓ := by
  rw [← hilbertSamuelValue_dehomogenizedNormalFamily_eq_translated d t
    (fun i => actualNormalHomogeneousPolynomial d t (q i) (g i)) q
      (fun i => actualNormalHomogeneousPolynomial_isHomogeneous d t (q i) (g i)) j b ℓ]
  exact hilbertSamuelValue_actual_normal_normalized_le_dehomogenized d t I g q hgI hgN j b ℓ

end
end Hironaka.HironakaActualNormalAxisDehomogenization
