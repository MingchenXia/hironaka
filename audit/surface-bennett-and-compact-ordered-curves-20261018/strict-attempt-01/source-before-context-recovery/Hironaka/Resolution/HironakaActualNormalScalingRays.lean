/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualNormalUnitAnalyticCoefficients
import Hironaka.Support.GenuineAmbientJetAlgEquivExact

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualNormalScalingRays
noncomputable section
open HolGerm OkaRelationSheaf HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaHolomorphicJetMonomialSpan HironakaHolomorphicPointJets HironakaHolomorphicJetChartInvariance
  HironakaSmoothCentreRealDomainActualAmbientHS

/-- The actual continuous complex linear map fixes the tangent block and scales the normal block. -/
def actualNormalScale (d t : ℕ) (c : ℂ) : ComplexModel (d+t) →L[ℂ] ComplexModel (d+t) :=
  (tangentInclusion d t).comp (tangentProjection d t)+
    c • (ContinuousLinearMap.id ℂ _-(tangentInclusion d t).comp (tangentProjection d t))

theorem actualNormalScale_tangent (d t : ℕ) (c : ℂ) (z : ComplexModel (d+t)) (i : Fin d) :
    actualNormalScale d t c z (i.castAdd t)=z (i.castAdd t) := by
  simp [actualNormalScale]

theorem actualNormalScale_normal (d t : ℕ) (c : ℂ) (z : ComplexModel (d+t)) (i : Fin t) :
    actualNormalScale d t c z (i.natAdd d)=c*z (i.natAdd d) := by
  simp [actualNormalScale,smul_eq_mul]

theorem tangentProjection_actualNormalScale (d t : ℕ) (c : ℂ) (z : ComplexModel (d+t)) :
    tangentProjection d t (actualNormalScale d t c z)=tangentProjection d t z := by
  ext i
  exact actualNormalScale_tangent d t c z i

/-- A true nonzero partial-normal scaling has its actual inverse, with both tangent and normal blocks retained. -/
def actualNormalScaleLinearEquiv (d t : ℕ) (c : ℂ) (hc : c ≠ 0) :
    ComplexModel (d+t) ≃L[ℂ] ComplexModel (d+t) where
  toFun := actualNormalScale d t c
  invFun := actualNormalScale d t c⁻¹
  map_add' := map_add _
  map_smul' r z := (actualNormalScale d t c).map_smul r z
  left_inv z := by
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [actualNormalScale_tangent]
    · simp [actualNormalScale_normal,hc]
  right_inv z := by
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [actualNormalScale_tangent]
    · simp [actualNormalScale_normal,hc]
  continuous_toFun := (actualNormalScale d t c).continuous
  continuous_invFun := (actualNormalScale d t c⁻¹).continuous

/-- Actual original pullback along the genuine continuous linear equivalence preserves the entire complex germ algebra. -/
def actualNormalScaleGermEquiv (d t : ℕ) (c : ℂ) (hc : c ≠ 0) :
    HolGerm (ComplexModel (d+t)) ≃ₐ[ℂ] HolGerm (ComplexModel (d+t)) where
  toRingEquiv := HolGerm.comapEquiv (actualNormalScaleLinearEquiv d t c hc)
  commutes' _ := rfl

theorem hilbertSamuelValue_actualNormalScale (d t : ℕ) (c : ℂ) (hc : c ≠ 0)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (ℓ : ℕ) :
    hilbertSamuelValue (Ideal.map (actualNormalScaleGermEquiv d t c hc).toRingEquiv.toRingHom I) ℓ=
      hilbertSamuelValue I ℓ :=
  actualAmbientHS_eq_of_genuineAlgEquiv (actualNormalScaleGermEquiv d t c hc) I ℓ

/-- ALL original tangent germs are fixed, by the actual whole projection identity. -/
theorem actualNormalScaleGermEquiv_tangentPullback (d t : ℕ) (c : ℂ) (hc : c ≠ 0)
    (a : HolGerm (ComplexModel d)) :
    actualNormalScaleGermEquiv d t c hc (tangentPullback d t a)=tangentPullback d t a := by
  induction a using HolGerm.induction_on with
  | h f hf =>
    simp only [tangentPullback,compAlgHom_mk]
    change HolGerm.comapEquiv (actualNormalScaleLinearEquiv d t c hc) (HolGerm.mk _ _)=_
    rw [HolGerm.comapEquiv_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => congrArg f (tangentProjection_actualNormalScale d t c z)

/-- Each actual original normal coordinate scales by the true scalar, with the original complex constant action. -/
theorem actualNormalScaleGermEquiv_normalCoordinate (d t : ℕ) (c : ℂ) (hc : c ≠ 0) (i : Fin t) :
    actualNormalScaleGermEquiv d t c hc (normalCoordinate d t i)=
      algebraMap ℂ (HolGerm (ComplexModel (d+t))) c*normalCoordinate d t i := by
  let hi : HolAt (fun z : ComplexModel (d+t) => z (i.natAdd d)) 0 :=
    Eventually.of_forall fun _ => (EuclideanSpace.proj (i.natAdd d) : ComplexModel (d+t) →L[ℂ] ℂ).differentiableAt
  change HolGerm.comapEquiv (actualNormalScaleLinearEquiv d t c hc)
    (HolGerm.mk (fun z => z (i.natAdd d)) hi)=
      HolGerm.mk (fun _ => c) (eventually_differentiableAt_const c)*HolGerm.mk _ hi
  rw [HolGerm.comapEquiv_mk,← HolGerm.mk_mul]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun z => actualNormalScale_normal d t c z i

/-- Genuine finite polynomial translation in the normal block only, with unchanged entire analytic tangent coefficients. -/
def actualTranslatedNormalPolynomialEval (d t : ℕ) (p : Fin t → ℂ) :
    MvPolynomial (Fin t) (HolGerm (ComplexModel d)) →+* HolGerm (ComplexModel (d+t)) :=
  MvPolynomial.eval₂Hom (tangentPullback d t).toRingHom
    (fun i => normalCoordinate d t i+algebraMap ℂ (HolGerm (ComplexModel (d+t))) (p i))

private theorem homogeneous_eval₂_scaled {R S : Type*} [CommRing R] [CommRing S] {t : ℕ}
    (f : R →+* S) (P : MvPolynomial (Fin t) R) (q : ℕ) (hP : P.IsHomogeneous q)
    (x : Fin t → S) (c : S) :
    MvPolynomial.eval₂ f (fun i => c*x i) P=c^q*MvPolynomial.eval₂ f x P := by
  change MvPolynomial.eval₂Hom f (fun i => c*x i) P=c^q*MvPolynomial.eval₂Hom f x P
  rw [← P.support_sum_monomial_coeff,map_sum,map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [MvPolynomial.eval₂Hom_monomial,Finsupp.prod,mul_pow,
    Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
  rw [← hP.degree_eq_sum_deg_support ha]
  ac_rfl

/-- Finite normal homogeneity gives the genuine original scalar factor, even for entire analytic tangent coefficients. -/
theorem actualNormalScaleGermEquiv_translatedPolynomial (d t : ℕ) (p : Fin t → ℂ)
    (c : ℂ) (hc : c ≠ 0) (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d)))
    (q : ℕ) (hP : P.IsHomogeneous q) :
    actualNormalScaleGermEquiv d t c hc (actualTranslatedNormalPolynomialEval d t (c • p) P)=
      (algebraMap ℂ (HolGerm (ComplexModel (d+t))) c)^q*actualTranslatedNormalPolynomialEval d t p P := by
  let E := actualNormalScaleGermEquiv d t c hc
  change E.toRingEquiv.toRingHom (MvPolynomial.eval₂ (tangentPullback d t).toRingHom
    (fun i => normalCoordinate d t i+algebraMap ℂ _ ((c • p) i)) P)=_
  rw [MvPolynomial.hom_eval₂]
  have he : E.toRingEquiv.toRingHom.comp (tangentPullback d t).toRingHom=(tangentPullback d t).toRingHom := by
    apply RingHom.ext
    intro a
    exact actualNormalScaleGermEquiv_tangentPullback d t c hc a
  rw [he]
  change MvPolynomial.eval₂ (tangentPullback d t).toRingHom
    (fun i => E (normalCoordinate d t i+algebraMap ℂ (HolGerm (ComplexModel (d+t))) ((c • p) i))) P=_
  have hx : (fun i => E (normalCoordinate d t i+algebraMap ℂ (HolGerm (ComplexModel (d+t))) ((c • p) i)))=
      (fun i => algebraMap ℂ (HolGerm (ComplexModel (d+t))) c*
        (normalCoordinate d t i+algebraMap ℂ (HolGerm (ComplexModel (d+t))) (p i))) := by
    funext i
    dsimp only [E]
    simp only [map_add,actualNormalScaleGermEquiv_normalCoordinate,AlgEquiv.commutes,Pi.smul_apply,smul_eq_mul]
    rw [map_mul,mul_add]
  rw [hx,homogeneous_eval₂_scaled _ P q hP]
  rfl

/-- The whole actual translated ideal of the given finite normal-homogeneous polynomial family. -/
def actualTranslatedNormalFamilyIdeal (d t : ℕ) {ι : Type*}
    (P : ι → MvPolynomial (Fin t) (HolGerm (ComplexModel d))) (p : Fin t → ℂ) :
    Ideal (HolGerm (ComplexModel (d+t))) :=
  Ideal.span (range fun i => actualTranslatedNormalPolynomialEval d t p (P i))

/-- Genuine nonzero scalar factors and their true inverse constant germs prove BOTH entire ideal image directions. -/
theorem map_actualNormalScale_translatedFamily (d t : ℕ) {ι : Type*}
    (P : ι → MvPolynomial (Fin t) (HolGerm (ComplexModel d))) (q : ι → ℕ)
    (hP : ∀ i, (P i).IsHomogeneous (q i)) (p : Fin t → ℂ) (c : ℂ) (hc : c ≠ 0) :
    Ideal.map (actualNormalScaleGermEquiv d t c hc).toRingEquiv.toRingHom
      (actualTranslatedNormalFamilyIdeal d t P (c • p))=actualTranslatedNormalFamilyIdeal d t P p := by
  rw [actualTranslatedNormalFamilyIdeal,Ideal.map_span,← Set.range_comp]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro g ⟨i,rfl⟩
    change actualNormalScaleGermEquiv d t c hc (actualTranslatedNormalPolynomialEval d t (c • p) (P i)) ∈ _
    rw [actualNormalScaleGermEquiv_translatedPolynomial d t p c hc _ (q i) (hP i)]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i,rfl⟩)
  · apply Ideal.span_le.mpr
    rintro g ⟨i,rfl⟩
    have hg : actualNormalScaleGermEquiv d t c hc (actualTranslatedNormalPolynomialEval d t (c • p) (P i)) ∈
        Ideal.span (range fun j => actualNormalScaleGermEquiv d t c hc
          (actualTranslatedNormalPolynomialEval d t (c • p) (P j))) := Ideal.subset_span ⟨i,rfl⟩
    rw [actualNormalScaleGermEquiv_translatedPolynomial d t p c hc _ (q i) (hP i)] at hg
    have hh := Ideal.mul_mem_left _ (algebraMap ℂ (HolGerm (ComplexModel (d+t))) ((c^(q i))⁻¹)) hg
    rw [← map_pow,← mul_assoc,← map_mul,inv_mul_cancel₀ (pow_ne_zero _ hc),map_one,one_mul] at hh
    exact hh

/-- Every original whole HS order is constant on the genuine nonzero translated normal ray. -/
theorem actualTranslatedNormalFamily_nonzero_ray_hs (d t : ℕ) {ι : Type*}
    (P : ι → MvPolynomial (Fin t) (HolGerm (ComplexModel d))) (q : ι → ℕ)
    (hP : ∀ i, (P i).IsHomogeneous (q i)) (p : Fin t → ℂ) (c : ℂ) (hc : c ≠ 0) (ℓ : ℕ) :
    hilbertSamuelValue (actualTranslatedNormalFamilyIdeal d t P (c • p)) ℓ=
      hilbertSamuelValue (actualTranslatedNormalFamilyIdeal d t P p) ℓ := by
  have h := hilbertSamuelValue_actualNormalScale d t c hc (actualTranslatedNormalFamilyIdeal d t P (c • p)) ℓ
  rw [map_actualNormalScale_translatedFamily d t P q hP p c hc] at h
  exact h.symm

end
end Hironaka.HironakaActualNormalScalingRays
