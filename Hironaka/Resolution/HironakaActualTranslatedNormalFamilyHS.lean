/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualNormalScalingRays
import Hironaka.Resolution.HironakaActualHolomorphicFibreHS

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualTranslatedNormalFamilyHS
noncomputable section
open HolGerm OkaRelationSheaf HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaHolomorphicJetMonomialSpan HironakaHolomorphicPointJets HironakaHolomorphicJetChartInvariance
  HironakaActualNormalScalingRays HironakaActualHolomorphicFibreHS

/-- All supported coefficient germs have genuine representatives on one internally chosen actual open domain. -/
theorem exists_actual_polynomial_coefficient_domain (d t s : ℕ)
    (P : Fin s → MvPolynomial (Fin t) (HolGerm (ComplexModel d))) :
    ∃ (U : Set (ComplexModel d)), IsOpen U ∧ (0 : ComplexModel d) ∈ U ∧
      ∃ (a : Fin s → (Fin t →₀ ℕ) → ComplexModel d → ℂ) (ha : ∀ i γ, HolAt (a i γ) 0),
        (∀ i γ, γ ∈ (P i).support → DifferentiableOn ℂ (a i γ) U) ∧
        ∀ i γ, MvPolynomial.coeff γ (P i)=HolGerm.mk (a i γ) (ha i γ) := by
  choose a ha he using fun i γ => HolGerm.exists_eq_mk (MvPolynomial.coeff γ (P i))
  let κ := Σ i : Fin s, {γ // γ ∈ (P i).support}
  have hnear : ∀ᶠ u in 𝓝 (0 : ComplexModel d),
      ∀ k : κ, DifferentiableAt ℂ (a k.1 k.2.val) u :=
    eventually_all.mpr fun k => ha k.1 k.2.val
  obtain ⟨U,hUf,hU,h0⟩ := eventually_nhds_iff.mp hnear
  refine ⟨U,hU,h0,a,ha,?_,he⟩
  intro i γ hγ u hu
  exact ((hUf u hu) ⟨i,⟨γ,hγ⟩⟩).differentiableWithinAt

private theorem holAt_finset_prod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} (S : Finset ι) (f : ι → E → ℂ) (hf : ∀ i, HolAt (f i) 0) :
    HolAt (fun z => ∏ i ∈ S, f i z) 0 := by
  induction S using Finset.induction_on with
  | empty => exact eventually_differentiableAt_one
  | @insert i S hi ih =>
    simpa only [Finset.prod_insert hi] using eventually_differentiableAt_mul (hf i) ih

private theorem mk_finset_prod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} (S : Finset ι) (f : ι → E → ℂ) (hf : ∀ i, HolAt (f i) 0) :
    HolGerm.mk (fun z => ∏ i ∈ S, f i z) (holAt_finset_prod S f hf)=
      ∏ i ∈ S, HolGerm.mk (f i) (hf i) := by
  induction S using Finset.induction_on with
  | empty => rfl
  | @insert i S hi ih =>
    simp only [Finset.prod_insert hi]
    change HolGerm.mk (fun z => f i z*(∏ j ∈ S, f j z))
      (eventually_differentiableAt_mul (hf i) (holAt_finset_prod S f hf))=_
    rw [HolGerm.mk_mul _ _ (hf i) (holAt_finset_prod S f hf),ih]

private theorem normal_translate_holAt (d t : ℕ) (p : Fin t → ℂ) (i : Fin t) :
    HolAt (fun z : ComplexModel (d+t) => z (i.natAdd d)+p i) 0 :=
  Eventually.of_forall fun _ =>
    (EuclideanSpace.proj (i.natAdd d) : ComplexModel (d+t) →L[ℂ] ℂ).differentiableAt.add
      (differentiableAt_const (p i))

private theorem normal_ray_monomial_holAt (d t : ℕ) (p : Fin t → ℂ)
    (a : (Fin t →₀ ℕ) → ComplexModel d → ℂ) (ha : ∀ γ, HolAt (a γ) 0) (γ : Fin t →₀ ℕ) :
    HolAt (fun z : ComplexModel (d+t) => a γ (tangentProjection d t z)*
      γ.prod (fun j k => (z (j.natAdd d)+p j)^k)) 0 :=
  eventually_differentiableAt_mul (eventually_differentiableAt_comp_clm (tangentProjection d t) (ha γ))
    (holAt_finset_prod γ.support (fun j (z : ComplexModel (d+t)) => (z (j.natAdd d)+p j)^(γ j))
      (fun j => eventually_differentiableAt_pow (normal_translate_holAt d t p j) (γ j)))

private theorem normal_ray_polynomial_mk (d t : ℕ) (p : Fin t → ℂ)
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d)))
    (a : (Fin t →₀ ℕ) → ComplexModel d → ℂ) (ha : ∀ γ, HolAt (a γ) 0)
    (he : ∀ γ, MvPolynomial.coeff γ P=HolGerm.mk (a γ) (ha γ)) :
    actualTranslatedNormalPolynomialEval d t p P=
      HolGerm.mk (fun z : ComplexModel (d+t) => ∑ γ ∈ P.support,
        a γ (tangentProjection d t z)*γ.prod (fun j k => (z (j.natAdd d)+p j)^k))
        (eventually_differentiableAt_sum P.support (normal_ray_monomial_holAt d t p a ha)) := by
  rw [HolGerm.mk_sum P.support _ (normal_ray_monomial_holAt d t p a ha)]
  conv_lhs => rw [← P.support_sum_monomial_coeff,map_sum]
  apply Finset.sum_congr rfl
  intro γ hγ
  simp only [actualTranslatedNormalPolynomialEval,MvPolynomial.eval₂Hom_monomial]
  let ht := eventually_differentiableAt_comp_clm (tangentProjection d t) (ha γ)
  let hx (j : Fin t) := eventually_differentiableAt_pow (normal_translate_holAt d t p j) (γ j)
  change (tangentPullback d t).toRingHom (MvPolynomial.coeff γ P)*
      (∏ j ∈ γ.support, (normalCoordinate d t j+algebraMap ℂ _ (p j))^(γ j))=
    HolGerm.mk (fun z : ComplexModel (d+t) => a γ (tangentProjection d t z)*
      ∏ j ∈ γ.support, (z (j.natAdd d)+p j)^(γ j))
      (eventually_differentiableAt_mul ht (holAt_finset_prod γ.support _ hx))
  change (tangentPullback d t).toRingHom (MvPolynomial.coeff γ P)*
      (∏ j ∈ γ.support, (normalCoordinate d t j+algebraMap ℂ _ (p j))^(γ j))=
    HolGerm.mk (fun z => a γ (tangentProjection d t z)) ht*
      HolGerm.mk (fun z : ComplexModel (d+t) => ∏ j ∈ γ.support,
        (z (j.natAdd d)+p j)^(γ j)) (holAt_finset_prod γ.support _ hx)
  rw [mk_finset_prod γ.support (fun j (z : ComplexModel (d+t)) =>
    (z (j.natAdd d)+p j)^(γ j)) hx]
  apply congrArg₂ (fun x y : HolGerm (ComplexModel (d+t)) => x*y)
  · rw [he γ]
    change tangentPullback d t (HolGerm.mk (a γ) (ha γ))=_
    rw [tangentPullback,compAlgHom_mk]
    rfl
  · apply Finset.prod_congr rfl
    intro j hj
    rw [HolGerm.mk_pow _ (normal_translate_holAt d t p j) (γ j)]
    rfl

/-- Only actual finite polynomial coefficients are represented; one real domain contains the entire parameter axis. -/
theorem exists_actual_joint_normal_ray_family (d t s : ℕ)
    (P : Fin s → MvPolynomial (Fin t) (HolGerm (ComplexModel d))) (p : Fin t → ℂ) :
    ∃ (D : Set (ComplexModel 1 × ComplexModel (d+t))) (hD : IsOpen D)
      (G : Fin s → ComplexModel 1 × ComplexModel (d+t) → ℂ)
      (hG : ∀ i, DifferentiableOn ℂ (G i) D),
      (∀ c : ComplexModel 1, (c,0) ∈ D) ∧
      ∀ (c : ComplexModel 1) (hc : (c,0) ∈ D),
        actualFibreIdeal hD G hG c hc=actualTranslatedNormalFamilyIdeal d t P ((c 0) • p) := by
  obtain ⟨U,hU,h0,a,ha,hcoeff,he⟩ := exists_actual_polynomial_coefficient_domain d t s P
  let D : Set (ComplexModel 1 × ComplexModel (d+t)) :=
    {v | tangentProjection d t v.2 ∈ U}
  have hD : IsOpen D := hU.preimage ((tangentProjection d t).continuous.comp continuous_snd)
  let G (i : Fin s) (v : ComplexModel 1 × ComplexModel (d+t)) : ℂ :=
    ∑ γ ∈ (P i).support, a i γ (tangentProjection d t v.2)*
      γ.prod (fun j k => (v.2 (j.natAdd d)+v.1 0*p j)^k)
  have hG : ∀ i, DifferentiableOn ℂ (G i) D := by
    intro i v hv
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.fun_sum
    intro γ hγ
    have hc : DifferentiableAt ℂ
        (fun w : ComplexModel 1 × ComplexModel (d+t) => a i γ (tangentProjection d t w.2)) v :=
      ((hcoeff i γ hγ).differentiableAt (hU.mem_nhds hv)).comp v
        ((tangentProjection d t).differentiableAt.comp v differentiableAt_snd)
    apply hc.mul
    change DifferentiableAt ℂ (fun w : ComplexModel 1 × ComplexModel (d+t) =>
      ∏ j ∈ γ.support, (w.2 (j.natAdd d)+w.1 0*p j)^(γ j)) v
    apply HasFDerivAt.differentiableAt
    apply HasFDerivAt.finsetProd
    intro j hj
    exact (((((EuclideanSpace.proj (j.natAdd d) : ComplexModel (d+t) →L[ℂ] ℂ).differentiableAt.comp v
      differentiableAt_snd).add
        (((EuclideanSpace.proj (0 : Fin 1) : ComplexModel 1 →L[ℂ] ℂ).differentiableAt.comp v
          differentiableAt_fst).mul (differentiableAt_const (p j)))).fun_pow (γ j))).hasFDerivAt
  refine ⟨D,hD,G,hG,?_,?_⟩
  · intro c
    change tangentProjection d t 0 ∈ U
    simpa only [map_zero] using h0
  · intro c hc
    rw [actualFibreIdeal_eq_original_span,actualTranslatedNormalFamilyIdeal]
    apply congrArg Ideal.span
    apply congrArg Set.range
    funext i
    rw [normal_ray_polynomial_mk d t ((c 0) • p) (P i) (a i) (ha i) (he i)]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => by simp only [G,Pi.smul_apply,smul_eq_mul]

/-- The actual entire translated normal ideal has every ORIGINAL HS value bounded by its unshifted ray origin. -/
theorem hilbertSamuelValue_actual_translated_normal_le (d t s : ℕ)
    (P : Fin s → MvPolynomial (Fin t) (HolGerm (ComplexModel d))) (q : Fin s → ℕ)
    (hP : ∀ i, (P i).IsHomogeneous (q i)) (p : Fin t → ℂ) (ℓ : ℕ) :
    hilbertSamuelValue (actualTranslatedNormalFamilyIdeal d t P p) ℓ ≤
      hilbertSamuelValue (actualTranslatedNormalFamilyIdeal d t P 0) ℓ := by
  obtain ⟨D,hD,G,hG,haxis,hfibre⟩ := exists_actual_joint_normal_ray_family d t s P p
  let C (c : ℂ) : ComplexModel 1 := c • (EuclideanSpace.basisFun (Fin 1) ℂ) 0
  have hC : Continuous C := continuous_id.smul continuous_const
  have hcoord (c : ℂ) : C c 0=c := by simp [C]
  let J (c : ℂ) := actualFibreIdeal hD G hG (C c) (haxis (C c))
  have hdict (c : ℂ) : J c=actualTranslatedNormalFamilyIdeal d t P (c • p) := by
    have h := hfibre (C c) (haxis (C c))
    rw [hcoord] at h
    exact h
  let R : ℂ → (⊤ : TopologicalSpace.Opens (ComplexModel 1)) := fun c => ⟨C c,mem_univ _⟩
  have hR : Continuous R := Continuous.subtype_mk hC _
  have hclosed : IsClosed {c : ℂ | hilbertSamuelValue (actualTranslatedNormalFamilyIdeal d t P p) ℓ ≤
      hilbertSamuelValue (J c) ℓ} :=
    (isClosed_actualFibreHS_superlevel hD G hG ⊤ (fun c _ => haxis c) ℓ
      (hilbertSamuelValue (actualTranslatedNormalFamilyIdeal d t P p) ℓ)).preimage hR
  have hsub : ({(0 : ℂ)}ᶜ : Set ℂ) ⊆
      {c : ℂ | hilbertSamuelValue (actualTranslatedNormalFamilyIdeal d t P p) ℓ ≤ hilbertSamuelValue (J c) ℓ} := by
    intro c hc
    have hc0 : c ≠ 0 := by simpa using hc
    change hilbertSamuelValue (actualTranslatedNormalFamilyIdeal d t P p) ℓ ≤ hilbertSamuelValue (J c) ℓ
    rw [hdict c,actualTranslatedNormalFamily_nonzero_ray_hs d t P q hP p c hc0]
  have hz := closure_minimal hsub hclosed ((dense_compl_singleton (0 : ℂ)) 0)
  change hilbertSamuelValue (actualTranslatedNormalFamilyIdeal d t P p) ℓ ≤ hilbertSamuelValue (J 0) ℓ at hz
  rw [hdict 0,zero_smul] at hz
  exact hz

end
end Hironaka.HironakaActualTranslatedNormalFamilyHS
