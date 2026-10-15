/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaRelativeNormalGraphCentralPolynomialModel
import Hironaka.Resolution.HironakaRelativeNormalCoherentTranslatedJets
import Hironaka.Resolution.HironakaRelativeNormalHomogeneousAnalyticContraction

/-! Four complete prior mathematical proofs. Only actual coefficient FUNCTIONS
are affinely translated; no map of arbitrary origin germs to nearby germs. -/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaRelativeNormalNearbyPolynomialCoefficientGerms
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf OkaIdealOperations
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalAssociatedGraded HironakaRelativeNormalCoherentSaturation HironakaRelativeNormalAnalyticCoefficients
  HironakaRelativeNormalDeformationInitialRelations HironakaRelativeNormalDeformationSaturation
  HironakaRelativeNormalDeformationFiniteRelationsSpread
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalGraphCentralPolynomialModel
  HironakaRelativeNormalHomogeneousAnalyticContraction HironakaHolomorphicJetChartInvariance
open FiniteGermIdealPullbackGenerators RelativePrincipalizationSpan InvertibleIdealQuotient
attribute [local instance] MvPolynomial.gradedAlgebra

theorem actualCoefficientFunctionTranslation_holomorphic (d : ℕ)
    (a : ComplexModel d) (f : ComplexModel d → ℂ) (hf : HolAt f a) :
    HolAt (f ∘ actualAffineTranslation d a) 0 := by
  have ht : Tendsto (actualAffineTranslation d a) (𝓝 0) (𝓝 a) := by
    simpa only [actualAffineTranslation_zero] using
      (actualAffineTranslation_contMDiff d a).continuous.tendsto (0 : ComplexModel d)
  exact (ht.eventually hf).mono fun z hz =>
    hz.comp z ((differentiableAt_const a).add differentiableAt_id)

theorem actualAmbientBaseTranslation_tangent (d t : ℕ) (a : ComplexModel d)
    (z : ComplexModel (d+t)) :
    tangentProjection d t (actualAffineTranslation (d+t) (tangentInclusion d t a) z) =
      actualAffineTranslation d a (tangentProjection d t z) := by
  simp only [actualAffineTranslation,map_add,tangentProjection_tangentInclusion]

theorem actualAmbientBaseTranslation_normal (d t : ℕ) (a : ComplexModel d)
    (z : ComplexModel (d+t)) (i : Fin t) :
    actualAffineTranslation (d+t) (tangentInclusion d t a) z (i.natAdd d) = z (i.natAdd d) := by
  change (EuclideanSpace.proj (i.natAdd d) : ComplexModel (d+t) →L[ℂ] ℂ)
    (tangentInclusion d t a+z) = _
  rw [map_add]
  change tangentInclusion d t a (i.natAdd d)+z (i.natAdd d) = z (i.natAdd d)
  rw [tangentInclusion_normal,zero_add]


def actualNearbyCoefficientPolynomial (d t : ℕ)
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) (a : ComplexModel d)
    (hcoeff : ∀ α, HolAt (actualCoefficientRepresentative (P.coeff α)) a) :
    MvPolynomial (Fin t) (HolGerm (ComplexModel d)) := by
  classical
  exact ∑ α ∈ P.support, MvPolynomial.monomial α
    (HolGerm.mk (actualCoefficientRepresentative (P.coeff α) ∘ actualAffineTranslation d a)
      (actualCoefficientFunctionTranslation_holomorphic d a _ (hcoeff α)))

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
theorem actualNearbyCoefficientPolynomial_coeff (d t : ℕ)
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) (a : ComplexModel d)
    (hcoeff : ∀ α, HolAt (actualCoefficientRepresentative (P.coeff α)) a)
    (α : Fin t →₀ ℕ) :
    (actualNearbyCoefficientPolynomial d t P a hcoeff).coeff α =
      HolGerm.mk (actualCoefficientRepresentative (P.coeff α) ∘ actualAffineTranslation d a)
        (actualCoefficientFunctionTranslation_holomorphic d a _ (hcoeff α)) := by
  classical
  by_cases hα : α ∈ P.support
  · simp [actualNearbyCoefficientPolynomial,MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial,hα]
  · have hz : P.coeff α = 0 := MvPolynomial.notMem_support_iff.mp hα
    have hzero : HolGerm.mk (actualCoefficientRepresentative (P.coeff α) ∘ actualAffineTranslation d a)
        (actualCoefficientFunctionTranslation_holomorphic d a _ (hcoeff α)) = 0 := by
      apply Subtype.ext
      change (Germ.coeRingHom (𝓝 (0 : ComplexModel d)))
        (actualCoefficientRepresentative (P.coeff α) ∘ actualAffineTranslation d a) = 0
      rw [hz,actualCoefficientRepresentative_zero]
      exact map_zero (Germ.coeRingHom (𝓝 (0 : ComplexModel d)))
    simp [actualNearbyCoefficientPolynomial,MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial,hα,hzero]

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
theorem actualNearbyCoefficientPolynomial_support_subset (d t : ℕ)
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) (a : ComplexModel d)
    (hcoeff : ∀ α, HolAt (actualCoefficientRepresentative (P.coeff α)) a) :
    (actualNearbyCoefficientPolynomial d t P a hcoeff).support ⊆ P.support := by
  intro α hα
  by_contra hn
  apply MvPolynomial.mem_support_iff.mp hα
  rw [actualNearbyCoefficientPolynomial_coeff]
  apply Subtype.ext
  change (Germ.coeRingHom (𝓝 (0 : ComplexModel d)))
    (actualCoefficientRepresentative (P.coeff α) ∘ actualAffineTranslation d a) = 0
  rw [MvPolynomial.notMem_support_iff.mp hn,actualCoefficientRepresentative_zero]
  exact map_zero (Germ.coeRingHom (𝓝 (0 : ComplexModel d)))

theorem actualNearbyCoefficientPolynomial_homogeneous (d t : ℕ)
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) (a : ComplexModel d)
    (hcoeff : ∀ α, HolAt (actualCoefficientRepresentative (P.coeff α)) a)
    {q : ℕ} (hP : P.IsHomogeneous q) :
    (actualNearbyCoefficientPolynomial d t P a hcoeff).IsHomogeneous q := by
  intro α hα
  exact hP (MvPolynomial.mem_support_iff.mp
    (actualNearbyCoefficientPolynomial_support_subset d t P a hcoeff (MvPolynomial.mem_support_iff.mpr hα)))


theorem actualNormalMonomialFunctionTranslation (d t : ℕ) (α : Fin t →₀ ℕ)
    (a : ComplexModel d) (z : ComplexModel (d+t)) :
    actualNormalMonomialFunction d t α (actualAffineTranslation (d+t) (tangentInclusion d t a) z) =
      actualNormalMonomialFunction d t α z := by
  classical
  unfold actualNormalMonomialFunction
  apply Finset.prod_congr rfl
  intro i _
  rw [actualAmbientBaseTranslation_normal]

theorem actualNormalPolynomialFunctionTranslation_dictionary (d t : ℕ)
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) (a : ComplexModel d)
    (z : ComplexModel (d+t)) :
    actualNormalPolynomialFunction d t P (actualAffineTranslation (d+t) (tangentInclusion d t a) z) =
      ∑ α ∈ P.support,
        actualCoefficientRepresentative (P.coeff α) (actualAffineTranslation d a (tangentProjection d t z)) *
          actualNormalMonomialFunction d t α z := by
  classical
  unfold actualNormalPolynomialFunction
  apply Finset.sum_congr rfl
  intro α _
  rw [actualAmbientBaseTranslation_tangent,actualNormalMonomialFunctionTranslation]

theorem actualNormalPolynomialFunctionTranslation_holomorphic (d t : ℕ)
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) (a : ComplexModel d)
    (hcoeff : ∀ α, HolAt (actualCoefficientRepresentative (P.coeff α)) a) :
    HolAt (actualNormalPolynomialFunction d t P ∘ actualAffineTranslation (d+t) (tangentInclusion d t a)) 0 := by
  classical
  have he : actualNormalPolynomialFunction d t P ∘ actualAffineTranslation (d+t) (tangentInclusion d t a) =
      fun z => ∑ α ∈ P.support,
        actualCoefficientRepresentative (P.coeff α) (actualAffineTranslation d a (tangentProjection d t z)) *
          actualNormalMonomialFunction d t α z := funext (actualNormalPolynomialFunctionTranslation_dictionary d t P a)
  rw [he]
  apply eventually_differentiableAt_sum P.support
  intro α
  have hb : HolAt ((actualCoefficientRepresentative (P.coeff α) ∘ actualAffineTranslation d a) ∘ tangentProjection d t) 0 :=
    eventually_differentiableAt_comp_clm (tangentProjection d t)
      (actualCoefficientFunctionTranslation_holomorphic d a _ (hcoeff α))
  exact hb.mul (Eventually.of_forall (actualNormalMonomialFunction_differentiableAt d t α))

theorem actualNormalPolynomialFunctionTranslation_whole_germ (d t : ℕ)
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) (a : ComplexModel d)
    (hcoeff : ∀ α, HolAt (actualCoefficientRepresentative (P.coeff α)) a) :
    HolGerm.mk (actualNormalPolynomialFunction d t P ∘ actualAffineTranslation (d+t) (tangentInclusion d t a))
      (actualNormalPolynomialFunctionTranslation_holomorphic d t P a hcoeff) =
        normalPolynomialEval d t (actualNearbyCoefficientPolynomial d t P a hcoeff) := by
  classical
  let c := fun α : Fin t →₀ ℕ => actualCoefficientRepresentative (P.coeff α) ∘ actualAffineTranslation d a
  have hc (α : Fin t →₀ ℕ) : HolAt (c α) 0 :=
    actualCoefficientFunctionTranslation_holomorphic d a _ (hcoeff α)
  let f := fun α : Fin t →₀ ℕ => fun z : ComplexModel (d+t) =>
    c α (tangentProjection d t z) * actualNormalMonomialFunction d t α z
  have hf (α : Fin t →₀ ℕ) : HolAt (f α) 0 := by
    have hb : HolAt (c α ∘ tangentProjection d t) 0 :=
      eventually_differentiableAt_comp_clm (tangentProjection d t) (hc α)
    exact hb.mul (Eventually.of_forall (actualNormalMonomialFunction_differentiableAt d t α))
  have he : actualNormalPolynomialFunction d t P ∘ actualAffineTranslation (d+t) (tangentInclusion d t a) =
      fun z => ∑ α ∈ P.support, f α z := funext (actualNormalPolynomialFunctionTranslation_dictionary d t P a)
  have hg : HolGerm.mk (actualNormalPolynomialFunction d t P ∘ actualAffineTranslation (d+t) (tangentInclusion d t a))
      (actualNormalPolynomialFunctionTranslation_holomorphic d t P a hcoeff) =
        HolGerm.mk (fun z => ∑ α ∈ P.support, f α z)
          (eventually_differentiableAt_sum P.support hf) := by
    apply Subtype.ext
    exact congrArg (Germ.coeRingHom (𝓝 (0 : ComplexModel (d+t)))) he
  rw [hg,HolGerm.mk_sum P.support f hf]
  rw [actualNearbyCoefficientPolynomial,map_sum]
  apply Finset.sum_congr rfl
  intro α _
  change HolGerm.mk ((c α ∘ tangentProjection d t)*actualNormalMonomialFunction d t α) _ = _
  rw [HolGerm.mk_mul' _ _ (eventually_differentiableAt_comp_clm (tangentProjection d t) (hc α))
      (Eventually.of_forall (actualNormalMonomialFunction_differentiableAt d t α)),
    actualNormalMonomialFunction_whole_germ,normalPolynomialEval_monomial]
  congr 1


private theorem actual_finite_span_reindex {n : ℕ} {ι : Type*} [Fintype ι]
    {s : ℕ} (e : Fin s ≃ ι) (F : ι → ComplexModel n → ℂ) (y : ComplexModel n)
    (g : ComplexModel n → ℂ) :
    InSpanAt (fun j => F (e j)) y g ↔ InSpanAt F y g := by
  constructor
  · rintro ⟨hg,c,hc,he⟩
    refine ⟨hg,fun i => c (e.symm i),fun i => hc (e.symm i),?_⟩
    filter_upwards [he] with z hz
    rw [hz]
    exact Fintype.sum_equiv e _ _ (fun j => by simp only [Equiv.symm_apply_apply])
  · rintro ⟨hg,c,hc,he⟩
    refine ⟨hg,fun j => c (e j),fun j => hc (e j),?_⟩
    filter_upwards [he] with z hz
    rw [hz]
    exact (e.sum_comp (fun i => c i z*F i z)).symm

private theorem actual_fixed_translation_membership {n N : ℕ}
    (I : GermIdeal n (ComplexModel n)) (S : Fin N → ComplexModel n → ℂ)
    {U : Set (ComplexModel n)} (hU : IsOpen U)
    (hS : ∀ i, MDifferentiableOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (S i) U)
    (hgen : ∀ y ∈ U, ∀ f, I.mem y f ↔ IsInSpanAt (n := n) (· ∈ range S) y f)
    {a : ComplexModel n} (ha : a ∈ U) (f : ComplexModel n → ℂ) :
    (actualTranslatedOriginalSheaf I a).mem 0 f ↔
      IsInSpanAt (n := n) (· ∈ range fun i => S i ∘ actualAffineTranslation n a) 0 f := by
  apply mem_pullback_iff_of_finite_generation
    (Eventually.of_forall fun _ => (actualAffineTranslation_contMDiff n a).contMDiffAt)
  · intro i
    simpa only [actualAffineTranslation_zero] using holomorphicAt_of_mdifferentiableOn hU (hS i) ha
  · simpa only [actualAffineTranslation_zero] using hgen a ha

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
private theorem actual_translated_origin_ideal_from_fixed_functions {n N : ℕ}
    (I : GermIdeal n (ComplexModel n)) (S : Fin N → ComplexModel n → ℂ)
    {U : Set (ComplexModel n)} (hU : IsOpen U)
    (hS : ∀ i, MDifferentiableOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (S i) U)
    (hgen : ∀ y ∈ U, ∀ f, I.mem y f ↔ IsInSpanAt (n := n) (· ∈ range S) y f)
    {a : ComplexModel n} (ha : a ∈ U) (hhol : ∀ i, HolAt (S i ∘ actualAffineTranslation n a) 0) :
    originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I a) =
      Ideal.span (range fun i => HolGerm.mk (S i ∘ actualAffineTranslation n a) (hhol i)) := by
  classical
  have hdict : ∀ (f : ComplexModel n → ℂ) (hf : HolAt f 0),
      (actualTranslatedOriginalSheaf I a).mem 0 f ↔
        HolGerm.mk f hf ∈ Ideal.span (range fun i => HolGerm.mk (S i ∘ actualAffineTranslation n a) (hhol i)) := by
    intro f hf
    rw [actual_fixed_translation_membership I S hU hS hgen ha f]
    constructor
    · intro h
      obtain ⟨_,c,hc,he⟩ := CoherentIdealColon.isInSpanAt_range_iff.mp h
      exact (inSpanAt_zero_iff_mem_origin_span _ hhol hf).mp
        ⟨hf,c,fun i => (hc i).mono (fun _ hz => hz.differentiableAt),he⟩
    · intro h
      obtain ⟨hh,c,hc,he⟩ := (inSpanAt_zero_iff_mem_origin_span _ hhol hf).mpr h
      exact CoherentIdealColon.isInSpanAt_range_iff.mpr
        ⟨hh.mono (fun _ hz => hz.mdifferentiableAt),c,
          fun i => (hc i).mono (fun _ hz => hz.mdifferentiableAt),he⟩
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro g ⟨f,hf,hIf,rfl⟩
    exact (hdict f hf).mp hIf
  · apply Ideal.span_le.mpr
    rintro g ⟨i,rfl⟩
    apply Ideal.subset_span
    refine ⟨S i ∘ actualAffineTranslation n a,hhol i,?_,rfl⟩
    apply (actual_fixed_translation_membership I S hU hS hgen ha _).mpr
    exact CoherentIdealColon.isInSpanAt_range_self
      (fun j => (hhol j).mono (fun _ hz => hz.mdifferentiableAt)) i


attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
private theorem actual_function_span_holomorphic_dictionary {n m : ℕ}
    (S : Fin m → ComplexModel n → ℂ) (y : ComplexModel n) (g : ComplexModel n → ℂ) :
    InSpanAt S y g ↔ IsInSpanAt (n := n) (· ∈ range S) y g := by
  rw [CoherentIdealColon.isInSpanAt_range_iff]
  constructor
  · rintro ⟨hg,c,hc,he⟩
    exact ⟨hg.mono (fun _ h => h.mdifferentiableAt),c,
      fun i => (hc i).mono (fun _ h => h.mdifferentiableAt),he⟩
  · rintro ⟨hg,c,hc,he⟩
    exact ⟨hg.mono (fun _ h => h.differentiableAt),c,
      fun i => (hc i).mono (fun _ h => h.differentiableAt),he⟩

theorem exists_original_whole_translated_central_polynomial_model (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    let := tangentAlgebra d t
    ∃ N : ℕ, ∃ B : Set (ComplexModel d), IsOpen B ∧ 0 ∈ B ∧
      (originalDeformationCentralIdeal d t I N).IsCoherent ∧
      (∀ a ∈ B, ∀ q : ℕ, ∀ g,
        (originalDeformationColonIdeal d t I (N+q)).mem (deformationCentralInclusion d t (tangentInclusion d t a)) g ↔
          (originalDeformationColonIdeal d t I N).mem (deformationCentralInclusion d t (tangentInclusion d t a)) g) ∧
      ∃ hc : ∀ a ∈ B, ∀ P : ↥(actualOriginalRelationFamily d t I), ∀ α,
        HolAt (actualCoefficientRepresentative (P.val.coeff α)) a,
        ∀ a (ha : a ∈ B),
          let H := Ideal.span (range fun P : ↥(actualOriginalRelationFamily d t I) =>
            actualNearbyCoefficientPolynomial d t P.val a (hc a ha P))
          H.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin t) (HolGerm (ComplexModel d))) ∧
          originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
            (originalDeformationCentralIdeal d t I N) (tangentInclusion d t a)) =
              Ideal.map (normalPolynomialEval d t).toRingHom H ∧
          Ideal.comap (normalPolynomialEval d t).toRingHom
            (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
              (originalDeformationCentralIdeal d t I N) (tangentInclusion d t a))) = H := by
  classical
  let := tangentAlgebra d t
  obtain ⟨N,V,hV,h0V,hcent,hcoeff,hpoly,hdegree,_hfg,hcentral,hchain,_hpow,_hsat⟩ :=
    exists_original_whole_central_polynomial_model d t I hI
  let B := tangentInclusion d t ⁻¹' V
  have hB : IsOpen B := hV.preimage (tangentInclusion d t).continuous
  have h0B : (0 : ComplexModel d) ∈ B := by
    change tangentInclusion d t 0 ∈ V
    simpa only [map_zero] using h0V
  have hc : ∀ a ∈ B, ∀ P : ↥(actualOriginalRelationFamily d t I), ∀ α,
      HolAt (actualCoefficientRepresentative (P.val.coeff α)) a := by
    intro a ha P α
    have hbnhds : ∀ᶠ b in 𝓝 a, b ∈ B := hB.mem_nhds ha
    exact hbnhds.mono fun b hb => by
      simpa only [tangentProjection_tangentInclusion] using hcoeff P.val P.property α (tangentInclusion d t b) hb
  refine ⟨N,B,hB,h0B,hcent,fun a ha => hchain _ ha,hc,?_⟩
  intro a ha
  dsimp only
  let μ := ↥(actualOriginalRelationFamily d t I)
  let e : Fin (Fintype.card μ) ≃ μ := (Fintype.equivFin μ).symm
  let F : μ → ComplexModel (d+t) → ℂ := fun P => actualNormalPolynomialFunction d t P.val
  let S := fun i : Fin (Fintype.card μ) => F (e i)
  let H := Ideal.span (range fun P : μ => actualNearbyCoefficientPolynomial d t P.val a (hc a ha P))
  have hH : H.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin t) (HolGerm (ComplexModel d))) := by
    apply Ideal.homogeneous_span
    rintro P ⟨Q,rfl⟩
    obtain ⟨q,hq,_⟩ := hdegree Q.val Q.property
    exact ⟨q,actualNearbyCoefficientPolynomial_homogeneous d t Q.val a (hc a ha Q) hq⟩
  have hS : ∀ i, MDifferentiableOn 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ℂ) (S i) V := by
    intro i y hy
    exact (hpoly (e i).val (e i).property y hy).self_of_nhds.mdifferentiableAt.mdifferentiableWithinAt
  have hgen : ∀ y ∈ V, ∀ g,
      (originalDeformationCentralIdeal d t I N).mem y g ↔ IsInSpanAt (n := d+t) (· ∈ range S) y g := by
    intro y hy g
    exact (hcentral y hy g).symm.trans
      ((actual_finite_span_reindex e F y g).symm.trans (actual_function_span_holomorphic_dictionary S y g))
  have hhol (i : Fin (Fintype.card μ)) :
      HolAt (S i ∘ actualAffineTranslation (d+t) (tangentInclusion d t a)) 0 :=
    actualNormalPolynomialFunctionTranslation_holomorphic d t (e i).val a (hc a ha (e i))
  have hwhole := actual_translated_origin_ideal_from_fixed_functions
    (originalDeformationCentralIdeal d t I N) S hV hS hgen ha hhol
  have heq : originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
      (originalDeformationCentralIdeal d t I N) (tangentInclusion d t a)) =
        Ideal.map (normalPolynomialEval d t).toRingHom H := by
    rw [hwhole,Ideal.map_span]
    apply congrArg Ideal.span
    ext f
    constructor
    · rintro ⟨i,rfl⟩
      refine ⟨actualNearbyCoefficientPolynomial d t (e i).val a (hc a ha (e i)),⟨e i,rfl⟩,?_⟩
      exact (actualNormalPolynomialFunctionTranslation_whole_germ d t (e i).val a (hc a ha (e i))).symm
    · rintro ⟨_,⟨P,rfl⟩,rfl⟩
      refine ⟨e.symm P,?_⟩
      change HolGerm.mk (S (e.symm P) ∘ actualAffineTranslation (d+t) (tangentInclusion d t a))
        (hhol (e.symm P)) = normalPolynomialEval d t (actualNearbyCoefficientPolynomial d t P.val a (hc a ha P))
      simpa only [S,F,Equiv.apply_symm_apply] using
        actualNormalPolynomialFunctionTranslation_whole_germ d t P.val a (hc a ha P)
  refine ⟨hH,heq,?_⟩
  rw [heq]
  exact whole_homogeneous_analytic_contraction d t H hH

end
end Hironaka.HironakaRelativeNormalNearbyPolynomialCoefficientGerms
