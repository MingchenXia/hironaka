import Hironaka.Analytic.Unibranch.HironakaG10GnLocalCentral
import Hironaka.Resolution.HironakaSmoothCentreRealDomainCoefficientAlgebra

/-!
# Nearby normal initial ideals for an ideal coherent on an open set (Φ-free real-domain chain, part 2)

Lane G10GN, run 0081 (plan item G10GN-N1). Continuation of `HironakaG10GnLocalCentral`: the TN chain
`HironakaSmoothCentreRealDomain{FinitePolynomialModel,NearbyInitialKernel,CoefficientAlgebra}` run for an
arbitrary ideal `F` of `𝒪_{ℂ^{d+t}}` coherent on an open `T ∋ 0` (no flattening chart). Main output:
**`exists_local_finiteType_coefficient_initial_family`** — an open `B ∋ 0` of `ℂ^d`, a finite-type ℂ-subalgebra
`C0` of the algebra of functions holomorphic near every point of `B`, and a finite family `Q` of homogeneous
polynomials over `C0` whose germs at ANY `a ∈ B` generate the normal initial ideal (the relations of the normal
cone `gr_{(y)}(𝒪/F)`) of the translated stalk of `F` at `(a, 0)` — ONE presentation for all nearby centre points
and all degrees. The proofs are those of the TN chain with `(F, T)` in place of
`(actualFlattenedOriginalSheaf A x Φ, Φ.target)`.

BP: hironaka-g10gn-local-normal-cone.tex.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10GnLocalNearby

noncomputable section

open Hironaka Hironaka
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf OkaIdealOperations
  OkaCoherence HironakaSmoothCentreCoherentDomain HironakaSmoothCentreRealDomainSaturation
  HironakaSmoothCentreRealDomainDeformation HironakaSmoothCentreRealDomainInitialRelations
  HironakaSmoothCentreRealDomainGraphDictionary HironakaSmoothCentreRealDomainInitialEquality
  HironakaSmoothCentreRealDomainFinitePolynomialModel HironakaSmoothCentreRealDomainNearbyInitialKernel
  HironakaRelativeNormalCoherentSaturation HironakaRelativeNormalDeformationSaturation
  HironakaRelativeNormalDeformationInitialRelations HironakaRelativeNormalIdeal
  HironakaRelativeNormalAssociatedGraded HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalDeformationFiniteRelationsSpread HironakaRelativeNormalCoherentTranslatedJets
  HironakaRelativeNormalAnalyticCoefficients HironakaRelativeNormalAffineDNCDictionary
  HironakaRelativeNormalGraphCentralPolynomialModel HironakaRelativeNormalNearbyPolynomialCoefficientGerms
  HironakaRelativeNormalHomogeneousAnalyticContraction HironakaRelativeNormalCoefficientFunctionAlgebra
  HironakaHolomorphicJetChartInvariance RelativePrincipalizationSpan InvertibleIdealQuotient
  RestrictedIdealExtension DerivativeIdealAlongEtale HadamardBridge
  Hironaka.Analytic.Unibranch.HironakaG10GnLocalCentral

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] coefficientSubalgebraRing

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

private theorem real_map_span_range {R S ι : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (Q : ι → R) :
    Ideal.map f (Ideal.span (range Q)) = Ideal.span (range (fun i => f (Q i))) := by
  rw [Ideal.map_span]
  apply congrArg Ideal.span
  ext x
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨Q i, ⟨i, rfl⟩, rfl⟩

theorem exists_local_central_finite_relation_model
    (d t : ℕ) (F : GermIdeal (d+t) (ComplexModel (d+t))) (T : Set (ComplexModel (d+t)))
    (hT : IsOpen T) (h0T : (0 : ComplexModel (d+t)) ∈ T) (hF : CoherentOn F T) :
    letI := tangentAlgebra d t
      ∃ N : ℕ, ∃ U : Set (ComplexModel (deformationDimension d t)),
        ∃ V : Set (ComplexModel (d+t)), IsOpen U ∧ 0 ∈ U ∧
        U ⊆ (deformationProjection d t) ⁻¹' T ∧
        CoherentOn (originalDeformationColonIdeal d t F N) U ∧
        (∀ y ∈ U, ∀ q : ℕ, ∀ g, (originalDeformationColonIdeal d t F (N+q)).mem y g ↔
          (originalDeformationColonIdeal d t F N).mem y g) ∧
        (∀ y ∈ U, ∀ g, (∃ q : ℕ, (originalDeformationColonIdeal d t F q).mem y g) ↔
          (originalDeformationColonIdeal d t F N).mem y g) ∧
        IsOpen V ∧ 0 ∈ V ∧ V ⊆ ((deformationCentralInclusion d t) ⁻¹' U) ∩ T ∧
        CoherentOn (originalDeformationCentralIdeal d t F N) V ∧
        (∀ P ∈ actualOriginalRelationFamily d t F, ∀ y ∈ V, HolAt (actualRelationFunction d t P) y) ∧
        (∀ y ∈ V, IdealFGAt (actualFiniteRelationSpan d t F) y) ∧
        (∀ y ∈ V, ∀ g, actualFiniteRelationSpan d t F y g ↔
          (originalDeformationCentralIdeal d t F N).mem y g) := by
  classical
  let := tangentAlgebra d t
  obtain ⟨N, U, hU, h0U, hUV, hcol, hchain, _hpow, hsat, hB, h0B,
    hcent, heq, _hcentral, _hgraph, _hgraphSat, _eGraph, _eCentral, _heGraph, _heCentral⟩ :=
    exists_local_whole_central_initial_equality d t F T hT h0T hF
  let B := (deformationCentralInclusion d t) ⁻¹' U
  have hcentFG := idealFGAt_of_coherentOn (originalDeformationCentralIdeal d t F N) B hcent h0B
  obtain ⟨R, hR, h0R, hhol, hfg⟩ := exists_actual_finite_relation_holomorphic_model d t F
  have hiff : ∀ g, actualFiniteRelationSpan d t F 0 g ↔
      (originalDeformationCentralIdeal d t F N).mem 0 g := by
    intro g
    constructor
    · intro hg
      have hmem := (actualFiniteRelationSpan_origin_dictionary d t F hg.1).mp hg
      change HolGerm.mk g hg.1 ∈ Ideal.map (normalPolynomialEval d t).toRingHom
        (originalNormalInitialIdeal d t (originalCoherentOriginIdeal F)) at hmem
      rw [← heq] at hmem
      exact (mk_mem_originalOriginIdeal_iff_of_local (originalDeformationCentralIdeal d t F N) hcentFG hg.1).mp hmem
    · intro hg
      have hgHol := holAt_mem_of_idealFGAt (originalDeformationCentralIdeal d t F N) hcentFG hg
      apply (actualFiniteRelationSpan_origin_dictionary d t F hgHol).mpr
      change HolGerm.mk g hgHol ∈ Ideal.map (normalPolynomialEval d t).toRingHom
        (originalNormalInitialIdeal d t (originalCoherentOriginIdeal F))
      rw [← heq]
      exact (mk_mem_originalOriginIdeal_iff_of_local (originalDeformationCentralIdeal d t F N) hcentFG hgHol).mpr hg
  obtain ⟨W, hW, h0W, hwhole⟩ := exists_open_coherent_equality (hfg 0 h0R) hcentFG hiff
  let V := (R ∩ W) ∩ (B ∩ T)
  have hV : IsOpen V := (hR.inter hW).inter (hB.inter hT)
  have h0V : (0 : ComplexModel (d+t)) ∈ V :=
    ⟨⟨h0R, h0W⟩, h0B, h0T⟩
  have hVsub : V ⊆ B ∩ T := inter_subset_right
  exact ⟨N, U, V, hU, h0U, hUV, hcol, hchain, hsat, hV, h0V, hVsub,
    coherentOn_restrict _ B hcent V hV (fun _ hy => hy.2.1),
    (fun P hP y hy => hhol P hP y hy.1.1), (fun y hy => hfg y hy.1.1),
    fun y hy => hwhole y hy.1.2⟩

theorem exists_local_central_polynomial_model
    (d t : ℕ) (F : GermIdeal (d+t) (ComplexModel (d+t))) (T : Set (ComplexModel (d+t)))
    (hT : IsOpen T) (h0T : (0 : ComplexModel (d+t)) ∈ T) (hF : CoherentOn F T) :
    letI := tangentAlgebra d t
      ∃ N : ℕ, ∃ U : Set (ComplexModel (deformationDimension d t)),
        ∃ V : Set (ComplexModel (d+t)), IsOpen U ∧ 0 ∈ U ∧
        U ⊆ (deformationProjection d t) ⁻¹' T ∧
        CoherentOn (originalDeformationColonIdeal d t F N) U ∧
        (∀ y ∈ U, ∀ q : ℕ, ∀ g, (originalDeformationColonIdeal d t F (N+q)).mem y g ↔
          (originalDeformationColonIdeal d t F N).mem y g) ∧
        (∀ y ∈ U, ∀ g, (∃ q : ℕ, (originalDeformationColonIdeal d t F q).mem y g) ↔
          (originalDeformationColonIdeal d t F N).mem y g) ∧
        IsOpen V ∧ 0 ∈ V ∧ V ⊆ ((deformationCentralInclusion d t) ⁻¹' U) ∩ T ∧
        CoherentOn (originalDeformationCentralIdeal d t F N) V ∧
        (∀ P ∈ actualOriginalRelationFamily d t F, ∀ α : Fin t →₀ ℕ, ∀ y ∈ V,
          DifferentiableAt ℂ (actualCoefficientRepresentative (P.coeff α)) (tangentProjection d t y)) ∧
        (∀ P ∈ actualOriginalRelationFamily d t F, ∀ y ∈ V, HolAt (actualNormalPolynomialFunction d t P) y) ∧
        (∀ P ∈ actualOriginalRelationFamily d t F, ∃ q : ℕ, P.IsHomogeneous q ∧
          ∀ y ∈ V, (actualPolynomialSpecialization P (tangentProjection d t y)).IsHomogeneous q) ∧
        (∀ y ∈ V, IdealFGAt (actualNormalPolynomialSpan d t F) y) ∧
        (∀ y ∈ V, ∀ g, actualNormalPolynomialSpan d t F y g ↔
          (originalDeformationCentralIdeal d t F N).mem y g) := by
  classical
  let := tangentAlgebra d t
  obtain ⟨N, U, R, hU, h0U, hUV, hcol, hchain, hsat, hR, h0R, hRsub,
    hcent, _hhol, _hfg, hcentral⟩ := exists_local_central_finite_relation_model d t F T hT h0T hF
  obtain ⟨W, hW, h0W, hcompare⟩ := exists_actual_original_polynomial_span_comparison_open d t F
  obtain ⟨B, hB, h0B, hcoeff⟩ := exists_common_polynomial_coefficient_open (actualOriginalRelationFamily d t F)
  let V := (R ∩ W) ∩ (tangentProjection d t) ⁻¹' B
  have hV : IsOpen V := (hR.inter hW).inter (hB.preimage (tangentProjection d t).continuous)
  have h0V : (0 : ComplexModel (d+t)) ∈ V :=
    ⟨⟨h0R, h0W⟩, by change tangentProjection d t 0 ∈ B; simpa only [map_zero] using h0B⟩
  have hc : ∀ P ∈ actualOriginalRelationFamily d t F, ∀ α : Fin t →₀ ℕ, ∀ y ∈ V,
      DifferentiableAt ℂ (actualCoefficientRepresentative (P.coeff α)) (tangentProjection d t y) := by
    intro P hP α y hy
    simpa only [actualPolynomialRepresentative_coeff] using hcoeff P hP α _ hy.2
  have hpoly : ∀ P ∈ actualOriginalRelationFamily d t F, ∀ y ∈ V,
      HolAt (actualNormalPolynomialFunction d t P) y := by
    intro P hP y hy
    have hVe : ∀ᶠ z in 𝓝 y, z ∈ V := hV.mem_nhds hy
    exact hVe.mono fun z hz =>
      actualNormalPolynomialFunction_differentiableAt d t P z (fun α => hc P hP α z hz)
  refine ⟨N, U, V, hU, h0U, hUV, hcol, hchain, hsat, hV, h0V,
    (fun _ hy => hRsub hy.1.1), coherentOn_restrict _ R hcent V hV (fun _ hy => hy.1.1),
    hc, hpoly, ?_, ?_, ?_⟩
  · intro P hP
    obtain ⟨q,hq⟩ := actualOriginalHomogeneousRelations_homogeneous d t (originalCoherentOriginIdeal F) P hP
    exact ⟨q, hq, fun y _ => actualPolynomialSpecialization_homogeneous P hq (tangentProjection d t y)⟩
  · intro y hy
    exact ⟨V, hV, hy, ↥(actualOriginalRelationFamily d t F), inferInstance,
      (fun P => actualNormalPolynomialFunction d t P.val),
      (fun P z hz => (hpoly P.val P.property z hz).self_of_nhds.differentiableWithinAt),
      fun _ _ _ => Iff.rfl⟩
  · intro y hy g
    exact (hcompare y hy.1.2 g).trans (hcentral y hy.1.1 g)

theorem exists_local_translated_central_polynomial_kernels
    (d t : ℕ) (F : GermIdeal (d+t) (ComplexModel (d+t))) (T : Set (ComplexModel (d+t)))
    (hT : IsOpen T) (h0T : (0 : ComplexModel (d+t)) ∈ T) (hF : CoherentOn F T) :
    letI := tangentAlgebra d t
      ∃ N : ℕ, ∃ U : Set (ComplexModel (deformationDimension d t)),
        ∃ V : Set (ComplexModel (d+t)), IsOpen U ∧ 0 ∈ U ∧
        U ⊆ (deformationProjection d t) ⁻¹' T ∧
        CoherentOn (originalDeformationColonIdeal d t F N) U ∧
        (∀ y ∈ U, ∀ q : ℕ, ∀ g, (originalDeformationColonIdeal d t F (N+q)).mem y g ↔
          (originalDeformationColonIdeal d t F N).mem y g) ∧
        (∀ y ∈ U, ∀ g, (∃ q : ℕ, (originalDeformationColonIdeal d t F q).mem y g) ↔
          (originalDeformationColonIdeal d t F N).mem y g) ∧
        IsOpen V ∧ 0 ∈ V ∧ V ⊆ ((deformationCentralInclusion d t) ⁻¹' U) ∩ T ∧
        CoherentOn (originalDeformationCentralIdeal d t F N) V ∧
        (∀ P ∈ actualOriginalRelationFamily d t F, ∀ α : Fin t →₀ ℕ, ∀ y ∈ V,
          DifferentiableAt ℂ (actualCoefficientRepresentative (P.coeff α)) (tangentProjection d t y)) ∧
        (∀ P ∈ actualOriginalRelationFamily d t F, ∀ y ∈ V, HolAt (actualNormalPolynomialFunction d t P) y) ∧
        (∀ P ∈ actualOriginalRelationFamily d t F, ∃ q : ℕ, P.IsHomogeneous q ∧
          ∀ y ∈ V, (actualPolynomialSpecialization P (tangentProjection d t y)).IsHomogeneous q) ∧
        (∀ y ∈ V, IdealFGAt (actualNormalPolynomialSpan d t F) y) ∧
        (∀ y ∈ V, ∀ g, actualNormalPolynomialSpan d t F y g ↔
          (originalDeformationCentralIdeal d t F N).mem y g) ∧
        let W := (tangentInclusion d t) ⁻¹' V
        IsOpen W ∧ 0 ∈ W ∧
        (∀ a ∈ W, tangentInclusion d t a ∈ T ∩ complexCoordinatePlane (d+t) d) ∧
        ∃ hc : ∀ a ∈ W, ∀ P : ↥(actualOriginalRelationFamily d t F), ∀ α,
          HolAt (actualCoefficientRepresentative (P.val.coeff α)) a,
        ∀ a (ha : a ∈ W),
          let H := Ideal.span (range fun P : ↥(actualOriginalRelationFamily d t F) =>
            actualNearbyCoefficientPolynomial d t P.val a (hc a ha P))
          H.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin t) (HolGerm (ComplexModel d))) ∧
          originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
            (originalDeformationCentralIdeal d t F N) (tangentInclusion d t a)) =
              Ideal.map (normalPolynomialEval d t).toRingHom H ∧
          Ideal.comap (normalPolynomialEval d t).toRingHom
            (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
              (originalDeformationCentralIdeal d t F N) (tangentInclusion d t a))) = H := by
  classical
  let := tangentAlgebra d t
  obtain ⟨N, U, V, hU, h0U, hUV, hcol, hchain, hsat, hV, h0V, hVsub,
    hcent, hcoeff, hpoly, hdegree, hfg, hcentral⟩ :=
    exists_local_central_polynomial_model d t F T hT h0T hF
  let W := (tangentInclusion d t) ⁻¹' V
  have hW : IsOpen W := hV.preimage (tangentInclusion d t).continuous
  have h0W : (0 : ComplexModel d) ∈ W := by
    change tangentInclusion d t 0 ∈ V
    simpa only [map_zero] using h0V
  have hc : ∀ a ∈ W, ∀ P : ↥(actualOriginalRelationFamily d t F), ∀ α,
      HolAt (actualCoefficientRepresentative (P.val.coeff α)) a := by
    intro a ha P α
    have hWe : ∀ᶠ b in 𝓝 a, b ∈ W := hW.mem_nhds ha
    exact hWe.mono fun b hb => by
      simpa only [tangentProjection_tangentInclusion] using hcoeff P.val P.property α (tangentInclusion d t b) hb
  refine ⟨N, U, V, hU, h0U, hUV, hcol, hchain, hsat, hV, h0V, hVsub,
    hcent, hcoeff, hpoly, hdegree, hfg, hcentral, hW, h0W,
    (fun a ha => ⟨(hVsub ha).2, tangentInclusion_mem_plane d t a⟩), hc, ?_⟩
  intro a ha
  dsimp only
  let μ := ↥(actualOriginalRelationFamily d t F)
  let e : Fin (Fintype.card μ) ≃ μ := (Fintype.equivFin μ).symm
  let G : μ → ComplexModel (d+t) → ℂ := fun P => actualNormalPolynomialFunction d t P.val
  let S := fun i : Fin (Fintype.card μ) => G (e i)
  let H := Ideal.span (range fun P : μ => actualNearbyCoefficientPolynomial d t P.val a (hc a ha P))
  have hH : H.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin t) (HolGerm (ComplexModel d))) := by
    apply Ideal.homogeneous_span
    rintro P ⟨Q, rfl⟩
    obtain ⟨q,hq,_⟩ := hdegree Q.val Q.property
    exact ⟨q, actualNearbyCoefficientPolynomial_homogeneous d t Q.val a (hc a ha Q) hq⟩
  have hS : ∀ i, MDifferentiableOn 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ℂ) (S i) V := by
    intro i y hy
    exact (hpoly (e i).val (e i).property y hy).self_of_nhds.mdifferentiableAt.mdifferentiableWithinAt
  have hgen : ∀ y ∈ V, ∀ g,
      (originalDeformationCentralIdeal d t F N).mem y g ↔ IsInSpanAt (n := d+t) (· ∈ range S) y g := by
    intro y hy g
    exact (hcentral y hy g).symm.trans
      ((actual_finite_span_reindex e G y g).symm.trans (actual_function_span_holomorphic_dictionary S y g))
  have hhol (i : Fin (Fintype.card μ)) :
      HolAt (S i ∘ actualAffineTranslation (d+t) (tangentInclusion d t a)) 0 :=
    actualNormalPolynomialFunctionTranslation_holomorphic d t (e i).val a (hc a ha (e i))
  have hwhole := translated_origin_ideal_eq_span_of_real_generators
    (originalDeformationCentralIdeal d t F N) S hV hS hgen ha hhol
  have heq : originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
      (originalDeformationCentralIdeal d t F N) (tangentInclusion d t a)) =
        Ideal.map (normalPolynomialEval d t).toRingHom H := by
    rw [hwhole, Ideal.map_span]
    apply congrArg Ideal.span
    ext f
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨actualNearbyCoefficientPolynomial d t (e i).val a (hc a ha (e i)), ⟨e i, rfl⟩, ?_⟩
      exact (actualNormalPolynomialFunctionTranslation_whole_germ d t (e i).val a (hc a ha (e i))).symm
    · rintro ⟨_, ⟨P, rfl⟩, rfl⟩
      refine ⟨e.symm P, ?_⟩
      change HolGerm.mk (S (e.symm P) ∘ actualAffineTranslation (d+t) (tangentInclusion d t a))
        (hhol (e.symm P)) = normalPolynomialEval d t (actualNearbyCoefficientPolynomial d t P.val a (hc a ha P))
      simpa only [S, G, Equiv.apply_symm_apply] using
        actualNormalPolynomialFunctionTranslation_whole_germ d t P.val a (hc a ha P)
  refine ⟨hH, heq, ?_⟩
  rw [heq]
  exact whole_homogeneous_analytic_contraction d t H hH


theorem exists_local_all_nearby_initial_polynomial_kernels
    (d t : ℕ) (F : GermIdeal (d+t) (ComplexModel (d+t))) (T : Set (ComplexModel (d+t)))
    (hT : IsOpen T) (h0T : (0 : ComplexModel (d+t)) ∈ T) (hF : CoherentOn F T) :
    letI := tangentAlgebra d t
      ∃ N : ℕ, ∃ U : Set (ComplexModel (deformationDimension d t)),
        ∃ V : Set (ComplexModel (d+t)), IsOpen U ∧ 0 ∈ U ∧
        U ⊆ (deformationProjection d t) ⁻¹' T ∧
        CoherentOn (originalDeformationColonIdeal d t F N) U ∧
        (∀ y ∈ U, ∀ q : ℕ, ∀ g, (originalDeformationColonIdeal d t F (N+q)).mem y g ↔
          (originalDeformationColonIdeal d t F N).mem y g) ∧
        (∀ y ∈ U, ∀ g, (∃ q : ℕ, (originalDeformationColonIdeal d t F q).mem y g) ↔
          (originalDeformationColonIdeal d t F N).mem y g) ∧
        IsOpen V ∧ 0 ∈ V ∧ V ⊆ ((deformationCentralInclusion d t) ⁻¹' U) ∩ T ∧
        CoherentOn (originalDeformationCentralIdeal d t F N) V ∧
        (∀ P ∈ actualOriginalRelationFamily d t F, ∀ α : Fin t →₀ ℕ, ∀ y ∈ V,
          DifferentiableAt ℂ (actualCoefficientRepresentative (P.coeff α)) (tangentProjection d t y)) ∧
        (∀ P ∈ actualOriginalRelationFamily d t F, ∀ y ∈ V, HolAt (actualNormalPolynomialFunction d t P) y) ∧
        (∀ P ∈ actualOriginalRelationFamily d t F, ∃ q : ℕ, P.IsHomogeneous q ∧
          ∀ y ∈ V, (actualPolynomialSpecialization P (tangentProjection d t y)).IsHomogeneous q) ∧
        (∀ y ∈ V, IdealFGAt (actualNormalPolynomialSpan d t F) y) ∧
        (∀ y ∈ V, ∀ g, actualNormalPolynomialSpan d t F y g ↔
          (originalDeformationCentralIdeal d t F N).mem y g) ∧
        let W := (tangentInclusion d t) ⁻¹' V
        IsOpen W ∧ 0 ∈ W ∧
        (∀ a ∈ W, tangentInclusion d t a ∈ T ∩ complexCoordinatePlane (d+t) d) ∧
        ∃ hc : ∀ a ∈ W, ∀ P : ↥(actualOriginalRelationFamily d t F), ∀ α,
          HolAt (actualCoefficientRepresentative (P.val.coeff α)) a,
        ∀ a (ha : a ∈ W),
          let H := Ideal.span (range fun P : ↥(actualOriginalRelationFamily d t F) =>
            actualNearbyCoefficientPolynomial d t P.val a (hc a ha P))
          let J := actualTranslatedOriginalSheaf F (tangentInclusion d t a)
          IdealFGAt J.mem 0 ∧ IdealFGAt (originalDeformationIdeal d t J).mem 0 ∧
          (∀ q : ℕ, ∀ f, (originalDeformationColonIdeal d t J (N+q)).mem 0 f ↔
            (originalDeformationColonIdeal d t J N).mem 0 f) ∧
          (∀ f, (∃ q : ℕ, (originalDeformationColonIdeal d t J q).mem 0 f) ↔
            (originalDeformationColonIdeal d t J N).mem 0 f) ∧
          H.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin t) (HolGerm (ComplexModel d))) ∧
          originalNormalInitialIdeal d t (originalCoherentOriginIdeal J) = H ∧
          originalCoherentOriginIdeal (originalDeformationCentralIdeal d t J N) =
            Ideal.map (normalPolynomialEval d t).toRingHom
              (originalNormalInitialIdeal d t (originalCoherentOriginIdeal J)) ∧
          originalCoherentOriginIdeal (originalDeformationCentralIdeal d t J N) =
            originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
              (originalDeformationCentralIdeal d t F N) (tangentInclusion d t a)) ∧
          originalCoherentOriginIdeal (originalDeformationCentralIdeal d t J N) =
            Ideal.map (normalPolynomialEval d t).toRingHom H ∧
          Ideal.comap (normalPolynomialEval d t).toRingHom
            (originalCoherentOriginIdeal (originalDeformationCentralIdeal d t J N)) = H := by
  classical
  let := tangentAlgebra d t
  obtain ⟨N,U,V,hU,h0U,hUV,hcol,hchain,hsat,hV,h0V,hVsub,
    hcent,hcoeff,hpoly,hdegree,hfg,hcentral,hW,h0W,hpoint,hc,hkernels⟩ :=
    exists_local_translated_central_polynomial_kernels d t F T hT h0T hF
  refine ⟨N,U,V,hU,h0U,hUV,hcol,hchain,hsat,hV,h0V,hVsub,
    hcent,hcoeff,hpoly,hdegree,hfg,hcentral,hW,h0W,hpoint,hc,?_⟩
  intro a ha
  dsimp only
  let J := actualTranslatedOriginalSheaf F (tangentInclusion d t a)
  let Tt := (actualAffineTranslation (d+t) (tangentInclusion d t a)) ⁻¹' T
  let H := Ideal.span (range fun P : ↥(actualOriginalRelationFamily d t F) =>
    actualNearbyCoefficientPolynomial d t P.val a (hc a ha P))
  have haT : tangentInclusion d t a ∈ T := (hpoint a ha).1
  have hTt : IsOpen Tt := hT.preimage
    (actualAffineTranslation_contMDiff (d+t) (tangentInclusion d t a)).continuous
  have h0Tt : (0 : ComplexModel (d+t)) ∈ Tt := by
    change actualAffineTranslation (d+t) (tangentInclusion d t a) 0 ∈ T
    simpa only [actualAffineTranslation_zero] using haT
  have hJ := coherentOn_actualTranslated_of_real F T hT hF (tangentInclusion d t a)
  have hJFG : IdealFGAt J.mem 0 := idealFGAt_of_coherentOn J Tt hJ h0Tt
  have hD := coherentOn_originalDeformation_of_real d t J Tt hTt hJ
  have h0D : (0 : ComplexModel (deformationDimension d t)) ∈ (deformationProjection d t) ⁻¹' Tt := by
    change deformationProjection d t 0 ∈ Tt
    simpa only [map_zero] using h0Tt
  have hDFG : IdealFGAt (originalDeformationIdeal d t J).mem 0 :=
    idealFGAt_of_coherentOn (originalDeformationIdeal d t J) _ hD h0D
  have hb : deformationCentralInclusion d t (tangentInclusion d t a) ∈ U := (hVsub ha).1
  have hst := original_translated_saturation_of_real d t F T hT hF a haT N
    (hchain _ hb) (hsat _ hb)
  have heInitial := whole_central_initial_equality_of_local_saturation d t J hJFG hDFG N hst.2
  have heSame := original_central_whole_origin_translation_of_real d t F T hT hF a haT N U hcol hb
  obtain ⟨hH,hmodel,hcontract⟩ := hkernels a ha
  have heModel : originalCoherentOriginIdeal (originalDeformationCentralIdeal d t J N) =
      Ideal.map (normalPolynomialEval d t).toRingHom H := heSame.trans hmodel
  have heKernel : originalNormalInitialIdeal d t (originalCoherentOriginIdeal J) = H := by
    have hi := whole_homogeneous_analytic_contraction d t
      (originalNormalInitialIdeal d t (originalCoherentOriginIdeal J))
      (originalNormalInitialIdeal_homogeneous d t (originalCoherentOriginIdeal J))
    rw [← heInitial,heModel] at hi
    exact hi.symm.trans (whole_homogeneous_analytic_contraction d t H hH)
  exact ⟨hJFG,hDFG,hst.1,hst.2,hH,heKernel,heInitial,heSame,heModel,
    by rw [heSame];exact hcontract⟩


theorem exists_local_coefficient_algebra_initial_family
    (d t : ℕ) (F : GermIdeal (d+t) (ComplexModel (d+t))) (T : Set (ComplexModel (d+t)))
    (hT : IsOpen T) (h0T : (0 : ComplexModel (d+t)) ∈ T) (hF : CoherentOn F T) :
      ∃ B : Set (ComplexModel d), IsOpen B ∧ ∃ h0 : (0 : ComplexModel d) ∈ B,
        (∀ a ∈ B, tangentInclusion d t a ∈ T ∩ complexCoordinatePlane (d+t) d) ∧
        ∃ Q : ↥(actualOriginalRelationFamily d t F) →
          MvPolynomial (Fin t) (coefficientFunctionAlgebra d B),
          (∀ P, ∃ q : ℕ, (Q P).IsHomogeneous q) ∧
          (∀ P, MvPolynomial.map (coefficientGermHom d B 0 h0).toRingHom (Q P) = P.val) ∧
          Ideal.map (MvPolynomial.map (coefficientGermHom d B 0 h0).toRingHom)
            (Ideal.span (range Q)) = originalNormalInitialIdeal d t (originalCoherentOriginIdeal F) ∧
          ∀ a (ha : a ∈ B),
            Ideal.map (MvPolynomial.map (coefficientGermHom d B a ha).toRingHom)
              (Ideal.span (range Q)) = originalNormalInitialIdeal d t
                (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf F (tangentInclusion d t a))) := by
  classical
  let := tangentAlgebra d t
  obtain ⟨_N,_U,V,_hU,_h0U,_hUV,_hcol,_hchain,_hsat,_hV,_h0V,_hVsub,
    _hcent,_hcoeff,_hpoly,_hdegree,_hfg,_hcentral,hB,h0B,hpoint,hc,hmodels⟩ :=
    exists_local_all_nearby_initial_polynomial_kernels d t F T hT h0T hF
  let B := (tangentInclusion d t) ⁻¹' V
  let Q := fun P : ↥(actualOriginalRelationFamily d t F) =>
    coefficientPolynomialLift d t B P.val (fun α a ha => hc a ha P α)
  have hQ0 (P : ↥(actualOriginalRelationFamily d t F)) :
      MvPolynomial.map (coefficientGermHom d B 0 h0B).toRingHom (Q P) = P.val :=
    coefficientPolynomialLift_origin d t B P.val (fun α a ha => hc a ha P α) h0B
  refine ⟨B,hB,h0B,hpoint,Q,?_,hQ0,?_,?_⟩
  · intro P
    obtain ⟨q,hq⟩ := actualOriginalHomogeneousRelations_homogeneous d t
      (originalCoherentOriginIdeal F) P.val P.property
    exact ⟨q,coefficientPolynomialLift_homogeneous d t B P.val _ hq⟩
  · rw [real_map_span_range (MvPolynomial.map (coefficientGermHom d B 0 h0B).toRingHom) Q]
    have he : (fun P => MvPolynomial.map (coefficientGermHom d B 0 h0B).toRingHom (Q P)) =
        fun P : ↥(actualOriginalRelationFamily d t F) => P.val := funext hQ0
    rw [he]
    have hr : range (fun P : ↥(actualOriginalRelationFamily d t F) => P.val) =
        (actualOriginalRelationFamily d t F : Set _) := by
      ext P
      exact ⟨fun ⟨Q,hQ⟩ => hQ ▸ Q.property,fun hP => ⟨⟨P,hP⟩,rfl⟩⟩
    rw [hr]
    exact (actualOriginalHomogeneousRelations_spec d t (originalCoherentOriginIdeal F)).2.symm
  · intro a ha
    rw [real_map_span_range (MvPolynomial.map (coefficientGermHom d B a ha).toRingHom) Q]
    have he : (fun P => MvPolynomial.map (coefficientGermHom d B a ha).toRingHom (Q P)) =
        fun P : ↥(actualOriginalRelationFamily d t F) =>
          actualNearbyCoefficientPolynomial d t P.val a (hc a ha P) := by
      funext P
      exact coefficientPolynomialLift_nearby d t B P.val _ a ha
    rw [he]
    obtain ⟨_,_,_,_,_,hinit,_,_,_,_⟩ := hmodels a ha
    exact hinit.symm

theorem exists_local_finiteType_coefficient_initial_family
    (d t : ℕ) (F : GermIdeal (d+t) (ComplexModel (d+t))) (T : Set (ComplexModel (d+t)))
    (hT : IsOpen T) (h0T : (0 : ComplexModel (d+t)) ∈ T) (hF : CoherentOn F T) :
      ∃ B : Set (ComplexModel d), IsOpen B ∧ ∃ h0 : (0 : ComplexModel d) ∈ B,
        (∀ a ∈ B, tangentInclusion d t a ∈ T ∩ complexCoordinatePlane (d+t) d) ∧
        ∃ C0 : Subalgebra ℂ (coefficientFunctionAlgebra d B), Algebra.FiniteType ℂ C0 ∧
        ∃ Q : ↥(actualOriginalRelationFamily d t F) → MvPolynomial (Fin t) C0,
          (∀ P, ∃ q : ℕ, (Q P).IsHomogeneous q) ∧
          Ideal.map (MvPolynomial.map ((coefficientGermHom d B 0 h0).comp C0.val).toRingHom)
            (Ideal.span (range Q)) = originalNormalInitialIdeal d t (originalCoherentOriginIdeal F) ∧
          ∀ a (ha : a ∈ B),
            Ideal.map (MvPolynomial.map ((coefficientGermHom d B a ha).comp C0.val).toRingHom)
              (Ideal.span (range Q)) = originalNormalInitialIdeal d t
                (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf F (tangentInclusion d t a))) := by
  classical
  obtain ⟨B,hB,h0B,hpoint,Q,hhom,_hQ0,horigin,hnearby⟩ :=
    exists_local_coefficient_algebra_initial_family d t F T hT h0T hF
  let Ps : Finset (MvPolynomial (Fin t) (coefficientFunctionAlgebra d B)) := Finset.univ.image Q
  have hPs (P : ↥(actualOriginalRelationFamily d t F)) : Q P ∈ Ps :=
    Finset.mem_image.mpr ⟨P,Finset.mem_univ _,rfl⟩
  let C0 : Subalgebra ℂ (coefficientFunctionAlgebra d B) := finitePolynomialCoefficientAlgebra Ps
  let L : ↥(actualOriginalRelationFamily d t F) → MvPolynomial (Fin t) C0 :=
    fun P => finiteCoefficientPolynomialLift Ps (Q P) (hPs P)
  have hL (a : ComplexModel d) (ha : a ∈ B) (P : ↥(actualOriginalRelationFamily d t F)) :
      MvPolynomial.map ((coefficientGermHom d B a ha).comp C0.val).toRingHom (L P) =
        MvPolynomial.map (coefficientGermHom d B a ha).toRingHom (Q P) := by
    rw [← finiteCoefficientPolynomialLift_map Ps (Q P) (hPs P)]
    rw [MvPolynomial.map_map]
    rfl
  have himage (a : ComplexModel d) (ha : a ∈ B) :
      Ideal.map (MvPolynomial.map ((coefficientGermHom d B a ha).comp C0.val).toRingHom)
        (Ideal.span (range L)) =
      Ideal.map (MvPolynomial.map (coefficientGermHom d B a ha).toRingHom) (Ideal.span (range Q)) := by
    let : CommRing C0 := C0.toCommRing
    rw [real_map_span_range (MvPolynomial.map ((coefficientGermHom d B a ha).comp C0.val).toRingHom) L,
      real_map_span_range (MvPolynomial.map (coefficientGermHom d B a ha).toRingHom) Q]
    exact congrArg (fun F => Ideal.span (range F)) (funext (hL a ha))
  refine ⟨B,hB,h0B,hpoint,C0,finitePolynomialCoefficientAlgebra_finiteType Ps,L,?_,?_,?_⟩
  · intro P
    obtain ⟨q,hq⟩ := hhom P
    exact ⟨q,finiteCoefficientPolynomialLift_homogeneous Ps (Q P) (hPs P) hq⟩
  · exact (himage 0 h0B).trans horigin
  · exact fun a ha => (himage a ha).trans (hnearby a ha)


end
end Hironaka.Analytic.Unibranch.HironakaG10GnLocalNearby
