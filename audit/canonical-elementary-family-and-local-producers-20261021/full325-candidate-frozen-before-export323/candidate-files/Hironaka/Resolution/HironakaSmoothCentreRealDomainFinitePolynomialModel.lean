/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothCentreRealDomainInitialEquality
import Hironaka.Resolution.HironakaRelativeNormalNearbyPolynomialCoefficientGerms

/-! # One actual finite original central polynomial family on real domains
Complete mathematics precedes source. The genuine local central family has its
whole original finite relation/polynomial presentation on one true real open.
Actual translated coefficient functions then give entire nearby central ideals
and polynomial kernels. No fake globally coherent flattened family occurs.
-/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaSmoothCentreRealDomainFinitePolynomialModel
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf OkaIdealOperations
  OkaCoherence HironakaSmoothCentreCoherentDomain HironakaSmoothCentreRealDomainSaturation
  HironakaSmoothCentreRealDomainDeformation HironakaSmoothCentreRealDomainInitialRelations
  HironakaSmoothCentreRealDomainInitialEquality HironakaSmoothCentreRealDomainGraphDictionary
  HironakaRelativeNormalCoherentSaturation
  HironakaRelativeNormalDeformationSaturation HironakaRelativeNormalDeformationInitialRelations
  HironakaRelativeNormalIdeal HironakaRelativeNormalAssociatedGraded HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalDeformationFiniteRelationsSpread HironakaRelativeNormalCoherentTranslatedJets
  HironakaRelativeNormalAnalyticCoefficients
  HironakaRelativeNormalGraphCentralPolynomialModel HironakaRelativeNormalNearbyPolynomialCoefficientGerms
  HironakaRelativeNormalHomogeneousAnalyticContraction HironakaHolomorphicJetChartInvariance
  RelativePrincipalizationSpan InvertibleIdealQuotient

attribute [local instance] MvPolynomial.gradedAlgebra

section Original
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- Pure original inputs supply every nearby WHOLE central stalk by the true finite original relation functions. -/
theorem exists_original_regular_real_central_finite_relation_model
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent) :
    letI := tangentAlgebra d t
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target ∧
      ∃ _h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x) = 0,
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) ∧
      ∃ N : ℕ, ∃ U : Set (ComplexModel (deformationDimension d t)),
        ∃ V : Set (ComplexModel (d+t)), IsOpen U ∧ 0 ∈ U ∧
        U ⊆ (deformationProjection d t) ⁻¹' Φ.target ∧
        let F := actualFlattenedOriginalSheaf A x Φ
        CoherentOn (originalDeformationColonIdeal d t F N) U ∧
        (∀ y ∈ U, ∀ q : ℕ, ∀ g, (originalDeformationColonIdeal d t F (N+q)).mem y g ↔
          (originalDeformationColonIdeal d t F N).mem y g) ∧
        (∀ y ∈ U, ∀ g, (∃ q : ℕ, (originalDeformationColonIdeal d t F q).mem y g) ↔
          (originalDeformationColonIdeal d t F N).mem y g) ∧
        IsOpen V ∧ 0 ∈ V ∧ V ⊆ ((deformationCentralInclusion d t) ⁻¹' U) ∩ Φ.target ∧
        CoherentOn (originalDeformationCentralIdeal d t F N) V ∧
        (∀ P ∈ actualOriginalRelationFamily d t F, ∀ y ∈ V, HolAt (actualRelationFunction d t P) y) ∧
        (∀ y ∈ V, IdealFGAt (actualFiniteRelationSpan d t F) y) ∧
        (∀ y ∈ V, ∀ g, actualFiniteRelationSpan d t F y g ↔
          (originalDeformationCentralIdeal d t F N).mem y g) := by
  classical
  let := tangentAlgebra d t
  obtain ⟨Φ, hsrc, h0, hflat, N, U, hU, h0U, hUV, hcol, hchain, _hpow, hsat, hB, h0B,
    hcent, heq, _hcentral, _hgraph, _hgraphSat, _eGraph, _eCentral, _heGraph, _heCentral⟩ :=
    exists_original_regular_real_whole_central_initial_equality C x hreg A hA
  let F := actualFlattenedOriginalSheaf A x Φ
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
  let V := (R ∩ W) ∩ (B ∩ Φ.target)
  have hV : IsOpen V := (hR.inter hW).inter (hB.inter Φ.isOpen_target)
  have h0V : (0 : ComplexModel (d+t)) ∈ V :=
    ⟨⟨h0R, h0W⟩, h0B, actualFlattening_target_zero_mem x Φ h0⟩
  have hVsub : V ⊆ B ∩ Φ.target := inter_subset_right
  exact ⟨Φ, hsrc, h0, hflat, N, U, V, hU, h0U, hUV, hcol, hchain, hsat, hV, h0V, hVsub,
    coherentOn_restrict _ B hcent V hV (fun _ hy => hy.2.1),
    (fun P hP y hy => hhol P hP y hy.1.1), (fun y hy => hfg y hy.1.1),
    fun y hy => hwhole y hy.1.2⟩

/-- One SAME real-domain central family has the actual finite ORIGINAL homogeneous polynomial functions. -/
theorem exists_original_regular_real_central_polynomial_model
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent) :
    letI := tangentAlgebra d t
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target ∧
      ∃ _h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x) = 0,
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) ∧
      ∃ N : ℕ, ∃ U : Set (ComplexModel (deformationDimension d t)),
        ∃ V : Set (ComplexModel (d+t)), IsOpen U ∧ 0 ∈ U ∧
        U ⊆ (deformationProjection d t) ⁻¹' Φ.target ∧
        let F := actualFlattenedOriginalSheaf A x Φ
        CoherentOn (originalDeformationColonIdeal d t F N) U ∧
        (∀ y ∈ U, ∀ q : ℕ, ∀ g, (originalDeformationColonIdeal d t F (N+q)).mem y g ↔
          (originalDeformationColonIdeal d t F N).mem y g) ∧
        (∀ y ∈ U, ∀ g, (∃ q : ℕ, (originalDeformationColonIdeal d t F q).mem y g) ↔
          (originalDeformationColonIdeal d t F N).mem y g) ∧
        IsOpen V ∧ 0 ∈ V ∧ V ⊆ ((deformationCentralInclusion d t) ⁻¹' U) ∩ Φ.target ∧
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
  obtain ⟨Φ, hsrc, h0, hflat, N, U, R, hU, h0U, hUV, hcol, hchain, hsat, hR, h0R, hRsub,
    hcent, _hhol, _hfg, hcentral⟩ := exists_original_regular_real_central_finite_relation_model C x hreg A hA
  let F := actualFlattenedOriginalSheaf A x Φ
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
  refine ⟨Φ, hsrc, h0, hflat, N, U, V, hU, h0U, hUV, hcol, hchain, hsat, hV, h0V,
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


/-- Pure original inputs supply ALL whole translated central polynomial ideals and ENTIRE kernels on one true base open. -/
theorem exists_original_regular_real_translated_central_polynomial_kernels
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent) :
    letI := tangentAlgebra d t
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target ∧
      ∃ _h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x) = 0,
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) ∧
      ∃ N : ℕ, ∃ U : Set (ComplexModel (deformationDimension d t)),
        ∃ V : Set (ComplexModel (d+t)), IsOpen U ∧ 0 ∈ U ∧
        U ⊆ (deformationProjection d t) ⁻¹' Φ.target ∧
        let F := actualFlattenedOriginalSheaf A x Φ
        CoherentOn (originalDeformationColonIdeal d t F N) U ∧
        (∀ y ∈ U, ∀ q : ℕ, ∀ g, (originalDeformationColonIdeal d t F (N+q)).mem y g ↔
          (originalDeformationColonIdeal d t F N).mem y g) ∧
        (∀ y ∈ U, ∀ g, (∃ q : ℕ, (originalDeformationColonIdeal d t F q).mem y g) ↔
          (originalDeformationColonIdeal d t F N).mem y g) ∧
        IsOpen V ∧ 0 ∈ V ∧ V ⊆ ((deformationCentralInclusion d t) ⁻¹' U) ∩ Φ.target ∧
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
        (∀ a ∈ W, tangentInclusion d t a ∈ Φ.target ∩ complexCoordinatePlane (d+t) d) ∧
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
  obtain ⟨Φ, hsrc, h0, hflat, N, U, V, hU, h0U, hUV, hcol, hchain, hsat, hV, h0V, hVsub,
    hcent, hcoeff, hpoly, hdegree, hfg, hcentral⟩ :=
    exists_original_regular_real_central_polynomial_model C x hreg A hA
  let F := actualFlattenedOriginalSheaf A x Φ
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
  refine ⟨Φ, hsrc, h0, hflat, N, U, V, hU, h0U, hUV, hcol, hchain, hsat, hV, h0V, hVsub,
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

end Original
end
end Hironaka.HironakaSmoothCentreRealDomainFinitePolynomialModel
