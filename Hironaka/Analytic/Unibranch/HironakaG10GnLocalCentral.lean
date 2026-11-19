import Hironaka.Resolution.HironakaSmoothCentreRealDomainInitialEquality

/-!
# Normal-cone central model for an ideal coherent on an open set (Φ-free real-domain chain, part 1)

Lane G10GN, run 0081 (plan item G10GN-N1, `work/hironaka-run0081-20261117/G10GN/hGF-route.md`). The TN chain
`HironakaSmoothCentreRealDomain{Deformation,InitialRelations,GraphDictionary,InitialEquality}` proves its
statements for the ideal `F := actualFlattenedOriginalSheaf A x Φ` obtained from a coherent ideal `A` on a complex
manifold and a flattening chart `Φ` of a regular centre, using `Φ` ONLY through `F`, the open set `Φ.target ∋ 0`
and `CoherentOn F Φ.target`. Here the same proofs are run for an ARBITRARY ideal `F` of `𝒪_{ℂ^{d+t}}` coherent on
an open `T ∋ 0` (no chart): `exists_local_graph_deformation_domain`, `exists_local_exact_deformation_central_model`,
`exists_local_central_initial_symbol_memberships`, `exists_local_central_initial_ideal_inclusion`,
`exists_local_whole_graph_model`, `exists_local_whole_central_initial_equality`. The proofs are those of the TN
chain, with `(F, T)` in place of `(actualFlattenedOriginalSheaf A x Φ, Φ.target)`.

BP: hironaka-g10gn-local-normal-cone.tex.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10GnLocalCentral

noncomputable section

open Hironaka Hironaka
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf OkaIdealOperations
  OkaCoherence HironakaSmoothCentreCoherentDomain HironakaSmoothCentreRealDomainSaturation
  HironakaSmoothCentreRealDomainDeformation HironakaSmoothCentreRealDomainInitialRelations
  HironakaSmoothCentreRealDomainGraphDictionary HironakaSmoothCentreRealDomainInitialEquality
  HironakaRelativeNormalCoherentSaturation HironakaRelativeNormalDeformationSaturation
  HironakaRelativeNormalDeformationInitialRelations HironakaRelativeNormalAnalyticGraphQuotient
  HironakaRelativeNormalIdeal HironakaRelativeNormalAssociatedGraded HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalIdealMatrices HironakaRelativeNormalPolynomialJetAlgebra
  HironakaRelativeNormalGraphWeightJets HironakaRelativeNormalGraphWeightComponents
  HironakaRelativeNormalGraphDiagonalCoefficients HironakaRelativeNormalGraphAnalyticFiniteRelations
  HironakaRelativeNormalGraphWeightAnalyticReconstruction HironakaRelativeNormalGraphCentralInitialSymbols
  HironakaRelativeNormalGraphCentralAnalyticClosure
  HironakaHolomorphicJetChartInvariance RelativePrincipalizationSpan InvertibleIdealQuotient
  HadamardBridge RestrictedIdealExtension

private theorem initialSymbol_mem_selected_central_local (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t)))
    (hD : IdealFGAt (originalDeformationIdeal d t I).mem 0) (N : ℕ)
    (hN : ∀ f, (∃ q : ℕ, (originalDeformationColonIdeal d t I q).mem 0 f) ↔
      (originalDeformationColonIdeal d t I N).mem 0 f)
    (q : ℕ) (g : HolGerm (ComplexModel (d+t)))
    (hIg : g ∈ originalCoherentOriginIdeal I) (hg : g ∈ normalIdeal d t ^ q) :
    normalPolynomialEval d t (originalNormalInitialSymbol d t q g hg) ∈
      originalCoherentOriginIdeal (originalDeformationCentralIdeal d t I N) := by
  obtain ⟨G, hG, hcentral⟩ := exists_divided_scaling_initial_symbol d t q g hg
  have hscaled := deformationScalingPullback_mem_originalIdeal_local d t I g hIg
  have hmul : G * deformationParameterGerm d t ^ q ∈
      originalCoherentOriginIdeal (originalDeformationIdeal d t I) := by
    rw [mul_comm, ← hG]
    exact hscaled
  have hcolon := (mem_actualOriginColonChain_iff
    (originalCoherentOriginIdeal (originalDeformationIdeal d t I)) (deformationParameterGerm d t) G q).mpr hmul
  obtain ⟨f, hf, rfl⟩ := HolGerm.exists_eq_mk G
  have hfunctional := (actualColonChain_origin_dictionary_of_local (originalDeformationIdeal d t I) hD
    (Eventually.of_forall fun _ => (deformationParameter d t).differentiableAt) q hf).mpr hcolon
  have hchosen := (hN f).mp ⟨q, hfunctional⟩
  have horigin : HolGerm.mk f hf ∈ originalCoherentOriginIdeal (originalDeformationColonIdeal d t I N) :=
    Ideal.subset_span ⟨f, hf, hchosen, rfl⟩
  have hj := map_linear_originIdeal_le (deformationCentralInclusion d t)
    (originalDeformationColonIdeal d t I N) (Ideal.mem_map_of_mem _ horigin)
  change deformationCentralPullback d t (HolGerm.mk f hf) ∈
    originalCoherentOriginIdeal (originalDeformationCentralIdeal d t I N) at hj
  rwa [hcentral] at hj

theorem exists_local_graph_deformation_domain
    (d t : ℕ) (F : GermIdeal (d+t) (ComplexModel (d+t))) (T : Set (ComplexModel (d+t)))
    (hT : IsOpen T) (h0T : (0 : ComplexModel (d+t)) ∈ T) (hF : CoherentOn F T) :
      let V := (deformationProjection d t) ⁻¹' T
      IsOpen V ∧ 0 ∈ V ∧ CoherentOn (originalDeformationIdeal d t F) V := by
  let V := (deformationProjection d t) ⁻¹' T
  have hV : IsOpen V := hT.preimage (deformationProjection d t).continuous
  have h0V : (0 : ComplexModel (deformationDimension d t)) ∈ V := by
    change deformationProjection d t 0 ∈ T
    simpa only [map_zero] using h0T
  have hpull := coherentOn_pullback_of_local F T hF V hV (deformationProjection d t)
    (fun _ _ => (deformationProjection d t).differentiableAt.mdifferentiableAt) (fun _ hz => hz)
  have hEq := coherentOn_of_isCoherent (deformationEquationIdeal d t)
    (deformationEquationIdeal_isCoherent d t) V hV
  exact ⟨hV, h0V,
    coherentOn_sum _ _ V hpull hEq⟩

theorem exists_local_exact_deformation_central_model
    (d t : ℕ) (F : GermIdeal (d+t) (ComplexModel (d+t))) (T : Set (ComplexModel (d+t)))
    (hT : IsOpen T) (h0T : (0 : ComplexModel (d+t)) ∈ T) (hF : CoherentOn F T) :
      ∃ N : ℕ, ∃ U : Set (ComplexModel (deformationDimension d t)), IsOpen U ∧ 0 ∈ U ∧
        U ⊆ (deformationProjection d t) ⁻¹' T ∧
        CoherentOn (originalDeformationColonIdeal d t F N) U ∧
        (∀ y ∈ U, ∀ q : ℕ, ∀ g, (originalDeformationColonIdeal d t F (N+q)).mem y g ↔
          (originalDeformationColonIdeal d t F N).mem y g) ∧
        (∀ y ∈ U, ∀ q : ℕ, N ≤ q → ∀ g, HolAt g y →
          ((originalDeformationIdeal d t F).mem y (fun z => g z * deformationParameter d t z ^ q) ↔
            (originalDeformationIdeal d t F).mem y (fun z => g z * deformationParameter d t z ^ N))) ∧
        (∀ y ∈ U, ∀ g, (∃ q : ℕ, (originalDeformationColonIdeal d t F q).mem y g) ↔
          (originalDeformationColonIdeal d t F N).mem y g) ∧
        let B := (deformationCentralInclusion d t) ⁻¹' U
        IsOpen B ∧ 0 ∈ B ∧ CoherentOn (originalDeformationCentralIdeal d t F N) B := by
  obtain ⟨hV, h0V, hD⟩ :=
    exists_local_graph_deformation_domain d t F T hT h0T hF
  let V := (deformationProjection d t) ⁻¹' T
  have hfg := idealFGAt_of_coherentOn (originalDeformationIdeal d t F) V hD h0V
  have hh : HolAt (deformationParameter d t) 0 :=
    Eventually.of_forall fun _ => (deformationParameter d t).differentiableAt
  let := isNoetherianRing_holGerm_euclidean (deformationDimension d t)
  obtain ⟨N, V0, hV0, h0V0, _hhV0, hstab, hpow, hsat⟩ :=
    exists_uniform_original_coherent_saturation_union (okaProperty_euclidean (deformationDimension d t)) hfg hh
  have hcolFG : IdealFGAt (originalDeformationColonIdeal d t F N).mem 0 :=
    actualColonChain_finitely_generated (okaProperty_euclidean (deformationDimension d t)) hfg hh N
  obtain ⟨O, hO, h0O, hcolO⟩ := exists_open_coherentOn_of_idealFGAt _ hcolFG
  let U := (V0 ∩ O) ∩ V
  have hU : IsOpen U := (hV0.inter hO).inter hV
  have h0U : (0 : ComplexModel (deformationDimension d t)) ∈ U := ⟨⟨h0V0, h0O⟩, h0V⟩
  have hcolU := coherentOn_restrict (originalDeformationColonIdeal d t F N) O hcolO U hU
    (fun _ hy => hy.1.2)
  let B := (deformationCentralInclusion d t) ⁻¹' U
  have hB : IsOpen B := hU.preimage (deformationCentralInclusion d t).continuous
  have h0B : (0 : ComplexModel (d+t)) ∈ B := by
    change deformationCentralInclusion d t 0 ∈ U
    simpa only [map_zero] using h0U
  have hcentral := coherentOn_pullback_of_local (originalDeformationColonIdeal d t F N) U hcolU B hB
    (deformationCentralInclusion d t)
    (fun _ _ => (deformationCentralInclusion d t).differentiableAt.mdifferentiableAt) (fun _ hy => hy)
  exact ⟨N, U, hU, h0U, (fun _ hy => hy.2), hcolU,
    (fun y hy => hstab y hy.1.1), (fun y hy => hpow y hy.1.1), (fun y hy => hsat y hy.1.1),
    hB, h0B, hcentral⟩


theorem exists_local_central_initial_symbol_memberships
    (d t : ℕ) (F : GermIdeal (d+t) (ComplexModel (d+t))) (T : Set (ComplexModel (d+t)))
    (hT : IsOpen T) (h0T : (0 : ComplexModel (d+t)) ∈ T) (hF : CoherentOn F T) :
    letI := tangentAlgebra d t
      ∃ N : ℕ, ∃ U : Set (ComplexModel (deformationDimension d t)), IsOpen U ∧ 0 ∈ U ∧
        U ⊆ (deformationProjection d t) ⁻¹' T ∧
        CoherentOn (originalDeformationColonIdeal d t F N) U ∧
        (∀ y ∈ U, ∀ q : ℕ, ∀ g, (originalDeformationColonIdeal d t F (N+q)).mem y g ↔
          (originalDeformationColonIdeal d t F N).mem y g) ∧
        (∀ y ∈ U, ∀ q : ℕ, N ≤ q → ∀ g, HolAt g y →
          ((originalDeformationIdeal d t F).mem y (fun z => g z * deformationParameter d t z ^ q) ↔
            (originalDeformationIdeal d t F).mem y (fun z => g z * deformationParameter d t z ^ N))) ∧
        (∀ y ∈ U, ∀ g, (∃ q : ℕ, (originalDeformationColonIdeal d t F q).mem y g) ↔
          (originalDeformationColonIdeal d t F N).mem y g) ∧
        let B := (deformationCentralInclusion d t) ⁻¹' U
        IsOpen B ∧ 0 ∈ B ∧ CoherentOn (originalDeformationCentralIdeal d t F N) B ∧
        ∀ (q : ℕ) (g : HolGerm (ComplexModel (d+t)))
          (_hIg : g ∈ originalCoherentOriginIdeal F) (hg : g ∈ normalIdeal d t ^ q),
          normalPolynomialEval d t (originalNormalInitialSymbol d t q g hg) ∈
            originalCoherentOriginIdeal (originalDeformationCentralIdeal d t F N) := by
  let := tangentAlgebra d t
  obtain ⟨N, U, hU, h0U, hUV, hcol, hchain, hpow, hsat, hB, h0B, hcent⟩ :=
    exists_local_exact_deformation_central_model d t F T hT h0T hF
  let V := (deformationProjection d t) ⁻¹' T
  have hV : IsOpen V := hT.preimage (deformationProjection d t).continuous
  have h0V : (0 : ComplexModel (deformationDimension d t)) ∈ V := by
    change deformationProjection d t 0 ∈ T
    simpa only [map_zero] using h0T
  have hpull := coherentOn_pullback_of_local F T hF V hV (deformationProjection d t)
    (fun _ _ => (deformationProjection d t).differentiableAt.mdifferentiableAt) (fun _ hz => hz)
  have hEq := coherentOn_of_isCoherent (deformationEquationIdeal d t)
    (deformationEquationIdeal_isCoherent d t) V hV
  have hD := coherentOn_sum _ _ V hpull hEq
  have hfg := idealFGAt_of_coherentOn (originalDeformationIdeal d t F) V hD h0V
  exact ⟨N, U, hU, h0U, hUV, hcol, hchain, hpow, hsat, hB, h0B, hcent,
    fun q g hIg hg => initialSymbol_mem_selected_central_local d t F hfg N (hsat 0 h0U) q g hIg hg⟩

theorem exists_local_central_initial_ideal_inclusion
    (d t : ℕ) (F : GermIdeal (d+t) (ComplexModel (d+t))) (T : Set (ComplexModel (d+t)))
    (hT : IsOpen T) (h0T : (0 : ComplexModel (d+t)) ∈ T) (hF : CoherentOn F T) :
    letI := tangentAlgebra d t
      ∃ N : ℕ, ∃ U : Set (ComplexModel (deformationDimension d t)), IsOpen U ∧ 0 ∈ U ∧
        U ⊆ (deformationProjection d t) ⁻¹' T ∧
        CoherentOn (originalDeformationColonIdeal d t F N) U ∧
        (∀ y ∈ U, ∀ q : ℕ, ∀ g, (originalDeformationColonIdeal d t F (N+q)).mem y g ↔
          (originalDeformationColonIdeal d t F N).mem y g) ∧
        (∀ y ∈ U, ∀ q : ℕ, N ≤ q → ∀ g, HolAt g y →
          ((originalDeformationIdeal d t F).mem y (fun z => g z * deformationParameter d t z ^ q) ↔
            (originalDeformationIdeal d t F).mem y (fun z => g z * deformationParameter d t z ^ N))) ∧
        (∀ y ∈ U, ∀ g, (∃ q : ℕ, (originalDeformationColonIdeal d t F q).mem y g) ↔
          (originalDeformationColonIdeal d t F N).mem y g) ∧
        let B := (deformationCentralInclusion d t) ⁻¹' U
        IsOpen B ∧ 0 ∈ B ∧ CoherentOn (originalDeformationCentralIdeal d t F N) B ∧
        Ideal.map (normalPolynomialEval d t).toRingHom
          (originalNormalInitialIdeal d t (originalCoherentOriginIdeal F)) ≤
            originalCoherentOriginIdeal (originalDeformationCentralIdeal d t F N) := by
  let := tangentAlgebra d t
  obtain ⟨N, U, hU, h0U, hUV, hcol, hchain, hpow, hsat, hB, h0B, hcent, hsymbols⟩ :=
    exists_local_central_initial_symbol_memberships d t F T hT h0T hF
  refine ⟨N, U, hU, h0U, hUV, hcol, hchain, hpow, hsat, hB, h0B, hcent, ?_⟩
  apply Ideal.map_le_iff_le_comap.mpr
  rw [originalNormalInitialIdeal_eq_span_original_relations]
  apply Ideal.span_le.mpr
  rintro P ⟨a, rfl⟩
  exact hsymbols a.1 a.2.val a.2.property.1 a.2.property.2


theorem exists_local_whole_graph_model
    (d t : ℕ) (F : GermIdeal (d+t) (ComplexModel (d+t))) (T : Set (ComplexModel (d+t)))
    (hT : IsOpen T) (h0T : (0 : ComplexModel (d+t)) ∈ T) (hF : CoherentOn F T) :
    letI := tangentAlgebra d t
      ∃ N : ℕ, ∃ U : Set (ComplexModel (deformationDimension d t)), IsOpen U ∧ 0 ∈ U ∧
        U ⊆ (deformationProjection d t) ⁻¹' T ∧
        CoherentOn (originalDeformationColonIdeal d t F N) U ∧
        (∀ y ∈ U, ∀ q : ℕ, ∀ g, (originalDeformationColonIdeal d t F (N+q)).mem y g ↔
          (originalDeformationColonIdeal d t F N).mem y g) ∧
        (∀ y ∈ U, ∀ q : ℕ, N ≤ q → ∀ g, HolAt g y →
          ((originalDeformationIdeal d t F).mem y (fun z => g z * deformationParameter d t z ^ q) ↔
            (originalDeformationIdeal d t F).mem y (fun z => g z * deformationParameter d t z ^ N))) ∧
        (∀ y ∈ U, ∀ g, (∃ q : ℕ, (originalDeformationColonIdeal d t F q).mem y g) ↔
          (originalDeformationColonIdeal d t F N).mem y g) ∧
        let B := (deformationCentralInclusion d t) ⁻¹' U
        IsOpen B ∧ 0 ∈ B ∧ CoherentOn (originalDeformationCentralIdeal d t F N) B ∧
        Ideal.map (normalPolynomialEval d t).toRingHom
          (originalNormalInitialIdeal d t (originalCoherentOriginIdeal F)) ≤
            originalCoherentOriginIdeal (originalDeformationCentralIdeal d t F N) ∧
        (∀ q : ℕ, originalCoherentOriginIdeal (originalDeformationCentralIdeal d t F q) =
          Ideal.map (graphCentralPullback d t).toRingHom (actualGraphColonIdeal d t F q)) ∧
        (∀ q : ℕ, actualGraphColonIdeal d t F (N+q) = actualGraphColonIdeal d t F N) ∧
        (∀ g, (∃ q : ℕ, g ∈ actualGraphColonIdeal d t F q) ↔ g ∈ actualGraphColonIdeal d t F N) ∧
        ∃ e : (HolGerm (ComplexModel (deformationDimension d t)) ⧸
            originalCoherentOriginIdeal (originalDeformationIdeal d t F)) ≃+*
          (HolGerm (ComplexModel (graphDimension d t)) ⧸ actualGraphScaledIdeal d t F),
          ∀ g : HolGerm (ComplexModel (deformationDimension d t)),
            e (Ideal.Quotient.mk _ g) = Ideal.Quotient.mk _ (graphTrace d t g) := by
  let := tangentAlgebra d t
  obtain ⟨N, U, hU, h0U, hUV, hcol, hchain, hpow, hsat, hB, h0B, hcent, hforward⟩ :=
    exists_local_central_initial_ideal_inclusion d t F T hT h0T hF
  let V := (deformationProjection d t) ⁻¹' T
  have hV : IsOpen V := hT.preimage (deformationProjection d t).continuous
  have h0V : (0 : ComplexModel (deformationDimension d t)) ∈ V := by
    change deformationProjection d t 0 ∈ T
    simpa only [map_zero] using h0T
  have hIFG := idealFGAt_of_coherentOn F T hF h0T
  have hpull := coherentOn_pullback_of_local F T hF V hV (deformationProjection d t)
    (fun _ _ => (deformationProjection d t).differentiableAt.mdifferentiableAt) (fun _ hz => hz)
  have hEq := coherentOn_of_isCoherent (deformationEquationIdeal d t)
    (deformationEquationIdeal_isCoherent d t) V hV
  have hD := coherentOn_sum _ _ V hpull hEq
  have hDFG := idealFGAt_of_coherentOn (originalDeformationIdeal d t F) V hD h0V
  have hpar : HolAt (deformationParameter d t) 0 :=
    Eventually.of_forall fun _ => (deformationParameter d t).differentiableAt
  have hring : ∀ q : ℕ,
      actualOriginColonChain (originalCoherentOriginIdeal (originalDeformationIdeal d t F))
        (deformationParameterGerm d t) (N+q) =
      actualOriginColonChain (originalCoherentOriginIdeal (originalDeformationIdeal d t F))
        (deformationParameterGerm d t) N := by
    intro q
    ext g
    induction g using HolGerm.induction_on with
    | h f hf =>
      change HolGerm.mk f hf ∈ actualOriginColonChain
        (originalCoherentOriginIdeal (originalDeformationIdeal d t F))
        (HolGerm.mk (deformationParameter d t) hpar) (N+q) ↔
        HolGerm.mk f hf ∈ actualOriginColonChain
        (originalCoherentOriginIdeal (originalDeformationIdeal d t F))
        (HolGerm.mk (deformationParameter d t) hpar) N
      rw [← actualColonChain_origin_dictionary_of_local (originalDeformationIdeal d t F) hDFG hpar (N+q) hf,
        ← actualColonChain_origin_dictionary_of_local (originalDeformationIdeal d t F) hDFG hpar N hf]
      exact hchain 0 h0U q f
  have hgraph : ∀ q : ℕ, actualGraphColonIdeal d t F (N+q) = actualGraphColonIdeal d t F N := by
    intro q
    rw [← graphTrace_map_originalOriginColon_of_local d t F hIFG (N+q),
      ← graphTrace_map_originalOriginColon_of_local d t F hIFG N, hring q]
  have hgraphSat : ∀ g, (∃ q : ℕ, g ∈ actualGraphColonIdeal d t F q) ↔
      g ∈ actualGraphColonIdeal d t F N := by
    intro g
    constructor
    · rintro ⟨q, hg⟩
      let G := graphBasePullback d t g
      have hGq : G ∈ actualOriginColonChain (originalCoherentOriginIdeal (originalDeformationIdeal d t F))
          (deformationParameterGerm d t) q := by
        rw [originalOriginColon_eq_graphTrace_comap_of_local d t F hIFG q]
        change graphTrace d t (graphBasePullback d t g) ∈ actualGraphColonIdeal d t F q
        rw [graphTrace_graphBasePullback]
        exact hg
      obtain ⟨f, hf, hG⟩ := HolGerm.exists_eq_mk G
      rw [hG] at hGq
      have hqfunc := (actualColonChain_origin_dictionary_of_local (originalDeformationIdeal d t F) hDFG hpar q hf).mpr hGq
      have hNfunc := (hsat 0 h0U f).mp ⟨q, hqfunc⟩
      have hGN := (actualColonChain_origin_dictionary_of_local (originalDeformationIdeal d t F) hDFG hpar N hf).mp hNfunc
      rw [← hG] at hGN
      change G ∈ actualOriginColonChain (originalCoherentOriginIdeal (originalDeformationIdeal d t F))
        (deformationParameterGerm d t) N at hGN
      rw [originalOriginColon_eq_graphTrace_comap_of_local d t F hIFG N] at hGN
      change graphTrace d t (graphBasePullback d t g) ∈ actualGraphColonIdeal d t F N at hGN
      rwa [graphTrace_graphBasePullback] at hGN
    · exact fun hg => ⟨N, hg⟩
  exact ⟨N, U, hU, h0U, hUV, hcol, hchain, hpow, hsat, hB, h0B, hcent,
    hforward, fun q => originalCentralOriginIdeal_eq_graphColon_image_of_local d t F hIFG hDFG q,
    hgraph, hgraphSat, originalGraphQuotientEquiv_of_local d t F hIFG,
    fun g => originalGraphQuotientEquiv_apply_mk_of_local d t F hIFG g⟩


theorem exists_local_whole_central_initial_equality
    (d t : ℕ) (F : GermIdeal (d+t) (ComplexModel (d+t))) (T : Set (ComplexModel (d+t)))
    (hT : IsOpen T) (h0T : (0 : ComplexModel (d+t)) ∈ T) (hF : CoherentOn F T) :
    letI := tangentAlgebra d t
      ∃ N : ℕ, ∃ U : Set (ComplexModel (deformationDimension d t)), IsOpen U ∧ 0 ∈ U ∧
        U ⊆ (deformationProjection d t) ⁻¹' T ∧
        CoherentOn (originalDeformationColonIdeal d t F N) U ∧
        (∀ y ∈ U, ∀ q : ℕ, ∀ g, (originalDeformationColonIdeal d t F (N+q)).mem y g ↔
          (originalDeformationColonIdeal d t F N).mem y g) ∧
        (∀ y ∈ U, ∀ q : ℕ, N ≤ q → ∀ g, HolAt g y →
          ((originalDeformationIdeal d t F).mem y (fun z => g z * deformationParameter d t z ^ q) ↔
            (originalDeformationIdeal d t F).mem y (fun z => g z * deformationParameter d t z ^ N))) ∧
        (∀ y ∈ U, ∀ g, (∃ q : ℕ, (originalDeformationColonIdeal d t F q).mem y g) ↔
          (originalDeformationColonIdeal d t F N).mem y g) ∧
        let B := (deformationCentralInclusion d t) ⁻¹' U
        IsOpen B ∧ 0 ∈ B ∧ CoherentOn (originalDeformationCentralIdeal d t F N) B ∧
        originalCoherentOriginIdeal (originalDeformationCentralIdeal d t F N) =
          Ideal.map (normalPolynomialEval d t).toRingHom
            (originalNormalInitialIdeal d t (originalCoherentOriginIdeal F)) ∧
        (∀ q : ℕ, originalCoherentOriginIdeal (originalDeformationCentralIdeal d t F q) =
          Ideal.map (graphCentralPullback d t).toRingHom (actualGraphColonIdeal d t F q)) ∧
        (∀ q : ℕ, actualGraphColonIdeal d t F (N+q) = actualGraphColonIdeal d t F N) ∧
        (∀ g, (∃ q : ℕ, g ∈ actualGraphColonIdeal d t F q) ↔ g ∈ actualGraphColonIdeal d t F N) ∧
        ∃ eGraph : (HolGerm (ComplexModel (deformationDimension d t)) ⧸
            originalCoherentOriginIdeal (originalDeformationIdeal d t F)) ≃+*
          (HolGerm (ComplexModel (graphDimension d t)) ⧸ actualGraphScaledIdeal d t F),
        ∃ eCentral : (HolGerm (ComplexModel (d+t)) ⧸
            Ideal.map (normalPolynomialEval d t).toRingHom
              (originalNormalInitialIdeal d t (originalCoherentOriginIdeal F))) ≃+*
          (HolGerm (ComplexModel (d+t)) ⧸
            originalCoherentOriginIdeal (originalDeformationCentralIdeal d t F N)),
          (∀ g : HolGerm (ComplexModel (deformationDimension d t)),
            eGraph (Ideal.Quotient.mk _ g) = Ideal.Quotient.mk _ (graphTrace d t g)) ∧
          (∀ g : HolGerm (ComplexModel (d+t)),
            eCentral (Ideal.Quotient.mk _ g) = Ideal.Quotient.mk _ g) := by
  let := tangentAlgebra d t
  obtain ⟨N, U, hU, h0U, hUV, hcol, hchain, hpow, hsat, hB, h0B,
    hcent, hforward, hcentral, hgraph, hgraphSat, eGraph, heGraph⟩ :=
    exists_local_whole_graph_model d t F T hT h0T hF
  have hreverse : originalCoherentOriginIdeal (originalDeformationCentralIdeal d t F N) ≤
      Ideal.map (normalPolynomialEval d t).toRingHom
        (originalNormalInitialIdeal d t (originalCoherentOriginIdeal F)) := by
    rw [hcentral N]
    apply Ideal.map_le_iff_le_comap.mpr
    intro h hh
    exact actual_graph_colon_central_mem_initial_image d t N F h hh
  have heq := hreverse.antisymm hforward
  exact ⟨N, U, hU, h0U, hUV, hcol, hchain, hpow, hsat, hB, h0B,
    hcent, heq, hcentral, hgraph, hgraphSat, eGraph, Ideal.quotEquivOfEq heq.symm,
    heGraph, fun g => Ideal.quotEquivOfEq_mk heq.symm g⟩


end
end Hironaka.Analytic.Unibranch.HironakaG10GnLocalCentral
