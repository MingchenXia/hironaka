/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothCentreRealDomainGraphDictionary
import Hironaka.Resolution.HironakaRelativeNormalGraphCentralAnalyticClosure

/-! # Exact whole original real central and initial ideal equality
Complete three-node mathematics precedes source. An actual graph colon member
internally supplies its finite whole original relation at that exponent.
True analytic reconstruction and Krull closure give the entire reverse inclusion
without any global coherence premise. Pure original inputs supply the SAME real
Phi/N/U/B and both exact quotient representative dictionaries.
-/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaSmoothCentreRealDomainInitialEquality
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf OkaIdealOperations
  HironakaSmoothCentreCoherentDomain HironakaSmoothCentreRealDomainGraphDictionary
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis HironakaRelativeNormalIdealMatrices
  HironakaRelativeNormalAssociatedGraded HironakaRelativeNormalPolynomialJetAlgebra
  HironakaRelativeNormalDeformationInitialRelations HironakaRelativeNormalDeformationSaturation
  HironakaRelativeNormalAnalyticGraphQuotient HironakaRelativeNormalGraphWeightJets
  HironakaRelativeNormalGraphWeightComponents HironakaRelativeNormalGraphDiagonalCoefficients
  HironakaRelativeNormalGraphAnalyticFiniteRelations HironakaRelativeNormalGraphWeightAnalyticReconstruction
  HironakaRelativeNormalGraphCentralInitialSymbols HironakaRelativeNormalGraphCentralAnalyticClosure
  HironakaHolomorphicJetChartInvariance

/-- A single ACTUAL whole graph-colon member supplies every genuine original central initial symbol. -/
theorem exists_actual_graph_colon_original_initial_symbols (d t N : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t)))
    (h : HolGerm (ComplexModel (graphDimension d t))) (hh : h ∈ actualGraphColonIdeal d t I N)
    (k : ℕ) :
    ∃ H : MvPolynomial (Fin (1+t)) (HolGerm (ComplexModel d)),
      ∃ F : HolGerm (ComplexModel (d+t)),
        (h-normalPolynomialEval d (1+t) H ∈ normalIdeal d (1+t)^(N+k+1)) ∧
        F ∈ originalCoherentOriginIdeal I ∧
        ∃ hFk : F ∈ normalIdeal d t^k,
          originalNormalInitialSymbol d t k F hFk = actualGraphCentralHomogeneousPart d t k H ∧
          actualGraphCentralHomogeneousPart d t k H ∈ originalNormalInitialIdeal d t (originalCoherentOriginIdeal I) := by
  obtain ⟨m,g,a,hg,heq⟩ := exists_actual_graph_colon_finite_original_germ_relation d t N I h hh
  obtain ⟨H,F,hH,hFI,hscaled⟩ := exists_actual_graph_weight_entire_original_reconstruction d t N k m I g a h hg heq
  let C := actualGraphCentralHomogeneousPart d t k H
  have hC : C.IsHomogeneous k := actualGraphCentralHomogeneousPart_homogeneous d t k H
  have hp := (normalPolynomialEval_mem_power_iff d (1+t) (2*k+1) _).mpr
    (actualGraph_negative_weight_central_jet_congruence d t k H)
  rw [map_sub,← actualGraphScalingGerm_polynomialEval] at hp
  have hs : actualGraphScalingGerm d t (F-normalPolynomialEval d t C) ∈ normalIdeal d (1+t)^(2*k+1) := by
    have ha := (normalIdeal d (1+t)^(2*k+1)).add_mem hscaled hp
    rw [map_sub]
    convert ha using 1
    ring
  have hrem := (actualGraphScalingGerm_odd_power_iff d t k _).mp hs
  have hFk : F ∈ normalIdeal d t^k := by
    have hv := normalPolynomialEval_mem_pow_of_homogeneous d t k C hC
    have hm := (normalIdeal d t^k).add_mem
      (Ideal.pow_le_pow_right (by omega : k ≤ k+1) hrem) hv
    simpa only [sub_add_cancel] using hm
  have he : originalNormalInitialSymbol d t k F hFk = C := by
    apply homogeneous_normal_polynomial_unique d t k _ C
      (originalNormalInitialSymbol_homogeneous d t k F hFk) hC
    have hm := (normalIdeal d t^(k+1)).sub_mem hrem
      (originalNormalInitialSymbol_remainder d t k F hFk)
    convert hm using 1
    ring
  have hmem := originalNormalRelation_mem_initialIdeal d t (originalCoherentOriginIdeal I) ⟨k,⟨F,hFI,hFk⟩⟩
  change originalNormalInitialSymbol d t k F hFk ∈ originalNormalInitialIdeal d t (originalCoherentOriginIdeal I) at hmem
  rw [he] at hmem
  exact ⟨H,F,hH,hFI,hFk,he,hmem⟩

/-- Whole central restriction of a single actual graph-colon germ has EVERY genuine initial-ideal approximation. -/
theorem actual_graph_colon_central_all_initial_approximations (d t N : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t)))
    (h : HolGerm (ComplexModel (graphDimension d t))) (hh : h ∈ actualGraphColonIdeal d t I N) :
    letI := tangentAlgebra d t
    ∀ q : ℕ, graphCentralPullback d t h ∈
      Ideal.map (normalPolynomialEval d t).toRingHom
        (originalNormalInitialIdeal d t (originalCoherentOriginIdeal I)) ⊔ normalIdeal d t^q := by
  classical
  let := tangentAlgebra d t
  intro q
  obtain ⟨Q,hQ,hbound⟩ := exists_actual_bounded_normal_polynomial_jet d t q
    (graphCentralPullback d t h)
  let HI := originalNormalInitialIdeal d t (originalCoherentOriginIdeal I)
  have hparts : ∀ k : ℕ,
      MvPolynomial.weightedHomogeneousComponent (fun _ : Fin t => (1 : ℕ)) k Q ∈ HI := by
    intro k
    by_cases hk : k < q
    · obtain ⟨H,_F,hH,_hFI,_hFk,_hSymbol,hHmem⟩ := exists_actual_graph_colon_original_initial_symbols d t N I h hh k
      have hcentral := graphCentralPullback_actual_mem_normal_power d t (N+k+1) _ hH
      rw [map_sub,graphCentralPullback_actual_polynomialEval] at hcentral
      have hP : graphCentralPullback d t h -
          normalPolynomialEval d t (actualGraphCentralPolynomial d t H) ∈ normalIdeal d t^(k+1) :=
        Ideal.pow_le_pow_right (by omega : k+1 ≤ N+k+1) hcentral
      have hQl : graphCentralPullback d t h-normalPolynomialEval d t Q ∈ normalIdeal d t^(k+1) :=
        Ideal.pow_le_pow_right (by omega : k+1 ≤ q) hQ
      have hPQ : normalPolynomialEval d t Q-
          normalPolynomialEval d t (actualGraphCentralPolynomial d t H) ∈ normalIdeal d t^(k+1) := by
        have hd := (normalIdeal d t^(k+1)).sub_mem hP hQl
        convert hd using 1
        ring
      have he := actual_homogeneous_part_eq_of_same_normal_jet d t k Q
        (actualGraphCentralPolynomial d t H) hPQ
      change MvPolynomial.weightedHomogeneousComponent (fun _ : Fin t => (1 : ℕ)) k Q =
        actualGraphCentralHomogeneousPart d t k H at he
      rw [he]
      exact hHmem
    · have hz : MvPolynomial.weightedHomogeneousComponent (fun _ : Fin t => (1 : ℕ)) k Q = 0 := by
        apply MvPolynomial.ext
        intro α
        rw [MvPolynomial.coeff_weightedHomogeneousComponent,MvPolynomial.coeff_zero]
        split_ifs with hα
        · apply hbound
          rw [actualGraph_unitWeight_degree] at hα
          omega
        · rfl
      rw [hz]
      exact HI.zero_mem
  have hQH : Q ∈ HI := by
    rw [← MvPolynomial.sum_weightedHomogeneousComponent (fun _ : Fin t => (1 : ℕ)) Q]
    rw [finsum_eq_sum _ (MvPolynomial.weightedHomogeneousComponent_finsupp
      (w := fun _ : Fin t => (1 : ℕ)) Q)]
    apply Ideal.sum_mem
    intro k _
    exact hparts k
  have hEval := Ideal.mem_map_of_mem (normalPolynomialEval d t).toRingHom hQH
  exact Submodule.mem_sup.mpr ⟨normalPolynomialEval d t Q,hEval,
    graphCentralPullback d t h-normalPolynomialEval d t Q,hQ,by ring⟩
/-- Every ENTIRE actual graph-colon central image lies in the WHOLE analytic original initial image. -/
theorem actual_graph_colon_central_mem_initial_image (d t N : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t)))
    (h : HolGerm (ComplexModel (graphDimension d t))) (hh : h ∈ actualGraphColonIdeal d t I N) :
    letI := tangentAlgebra d t
    graphCentralPullback d t h ∈ Ideal.map (normalPolynomialEval d t).toRingHom
      (originalNormalInitialIdeal d t (originalCoherentOriginIdeal I)) := by
  let := isNoetherianRing_holGerm_euclidean (d+t)
  let := tangentAlgebra d t
  exact actual_ideal_mem_of_all_normal_approximations
    (Ideal.map (normalPolynomialEval d t).toRingHom (originalNormalInitialIdeal d t (originalCoherentOriginIdeal I)))
    (normalIdeal d t) (actual_normalIdeal_ne_top d t) (graphCentralPullback d t h)
    (actual_graph_colon_central_all_initial_approximations d t N I h hh)

section Original
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- Pure original inputs internally supply actual WHOLE central equality and both entire representative quotient formulas. -/
theorem exists_original_regular_real_whole_central_initial_equality
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent) :
    letI := tangentAlgebra d t
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target ∧
      ∃ _h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x) = 0,
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) ∧
      ∃ N : ℕ, ∃ U : Set (ComplexModel (deformationDimension d t)), IsOpen U ∧ 0 ∈ U ∧
        U ⊆ (deformationProjection d t) ⁻¹' Φ.target ∧
        let F := actualFlattenedOriginalSheaf A x Φ
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
  obtain ⟨Φ, hsrc, h0, hflat, N, U, hU, h0U, hUV, hcol, hchain, hpow, hsat, hB, h0B,
    hcent, hforward, hcentral, hgraph, hgraphSat, eGraph, heGraph⟩ :=
    exists_original_regular_real_whole_graph_model C x hreg A hA
  let F := actualFlattenedOriginalSheaf A x Φ
  have hreverse : originalCoherentOriginIdeal (originalDeformationCentralIdeal d t F N) ≤
      Ideal.map (normalPolynomialEval d t).toRingHom
        (originalNormalInitialIdeal d t (originalCoherentOriginIdeal F)) := by
    rw [hcentral N]
    apply Ideal.map_le_iff_le_comap.mpr
    intro h hh
    exact actual_graph_colon_central_mem_initial_image d t N F h hh
  have heq := hreverse.antisymm hforward
  exact ⟨Φ, hsrc, h0, hflat, N, U, hU, h0U, hUV, hcol, hchain, hpow, hsat, hB, h0B,
    hcent, heq, hcentral, hgraph, hgraphSat, eGraph, Ideal.quotEquivOfEq heq.symm,
    heGraph, fun g => Ideal.quotEquivOfEq_mk heq.symm g⟩

end Original
end
end Hironaka.HironakaSmoothCentreRealDomainInitialEquality
