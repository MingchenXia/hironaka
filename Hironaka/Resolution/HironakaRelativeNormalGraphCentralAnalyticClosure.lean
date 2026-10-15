/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalGraphCentralInitialSymbols
import Mathlib.RingTheory.Filtration

/-! Four complete mathematical proofs preceded this OWN OFFLIB continuation.
LSP is unavailable; every edit is followed by a serialized narrow kernel check.
The genuine origin reverse inclusion does not assert a nearby Rees dictionary. -/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaRelativeNormalGraphCentralAnalyticClosure
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalIdealMatrices HironakaRelativeNormalAssociatedGraded
  HironakaRelativeNormalPolynomialJetAlgebra HironakaRelativeNormalDeformationInitialRelations
  HironakaRelativeNormalAnalyticGraphQuotient HironakaRelativeNormalDeformationSaturation
  HironakaRelativeNormalGraphWeightJets HironakaRelativeNormalGraphWeightComponents
  HironakaRelativeNormalGraphDiagonalCoefficients HironakaRelativeNormalGraphCentralInitialSymbols

theorem actual_ideal_mem_of_all_normal_approximations
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (A J : Ideal R) (hJ : J ≠ ⊤) (g : R)
    (hg : ∀ q : ℕ, g ∈ A ⊔ J^q) : g ∈ A := by
  have hclass : (Ideal.Quotient.mk A g) ∈
      (⨅ q : ℕ, J^q • ⊤ : Submodule R (R ⧸ A)) := by
    rw [Submodule.mem_iInf]
    intro q
    obtain ⟨a,ha,b,hb,hab⟩ := Submodule.mem_sup.mp (hg q)
    have ha0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha
    have hsmul : b • (1 : R ⧸ A) ∈ (J^q • ⊤ : Submodule R (R ⧸ A)) :=
      Submodule.smul_mem_smul hb (Submodule.mem_top)
    have he : Ideal.Quotient.mk A g = b • (1 : R ⧸ A) := by
      rw [← hab,map_add,ha0,zero_add]
      change algebraMap R (R ⧸ A) b = _
      simp only [Algebra.smul_def,mul_one]
    rw [he]
    exact hsmul
  rw [J.iInf_pow_smul_eq_bot_of_isLocalRing (M := R ⧸ A) hJ] at hclass
  exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using hclass)

theorem actual_normalIdeal_ne_top (d t : ℕ) : normalIdeal d t ≠ ⊤ := by
  intro htop
  have hone : (1 : HolGerm (ComplexModel (d+t))) ∈ normalIdeal d t := by
    rw [htop]
    simp
  rw [normalIdeal_eq_ker_planeTrace] at hone
  have hzero : planeTrace d t 1 = 0 := hone
  exact one_ne_zero (by simpa only [map_one] using hzero)

theorem exists_actual_bounded_normal_polynomial_jet (d t q : ℕ)
    (g : HolGerm (ComplexModel (d+t))) :
    ∃ Q : MvPolynomial (Fin t) (HolGerm (ComplexModel d)),
      (g-normalPolynomialEval d t Q ∈ normalIdeal d t^q) ∧
      ∀ α : Fin t →₀ ℕ, q ≤ normalExponentDegree α → MvPolynomial.coeff α Q = 0 := by
  classical
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  obtain ⟨a,ha⟩ := exists_normalMonomial_coefficient_representative d t q g
  refine ⟨∑ β : normalExponentIndex t q, MvPolynomial.monomial β.val (a β),?_,?_⟩
  · simpa only [map_sum,normalPolynomialEval_monomial] using ha
  · intro α hα
    rw [MvPolynomial.coeff_sum]
    apply Finset.sum_eq_zero
    intro β _
    have hne : β.val ≠ α := by
      intro he
      have hb := β.property
      rw [he] at hb
      omega
    simp only [MvPolynomial.coeff_monomial,if_neg hne]

theorem actual_homogeneous_part_eq_of_same_normal_jet (d t k : ℕ)
    (P Q : MvPolynomial (Fin t) (HolGerm (ComplexModel d)))
    (hPQ : normalPolynomialEval d t P-normalPolynomialEval d t Q ∈ normalIdeal d t^(k+1)) :
    MvPolynomial.weightedHomogeneousComponent (fun _ : Fin t => (1 : ℕ)) k P =
      MvPolynomial.weightedHomogeneousComponent (fun _ : Fin t => (1 : ℕ)) k Q := by
  classical
  apply MvPolynomial.ext
  intro α
  simp only [MvPolynomial.coeff_weightedHomogeneousComponent]
  split_ifs with hα
  · have hd : normalExponentDegree α = k := by
      rwa [actualGraph_unitWeight_degree] at hα
    have he := coefficient_eq_zero_of_normalPolynomialEval_mem d t (k+1) (P-Q) α
      (by omega) (by simpa only [map_sub] using hPQ)
    rw [MvPolynomial.coeff_sub] at he
    exact sub_eq_zero.mp he
  · rfl

theorem exists_original_coherent_all_graph_central_initial_approximations (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    let := tangentAlgebra d t
    ∃ N : ℕ, ∃ U : Set (ComplexModel (deformationDimension d t)), IsOpen U ∧ 0 ∈ U ∧
      (∀ q : ℕ, actualGraphColonIdeal d t I (N+q) = actualGraphColonIdeal d t I N) ∧
      (∀ y ∈ U, ∀ q : ℕ, ∀ f,
        (originalDeformationColonIdeal d t I (N+q)).mem y f ↔
          (originalDeformationColonIdeal d t I N).mem y f) ∧
      ∀ h : HolGerm (ComplexModel (graphDimension d t)),
        (∃ q : ℕ, h ∈ actualGraphColonIdeal d t I q) → ∀ q : ℕ,
        graphCentralPullback d t h ∈
          Ideal.map (normalPolynomialEval d t).toRingHom
            (originalNormalInitialIdeal d t (originalCoherentOriginIdeal I)) ⊔ normalIdeal d t^q := by
  classical
  let := tangentAlgebra d t
  obtain ⟨N,U,hU,h0,hgraph,hchain,hproduce⟩ :=
    exists_original_coherent_all_graph_central_initial_symbols d t I hI
  refine ⟨N,U,hU,h0,hgraph,hchain,?_⟩
  intro h hsat q
  obtain ⟨Q,hQ,hbound⟩ := exists_actual_bounded_normal_polynomial_jet d t q
    (graphCentralPullback d t h)
  let HI := originalNormalInitialIdeal d t (originalCoherentOriginIdeal I)
  have hparts : ∀ k : ℕ,
      MvPolynomial.weightedHomogeneousComponent (fun _ : Fin t => (1 : ℕ)) k Q ∈ HI := by
    intro k
    by_cases hk : k < q
    · obtain ⟨H,_F,hH,_hFI,_hFk,_hSymbol,hHmem⟩ := hproduce h hsat k
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

theorem exists_original_coherent_whole_graph_central_reverse_inclusion (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    let := tangentAlgebra d t
    ∃ N : ℕ, ∃ U : Set (ComplexModel (deformationDimension d t)), IsOpen U ∧ 0 ∈ U ∧
      (∀ q : ℕ, actualGraphColonIdeal d t I (N+q) = actualGraphColonIdeal d t I N) ∧
      (∀ y ∈ U, ∀ q : ℕ, ∀ f,
        (originalDeformationColonIdeal d t I (N+q)).mem y f ↔
          (originalDeformationColonIdeal d t I N).mem y f) ∧
      (∀ h : HolGerm (ComplexModel (graphDimension d t)),
        (∃ q : ℕ, h ∈ actualGraphColonIdeal d t I q) →
        graphCentralPullback d t h ∈ Ideal.map (normalPolynomialEval d t).toRingHom
          (originalNormalInitialIdeal d t (originalCoherentOriginIdeal I))) ∧
      originalCoherentOriginIdeal (originalDeformationCentralIdeal d t I N) ≤
        Ideal.map (normalPolynomialEval d t).toRingHom
          (originalNormalInitialIdeal d t (originalCoherentOriginIdeal I)) := by
  let := isNoetherianRing_holGerm_euclidean (d+t)
  let := tangentAlgebra d t
  obtain ⟨N,U,hU,h0,hgraph,hchain,happrox⟩ :=
    exists_original_coherent_all_graph_central_initial_approximations d t I hI
  let AH := Ideal.map (normalPolynomialEval d t).toRingHom
    (originalNormalInitialIdeal d t (originalCoherentOriginIdeal I))
  have hwhole : ∀ h : HolGerm (ComplexModel (graphDimension d t)),
      (∃ q : ℕ, h ∈ actualGraphColonIdeal d t I q) → graphCentralPullback d t h ∈ AH := by
    intro h hsat
    exact actual_ideal_mem_of_all_normal_approximations AH (normalIdeal d t)
      (actual_normalIdeal_ne_top d t) (graphCentralPullback d t h) (happrox h hsat)
  refine ⟨N,U,hU,h0,hgraph,hchain,hwhole,?_⟩
  rw [originalCentralOriginIdeal_eq_graphColon_image d t I hI N]
  apply Ideal.map_le_iff_le_comap.mpr
  intro h hh
  exact hwhole h ⟨N,hh⟩

end
end Hironaka.HironakaRelativeNormalGraphCentralAnalyticClosure
