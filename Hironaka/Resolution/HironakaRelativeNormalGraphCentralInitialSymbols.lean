/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalGraphDiagonalCoefficients

/-! Actual initial symbols in the WHOLE original ideal from genuine saturated
central graph jets. Three complete mathematical proofs preceded Lean.
OWN OFFLIB only; whole analytic central closure/nearby cone/ALLq OPEN. -/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaRelativeNormalGraphCentralInitialSymbols
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalIdealMatrices
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetMonomialSpan
  HironakaRelativeNormalAssociatedGraded HironakaRelativeNormalPolynomialJetAlgebra
  HironakaRelativeNormalDeformationInitialRelations HironakaRelativeNormalAnalyticGraphQuotient
  HironakaRelativeNormalDeformationSaturation HironakaRelativeNormalGraphWeightJets
  HironakaRelativeNormalGraphWeightComponents HironakaRelativeNormalGraphWeightAnalyticReconstruction
  HironakaRelativeNormalGraphDiagonalCoefficients

private theorem exists_actual_original_polynomial_jet (d t L : ℕ)
    (g : HolGerm (ComplexModel (d+t))) :
    ∃ P : MvPolynomial (Fin t) (HolGerm (ComplexModel d)),
      g-normalPolynomialEval d t P ∈ normalIdeal d t^L := by
  classical
  let := tangentAlgebra d t
  let := normalExponentFintype t L
  obtain ⟨a,ha⟩ := exists_normalMonomial_coefficient_representative d t L g
  refine ⟨∑ α : normalExponentIndex t L, MvPolynomial.monomial α.val (a α),?_⟩
  simpa only [map_sum,normalPolynomialEval_monomial] using ha

theorem actualGraphScalingGerm_odd_power_iff (d t k : ℕ)
    (g : HolGerm (ComplexModel (d+t))) :
    actualGraphScalingGerm d t g ∈ normalIdeal d (1+t)^(2*k+1) ↔ g ∈ normalIdeal d t^(k+1) := by
  constructor
  · intro hg
    obtain ⟨P,hP⟩ := exists_actual_original_polynomial_jet d t (k+1) g
    have hs := actualGraphScaling_mem_double_normal_power d t (k+1) _ hP
    rw [map_sub] at hs
    have hs' := Ideal.pow_le_pow_right (by omega : 2*k+1 ≤ 2*(k+1)) hs
    have he := (normalIdeal d (1+t)^(2*k+1)).sub_mem hg hs'
    rw [sub_sub_cancel,actualGraphScalingGerm_polynomialEval] at he
    have hp := (actualGraphPolynomialSubstitution_odd_power_iff d t k P).mp
      ((normalPolynomialEval_mem_power_iff d (1+t) (2*k+1) _).mp he)
    have hv := (normalPolynomialEval_mem_power_iff d t (k+1) P).mpr hp
    have hr := (normalIdeal d t^(k+1)).add_mem hP hv
    simpa only [sub_add_cancel] using hr
  · intro hg
    exact Ideal.pow_le_pow_right (by omega : 2*k+1 ≤ 2*(k+1))
      (actualGraphScaling_mem_double_normal_power d t (k+1) g hg)

theorem actualGraphCentralHomogeneousPart_homogeneous (d t k : ℕ)
    (H : MvPolynomial (Fin (1+t)) (HolGerm (ComplexModel d))) :
    (actualGraphCentralHomogeneousPart d t k H).IsHomogeneous k := by
  exact MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous k (actualGraphCentralPolynomial d t H)

theorem graphCentralPullback_actual_base (d t : ℕ) (a : HolGerm (ComplexModel d)) :
    graphCentralPullback d t (tangentPullback d (1+t) a) = tangentPullback d t a := by
  induction a using HolGerm.induction_on with
  | h f hf =>
    unfold graphCentralPullback tangentPullback
    rw [compAlgHom_mk,compAlgHom_mk,compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    apply Eventually.of_forall
    intro z
    apply congrArg f
    ext i
    exact graphCentralInclusion_tangent d t z i

theorem graphCentralPullback_actual_parameter (d t : ℕ) :
    graphCentralPullback d t (normalCoordinate d (1+t) (actualGraphParameterIndex t)) = 0 := by
  rw [← HironakaRelativeNormalGraphAnalyticFiniteRelations.graphParameterGerm_normalCoordinate]
  unfold graphCentralPullback graphParameterGerm
  rw [compAlgHom_mk,← HolGerm.mk_zero,HolGerm.mk_eq_mk_iff]
  exact Eventually.of_forall fun z => graphCentralInclusion_parameter d t z

theorem graphCentralPullback_actual_fiber (d t : ℕ) (i : Fin t) :
    graphCentralPullback d t (normalCoordinate d (1+t) (actualGraphFiberIndex t i)) = normalCoordinate d t i := by
  unfold graphCentralPullback normalCoordinate coordinateGerm
  rw [compAlgHom_mk,HolGerm.mk_eq_mk_iff]
  apply Eventually.of_forall
  intro z
  have he : (actualGraphFiberIndex t i).natAdd d =
      (⟨d+1+i.val,by dsimp [graphDimension]; omega⟩ : Fin (graphDimension d t)) := by
    apply Fin.ext
    simp only [actualGraphFiberIndex,Fin.val_natAdd]
    omega
  change graphCentralInclusion d t z ((actualGraphFiberIndex t i).natAdd d) = z (i.natAdd d)
  rw [he]
  exact graphCentralInclusion_fiber d t z i

theorem graphCentralPullback_actual_polynomial_variable (d t : ℕ) (j : Fin (1+t)) :
    graphCentralPullback d t (normalPolynomialEval d (1+t) (MvPolynomial.X j)) =
      normalPolynomialEval d t (actualGraphCentralPolynomial d t (MvPolynomial.X j)) := by
  let := tangentAlgebra d t
  let := tangentAlgebra d (1+t)
  by_cases hj : j.val = 0
  · have he : j = actualGraphParameterIndex t := Fin.ext hj
    subst j
    rw [actualGraphCentralPolynomial_parameter,map_zero]
    rw [normalPolynomialEval,MvPolynomial.aeval_X]
    exact graphCentralPullback_actual_parameter d t
  · let i : Fin t := ⟨j.val-1,by omega⟩
    have he : j = actualGraphFiberIndex t i := Fin.ext (by dsimp [i,actualGraphFiberIndex]; omega)
    rw [he,actualGraphCentralPolynomial_fiber]
    rw [normalPolynomialEval,MvPolynomial.aeval_X,normalPolynomialEval,MvPolynomial.aeval_X]
    exact graphCentralPullback_actual_fiber d t i

theorem graphCentralPullback_actual_polynomialEval (d t : ℕ)
    (H : MvPolynomial (Fin (1+t)) (HolGerm (ComplexModel d))) :
    graphCentralPullback d t (normalPolynomialEval d (1+t) H) =
      normalPolynomialEval d t (actualGraphCentralPolynomial d t H) := by
  let := tangentAlgebra d t
  let := tangentAlgebra d (1+t)
  induction H using MvPolynomial.induction_on with
  | C a =>
    rw [actualGraphCentralPolynomial,MvPolynomial.aeval_C]
    change graphCentralPullback d t (normalPolynomialEval d (1+t) (MvPolynomial.C a)) =
      normalPolynomialEval d t (MvPolynomial.C a)
    rw [normalPolynomialEval,MvPolynomial.aeval_C,normalPolynomialEval,MvPolynomial.aeval_C]
    change graphCentralPullback d t (tangentPullback d (1+t) a) = tangentPullback d t a
    exact graphCentralPullback_actual_base d t a
  | add P Q hP hQ => rw [map_add,map_add,map_add,map_add,hP,hQ]
  | mul_X P j hP =>
    rw [map_mul,map_mul,map_mul,map_mul,hP,graphCentralPullback_actual_polynomial_variable]

theorem graphCentralPullback_actual_map_normalIdeal_le (d t : ℕ) :
    Ideal.map (graphCentralPullback d t).toRingHom (normalIdeal d (1+t)) ≤ normalIdeal d t := by
  rw [normalIdeal,Ideal.map_span]
  apply Ideal.span_le.mpr
  rintro g ⟨a,⟨j,rfl⟩,rfl⟩
  by_cases hj : j.val = 0
  · have he : j = actualGraphParameterIndex t := Fin.ext hj
    subst j
    change graphCentralPullback d t (normalCoordinate d (1+t) (actualGraphParameterIndex t)) ∈ normalIdeal d t
    rw [graphCentralPullback_actual_parameter]
    exact Ideal.zero_mem _
  · let i : Fin t := ⟨j.val-1,by omega⟩
    have he : j = actualGraphFiberIndex t i := Fin.ext (by dsimp [i,actualGraphFiberIndex]; omega)
    rw [he]
    change graphCentralPullback d t (normalCoordinate d (1+t) (actualGraphFiberIndex t i)) ∈ normalIdeal d t
    rw [graphCentralPullback_actual_fiber]
    exact Ideal.subset_span ⟨i,rfl⟩

theorem graphCentralPullback_actual_mem_normal_power (d t L : ℕ)
    (h : HolGerm (ComplexModel (graphDimension d t))) (hh : h ∈ normalIdeal d (1+t)^L) :
    graphCentralPullback d t h ∈ normalIdeal d t^L := by
  have hm := Ideal.mem_map_of_mem (graphCentralPullback d t).toRingHom hh
  rw [Ideal.map_pow] at hm
  exact (pow_le_pow_left' (graphCentralPullback_actual_map_normalIdeal_le d t) L) hm

theorem exists_original_coherent_all_graph_central_initial_symbols (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    ∃ N : ℕ, ∃ U : Set (ComplexModel (deformationDimension d t)), IsOpen U ∧ 0 ∈ U ∧
      (∀ q : ℕ, actualGraphColonIdeal d t I (N+q) = actualGraphColonIdeal d t I N) ∧
      (∀ y ∈ U, ∀ q : ℕ, ∀ f,
        (originalDeformationColonIdeal d t I (N+q)).mem y f ↔
          (originalDeformationColonIdeal d t I N).mem y f) ∧
      ∀ h : HolGerm (ComplexModel (graphDimension d t)), (∃ q : ℕ, h ∈ actualGraphColonIdeal d t I q) →
        ∀ k : ℕ, ∃ H : MvPolynomial (Fin (1+t)) (HolGerm (ComplexModel d)),
          ∃ F : HolGerm (ComplexModel (d+t)),
            (h-normalPolynomialEval d (1+t) H ∈ normalIdeal d (1+t)^(N+k+1)) ∧
            F ∈ originalCoherentOriginIdeal I ∧
            ∃ hFk : F ∈ normalIdeal d t^k,
              originalNormalInitialSymbol d t k F hFk = actualGraphCentralHomogeneousPart d t k H ∧
              actualGraphCentralHomogeneousPart d t k H ∈ originalNormalInitialIdeal d t (originalCoherentOriginIdeal I) := by
  obtain ⟨N,U,hU,h0,hgraph,hchain,hr⟩ := exists_original_coherent_uniform_graph_weight_reconstructions d t I hI
  refine ⟨N,U,hU,h0,hgraph,hchain,?_⟩
  intro h hh k
  obtain ⟨H,F,hH,hFI,hscaled⟩ := hr h hh k
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

end
end Hironaka.HironakaRelativeNormalGraphCentralInitialSymbols
