/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalGraphWeightReconstruction

/-! Actual original whole graph saturation internally selects true finite
analytic relations and their multiplicative polynomial jets. Four prior full
mathematical proofs; OWN OFFLIB only. Reverse central/nearby cone/ALLq OPEN. -/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaRelativeNormalGraphAnalyticFiniteRelations
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis HironakaRelativeNormalIdealMatrices
  HironakaRelativeNormalDeformationInitialRelations HironakaRelativeNormalAnalyticGraphQuotient
  HironakaRelativeNormalDeformationSaturation HironakaRelativeNormalCoherentSaturation
  HironakaRelativeNormalPolynomialJetAlgebra HironakaRelativeNormalGraphWeightJets
  HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetMonomialSpan

theorem actualGraphScalingGerm_graphTrace_tangentPullback (d t : ℕ)
    (g : HolGerm (ComplexModel (d+t))) :
    actualGraphScalingGerm d t g = graphTrace d t (tangentPullback (d+t) (1+t) g) := by
  induction g using HolGerm.induction_on with
  | h f hf =>
    unfold actualGraphScalingGerm graphTrace tangentPullback
    rw [compAlgHom_mk,compAlgHom_mk,compAlgHom_mk]
    rfl

theorem actualGraphScaledIdeal_scaling_map (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) :
    actualGraphScaledIdeal d t I =
      Ideal.map (actualGraphScalingGerm d t).toRingHom (originalCoherentOriginIdeal I) := by
  have he : ((graphTrace d t).comp (tangentPullback (d+t) (1+t))).toRingHom =
      (actualGraphScalingGerm d t).toRingHom :=
    RingHom.ext (fun g => (actualGraphScalingGerm_graphTrace_tangentPullback d t g).symm)
  rw [actualGraphScaledIdeal,he]

theorem graphParameterGerm_normalCoordinate (d t : ℕ) :
    graphParameterGerm d t = normalCoordinate d (1+t) (actualGraphParameterIndex t) := by
  unfold graphParameterGerm normalCoordinate coordinateGerm
  apply HolGerm.mk_eq_mk_iff.mpr
  apply Eventually.of_forall
  intro z
  change z (⟨d,by dsimp [graphDimension]; omega⟩ : Fin (graphDimension d t)) = z ((actualGraphParameterIndex t).natAdd d)
  apply congrArg (fun j : Fin (graphDimension d t) => z j)
  exact Fin.ext (by simp only [actualGraphParameterIndex,Fin.val_natAdd,Nat.add_zero])

private theorem actual_colon_power_membership {R : Type*} [CommRing R]
    (I : Ideal R) (u : R) (N : ℕ) (g : R) :
    g ∈ actualOriginColonChain I u N ↔ g*u^N ∈ I := by
  induction N generalizing g with
  | zero => simp only [actualOriginColonChain,pow_zero,mul_one]
  | succ N ih =>
    rw [actualOriginColonChain,Submodule.mem_colon_singleton]
    change g*u ∈ actualOriginColonChain I u N ↔ g*u^(N+1) ∈ I
    rw [ih,pow_succ,mul_assoc,mul_comm u (u^N)]

theorem exists_actual_graph_colon_finite_original_germ_relation (d t N : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t)))
    (h : HolGerm (ComplexModel (graphDimension d t))) (hh : h ∈ actualGraphColonIdeal d t I N) :
    ∃ m : ℕ, ∃ g : Fin m → HolGerm (ComplexModel (d+t)),
      ∃ a : Fin m → HolGerm (ComplexModel (graphDimension d t)),
      (∀ i, g i ∈ originalCoherentOriginIdeal I) ∧
      graphParameterGerm d t^N * h = ∑ i : Fin m, a i * actualGraphScalingGerm d t (g i) := by
  classical
  change h ∈ actualOriginColonChain (actualGraphScaledIdeal d t I) (graphParameterGerm d t) N at hh
  rw [actual_colon_power_membership] at hh
  have hm : graphParameterGerm d t^N * h ∈
      Ideal.map (actualGraphScalingGerm d t).toRingHom (originalCoherentOriginIdeal I) := by
    rw [← actualGraphScaledIdeal_scaling_map]
    simpa only [mul_comm] using hh
  change graphParameterGerm d t^N * h ∈ Submodule.span (HolGerm (ComplexModel (graphDimension d t)))
    ((actualGraphScalingGerm d t).toRingHom '' (originalCoherentOriginIdeal I : Set (HolGerm (ComplexModel (d+t))))) at hm
  obtain ⟨m,a,v,hv⟩ := Submodule.mem_span_set'.mp hm
  have hpre (i : Fin m) : ∃ g ∈ originalCoherentOriginIdeal I,
      actualGraphScalingGerm d t g = (v i).val := (v i).property
  choose g hgI hg using hpre
  refine ⟨m,g,a,hgI,?_⟩
  apply Eq.symm
  calc
    _ = ∑ i : Fin m, a i * (v i).val := Finset.sum_congr rfl (fun i _ => by rw [hg i])
    _ = _ := by simpa only [smul_eq_mul] using hv

private theorem exists_actual_polynomial_representative (d t L : ℕ)
    (g : HolGerm (ComplexModel (d+t))) :
    ∃ P : MvPolynomial (Fin t) (HolGerm (ComplexModel d)),
      g-normalPolynomialEval d t P ∈ normalIdeal d t^L := by
  classical
  let := tangentAlgebra d t
  let := normalExponentFintype t L
  obtain ⟨a,ha⟩ := exists_normalMonomial_coefficient_representative d t L g
  refine ⟨∑ α : normalExponentIndex t L, MvPolynomial.monomial α.val (a α),?_⟩
  simpa only [map_sum,normalPolynomialEval_monomial] using ha

theorem exists_actual_entire_finite_graph_jet_relation (d t N L m : ℕ)
    (g : Fin m → HolGerm (ComplexModel (d+t)))
    (a : Fin m → HolGerm (ComplexModel (graphDimension d t)))
    (h : HolGerm (ComplexModel (graphDimension d t)))
    (heq : graphParameterGerm d t^N * h = ∑ i : Fin m, a i * actualGraphScalingGerm d t (g i)) :
    ∃ H : MvPolynomial (Fin (1+t)) (HolGerm (ComplexModel d)),
      ∃ A : Fin m → MvPolynomial (Fin (1+t)) (HolGerm (ComplexModel d)),
      ∃ P : Fin m → MvPolynomial (Fin t) (HolGerm (ComplexModel d)),
      (h-normalPolynomialEval d (1+t) H ∈ normalIdeal d (1+t)^L) ∧
      (∀ i, a i-normalPolynomialEval d (1+t) (A i) ∈ normalIdeal d (1+t)^L) ∧
      (∀ i, g i-normalPolynomialEval d t (P i) ∈ normalIdeal d t^L) ∧
      (MvPolynomial.X (actualGraphParameterIndex t)^N * H -
        ∑ i : Fin m, A i * actualGraphPolynomialSubstitution d t (P i)) ∈
        actualPolynomialNormalIdeal d (1+t)^L := by
  classical
  let := tangentAlgebra d t
  let := tangentAlgebra d (1+t)
  obtain ⟨H,hH⟩ := exists_actual_polynomial_representative d (1+t) L h
  choose A hA using fun i : Fin m => exists_actual_polynomial_representative d (1+t) L (a i)
  choose P hP using fun i : Fin m => exists_actual_polynomial_representative d t L (g i)
  refine ⟨H,A,P,hH,hA,hP,?_⟩
  have hs (i : Fin m) : actualGraphScalingGerm d t (g i)-
      actualGraphScalingGerm d t (normalPolynomialEval d t (P i)) ∈ normalIdeal d (1+t)^L := by
    have hr := actualGraphScaling_mem_double_normal_power d t L (g i-normalPolynomialEval d t (P i)) (hP i)
    rw [map_sub] at hr
    exact Ideal.pow_le_pow_right (by omega : L ≤ 2*L) hr
  have hprod (i : Fin m) : a i * actualGraphScalingGerm d t (g i) -
      normalPolynomialEval d (1+t) (A i) * actualGraphScalingGerm d t (normalPolynomialEval d t (P i)) ∈
        normalIdeal d (1+t)^L := by
    have hr := (normalIdeal d (1+t)^L).add_mem
      ((normalIdeal d (1+t)^L).mul_mem_right (actualGraphScalingGerm d t (g i)) (hA i))
      ((normalIdeal d (1+t)^L).mul_mem_left (normalPolynomialEval d (1+t) (A i)) (hs i))
    convert hr using 1
    ring
  have hsum := (normalIdeal d (1+t)^L).sum_mem (fun i (_hi : i ∈ Finset.univ) => hprod i)
  rw [Finset.sum_sub_distrib,← heq] at hsum
  have hr := (normalIdeal d (1+t)^L).sub_mem hsum
    ((normalIdeal d (1+t)^L).mul_mem_left (graphParameterGerm d t^N) hH)
  have hx : normalPolynomialEval d (1+t) (MvPolynomial.X (actualGraphParameterIndex t)) = graphParameterGerm d t := by
    rw [normalPolynomialEval,MvPolynomial.aeval_X]
    exact (graphParameterGerm_normalCoordinate d t).symm
  apply (normalPolynomialEval_mem_power_iff d (1+t) L _).mp
  rw [map_sub,map_mul,map_pow,hx,map_sum]
  simp_rw [map_mul,← actualGraphScalingGerm_polynomialEval]
  convert hr using 1
  ring

theorem exists_original_coherent_uniform_graph_finite_relations (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    ∃ N : ℕ, ∃ U : Set (ComplexModel (deformationDimension d t)), IsOpen U ∧ 0 ∈ U ∧
      (∀ q : ℕ, actualGraphColonIdeal d t I (N+q) = actualGraphColonIdeal d t I N) ∧
      (∀ y ∈ U, ∀ q : ℕ, ∀ f,
        (originalDeformationColonIdeal d t I (N+q)).mem y f ↔
          (originalDeformationColonIdeal d t I N).mem y f) ∧
      ∀ h : HolGerm (ComplexModel (graphDimension d t)),
        (∃ q : ℕ, h ∈ actualGraphColonIdeal d t I q) →
        ∃ m : ℕ, ∃ g : Fin m → HolGerm (ComplexModel (d+t)),
          ∃ a : Fin m → HolGerm (ComplexModel (graphDimension d t)),
          (∀ i, g i ∈ originalCoherentOriginIdeal I) ∧
          (graphParameterGerm d t^N * h = ∑ i : Fin m, a i * actualGraphScalingGerm d t (g i)) ∧
          ∀ L : ℕ, ∃ H : MvPolynomial (Fin (1+t)) (HolGerm (ComplexModel d)),
            ∃ A : Fin m → MvPolynomial (Fin (1+t)) (HolGerm (ComplexModel d)),
              ∃ P : Fin m → MvPolynomial (Fin t) (HolGerm (ComplexModel d)),
              (h-normalPolynomialEval d (1+t) H ∈ normalIdeal d (1+t)^L) ∧
              (∀ i, a i-normalPolynomialEval d (1+t) (A i) ∈ normalIdeal d (1+t)^L) ∧
              (∀ i, g i-normalPolynomialEval d t (P i) ∈ normalIdeal d t^L) ∧
              (MvPolynomial.X (actualGraphParameterIndex t)^N * H -
                ∑ i : Fin m, A i * actualGraphPolynomialSubstitution d t (P i)) ∈
                  actualPolynomialNormalIdeal d (1+t)^L := by
  obtain ⟨N,U,hU,h0,hcentral,hgraph,hsat,hchain,hpow,hwhole⟩ := exists_original_graph_saturated_model d t I hI
  refine ⟨N,U,hU,h0,hgraph,hchain,?_⟩
  intro h hh
  obtain ⟨m,g,a,hg,heq⟩ := exists_actual_graph_colon_finite_original_germ_relation d t N I h ((hsat h).mp hh)
  exact ⟨m,g,a,hg,heq,fun L => exists_actual_entire_finite_graph_jet_relation d t N L m g a h heq⟩

end
end Hironaka.HironakaRelativeNormalGraphAnalyticFiniteRelations
