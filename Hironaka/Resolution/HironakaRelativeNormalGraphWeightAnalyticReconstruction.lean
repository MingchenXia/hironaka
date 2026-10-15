/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalGraphAnalyticFiniteRelations
import Hironaka.Resolution.HironakaRelativeNormalGraphWeightCancellation

/-! Actual whole original-ideal analytic reconstruction of finite central-weight
jets. Three complete mathematical proofs preceded Lean. OWN OFFLIB only;
whole central initial ideal/nearby cone/ALLq analytic free remain OPEN. -/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaRelativeNormalGraphWeightAnalyticReconstruction
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm HironakaRelativeNormalIdeal
  HironakaRelativeNormalDeformationInitialRelations HironakaRelativeNormalAnalyticGraphQuotient
  HironakaRelativeNormalDeformationSaturation HironakaRelativeNormalGraphAnalyticFiniteRelations
  HironakaRelativeNormalMonomialBasis HironakaRelativeNormalPolynomialJetAlgebra
  HironakaRelativeNormalGraphWeightJets HironakaRelativeNormalGraphWeightComponents
  HironakaRelativeNormalGraphWeightReconstruction HironakaRelativeNormalGraphWeightCancellation

theorem actualGraph_reconstructed_entire_germ_mem_original_ideal (d t : ℕ) {ι : Type*}
    (S : Finset ι) (B : ι → MvPolynomial (Fin t) (HolGerm (ComplexModel d)))
    (g : ι → HolGerm (ComplexModel (d+t)))
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hg : ∀ i ∈ S, g i ∈ originalCoherentOriginIdeal I) :
    (∑ i ∈ S, normalPolynomialEval d t (B i)*g i) ∈ originalCoherentOriginIdeal I := by
  apply (originalCoherentOriginIdeal I).sum_mem
  intro i hi
  exact (originalCoherentOriginIdeal I).mul_mem_left _ (hg i hi)

theorem actualGraphScalingGerm_reconstructed_entire_sum (d t : ℕ) {ι : Type*}
    (S : Finset ι) (B : ι → MvPolynomial (Fin t) (HolGerm (ComplexModel d)))
    (g : ι → HolGerm (ComplexModel (d+t))) :
    actualGraphScalingGerm d t (∑ i ∈ S, normalPolynomialEval d t (B i)*g i) =
      ∑ i ∈ S, actualGraphScalingGerm d t (normalPolynomialEval d t (B i))*actualGraphScalingGerm d t (g i) := by
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => map_mul _ _ _)

theorem exists_actual_graph_weight_entire_original_reconstruction (d t N k m : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t)))
    (g : Fin m → HolGerm (ComplexModel (d+t)))
    (a : Fin m → HolGerm (ComplexModel (graphDimension d t)))
    (h : HolGerm (ComplexModel (graphDimension d t)))
    (hg : ∀ i, g i ∈ originalCoherentOriginIdeal I)
    (heq : graphParameterGerm d t^N*h = ∑ i : Fin m, a i*actualGraphScalingGerm d t (g i)) :
    ∃ H : MvPolynomial (Fin (1+t)) (HolGerm (ComplexModel d)),
      ∃ F : HolGerm (ComplexModel (d+t)),
        (h-normalPolynomialEval d (1+t) H ∈ normalIdeal d (1+t)^(N+k+1)) ∧
        F ∈ originalCoherentOriginIdeal I ∧
        actualGraphScalingGerm d t F - normalPolynomialEval d (1+t)
          (MvPolynomial.X (actualGraphParameterIndex t)^k*actualGraphWeightComponent d t (-(k : ℤ)) H) ∈
          normalIdeal d (1+t)^(2*k+1) := by
  classical
  let := tangentAlgebra d t
  let := tangentAlgebra d (1+t)
  let L := N+k+1
  obtain ⟨H,A,P,hH,hA,hP,hR⟩ := exists_actual_entire_finite_graph_jet_relation d t N L m g a h heq
  let B : Fin m → MvPolynomial (Fin t) (HolGerm (ComplexModel d)) :=
    fun i => actualGraphReconstructedCoefficient d t N k (A i)
  let F := ∑ i : Fin m, normalPolynomialEval d t (B i)*g i
  have hF : F ∈ originalCoherentOriginIdeal I :=
    actualGraph_reconstructed_entire_germ_mem_original_ideal d t Finset.univ B g I (fun i _ => hg i)
  refine ⟨H,F,hH,hF,?_⟩
  have hc := actualGraph_reconstructed_finite_jet_congruence d t N k L Finset.univ H A P (by dsimp [L]; omega) hR
  have hdegree : L+k-N = 2*k+1 := by dsimp [L]; omega
  rw [hdegree] at hc
  have hce := (normalPolynomialEval_mem_power_iff d (1+t) (2*k+1) _).mpr hc
  rw [map_sub] at hce
  have hs (i : Fin m) : actualGraphScalingGerm d t (g i)-
      actualGraphScalingGerm d t (normalPolynomialEval d t (P i)) ∈ normalIdeal d (1+t)^(2*k+1) := by
    have hp := actualGraphScaling_mem_double_normal_power d t L _ (hP i)
    rw [map_sub] at hp
    exact Ideal.pow_le_pow_right (by dsimp [L]; omega : 2*k+1 ≤ 2*L) hp
  have hprod (i : Fin m) : actualGraphScalingGerm d t (normalPolynomialEval d t (B i))*actualGraphScalingGerm d t (g i) -
      normalPolynomialEval d (1+t) (actualGraphPolynomialSubstitution d t (B i*P i)) ∈ normalIdeal d (1+t)^(2*k+1) := by
    have hp := (normalIdeal d (1+t)^(2*k+1)).mul_mem_left
      (actualGraphScalingGerm d t (normalPolynomialEval d t (B i))) (hs i)
    rw [← actualGraphScalingGerm_polynomialEval,map_mul,map_mul] 
    convert hp using 1
    ring
  have hsum := (normalIdeal d (1+t)^(2*k+1)).sum_mem (fun i (_hi : i ∈ Finset.univ) => hprod i)
  rw [Finset.sum_sub_distrib,← actualGraphScalingGerm_reconstructed_entire_sum,
    ← map_sum,← map_sum] at hsum
  have hr := (normalIdeal d (1+t)^(2*k+1)).sub_mem hsum hce
  change actualGraphScalingGerm d t F - _ ∈ _
  convert hr using 1
  ring

theorem exists_original_coherent_uniform_graph_weight_reconstructions (d t : ℕ)
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
            actualGraphScalingGerm d t F - normalPolynomialEval d (1+t)
              (MvPolynomial.X (actualGraphParameterIndex t)^k*actualGraphWeightComponent d t (-(k : ℤ)) H) ∈
                normalIdeal d (1+t)^(2*k+1) := by
  obtain ⟨N,U,hU,h0,hgraph,hchain,hr⟩ := exists_original_coherent_uniform_graph_finite_relations d t I hI
  refine ⟨N,U,hU,h0,hgraph,hchain,?_⟩
  intro h hh k
  obtain ⟨m,g,a,hg,heq,hjets⟩ := hr h hh
  exact exists_actual_graph_weight_entire_original_reconstruction d t N k m I g a h hg heq

end
end Hironaka.HironakaRelativeNormalGraphWeightAnalyticReconstruction
