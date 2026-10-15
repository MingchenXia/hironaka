/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalGraphWeightReconstruction

/-! Genuine weight extraction and literal parameter-power cancellation in
actual graph polynomial jets. Three full mathematical proofs preceded Lean.
OWN OFFLIB only; reverse whole analytic ideal/nearby cone/ALLq remain OPEN. -/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaRelativeNormalGraphWeightCancellation
noncomputable section
open HolGerm HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalPolynomialJetAlgebra HironakaRelativeNormalGraphWeightJets
  HironakaRelativeNormalGraphWeightComponents HironakaRelativeNormalGraphWeightReconstruction

theorem actualGraphWeightComponent_mul_homogeneous (d t : ℕ) (w m : ℤ)
    (A Q : MvPolynomial (Fin (1+t)) (HolGerm (ComplexModel d)))
    (hQ : MvPolynomial.IsWeightedHomogeneous (actualGraphIntegerWeight t) Q m) :
    actualGraphWeightComponent d t w (A*Q) =
      actualGraphWeightComponent d t (w-m) A * Q := by
  classical
  apply MvPolynomial.ext
  intro δ
  rw [actualGraphWeightComponent_coeff,MvPolynomial.coeff_mul,MvPolynomial.coeff_mul]
  split_ifs with hδ
  · apply Finset.sum_congr rfl
    intro a ha
    rw [actualGraphWeightComponent_coeff]
    by_cases hs : MvPolynomial.coeff a.2 Q = 0
    · simp only [hs,mul_zero]
    · have hw := hQ hs
      have he := congrArg (Finsupp.weight (actualGraphIntegerWeight t)) (Finset.mem_antidiagonal.mp ha)
      rw [map_add,hw,hδ] at he
      have hwδ : Finsupp.weight (actualGraphIntegerWeight t) a.1 = w-m := by omega
      rw [if_pos hwδ]
  · apply Eq.symm
    apply Finset.sum_eq_zero
    intro a ha
    rw [actualGraphWeightComponent_coeff]
    by_cases hs : MvPolynomial.coeff a.2 Q = 0
    · simp only [hs,mul_zero]
    · have hw := hQ hs
      have hwδ : Finsupp.weight (actualGraphIntegerWeight t) a.1 ≠ w-m := by
        intro he
        apply hδ
        rw [← Finset.mem_antidiagonal.mp ha,map_add,hw,he]
        omega
      rw [if_neg hwδ,zero_mul]

theorem actualGraphWeightComponent_parameter_power (d t N k : ℕ)
    (H : MvPolynomial (Fin (1+t)) (HolGerm (ComplexModel d))) :
    actualGraphWeightComponent d t ((N : ℤ)-k)
      (MvPolynomial.X (actualGraphParameterIndex t)^N*H) =
      MvPolynomial.X (actualGraphParameterIndex t)^N * actualGraphWeightComponent d t (-(k : ℤ)) H := by
  have hu := (MvPolynomial.isWeightedHomogeneous_X (R := HolGerm (ComplexModel d))
    (actualGraphIntegerWeight t) (actualGraphParameterIndex t)).pow N
  have hp : MvPolynomial.IsWeightedHomogeneous (actualGraphIntegerWeight t)
      (MvPolynomial.X (actualGraphParameterIndex t)^N : MvPolynomial (Fin (1+t)) (HolGerm (ComplexModel d))) (N : ℤ) := by
    simpa only [actualGraphIntegerWeight_parameter,nsmul_eq_mul,mul_one] using hu
  rw [mul_comm _ H,actualGraphWeightComponent_mul_homogeneous d t _ _ H _ hp]
  have hw : ((N : ℤ)-k)-N = -(k : ℤ) := by omega
  rw [hw,mul_comm]

theorem actualGraphParameterExponent_degree (t N : ℕ) (α : Fin (1+t) →₀ ℕ) :
    normalExponentDegree (Finsupp.single (actualGraphParameterIndex t) N + α) =
      N+normalExponentDegree α := by
  classical
  simp [normalExponentDegree,Finsupp.add_apply,Finset.sum_add_distrib]

theorem actualGraphPolynomial_parameter_power_cancel (d t N M : ℕ)
    (Q : MvPolynomial (Fin (1+t)) (HolGerm (ComplexModel d))) (hNM : N ≤ M)
    (hQ : MvPolynomial.X (actualGraphParameterIndex t)^N*Q ∈ actualPolynomialNormalIdeal d (1+t)^M) :
    Q ∈ actualPolynomialNormalIdeal d (1+t)^(M-N) := by
  rw [actualPolynomialNormalIdeal_power_iff_coefficients] at hQ ⊢
  intro α hα
  have hdeg : normalExponentDegree (Finsupp.single (actualGraphParameterIndex t) N+α) < M := by
    rw [actualGraphParameterExponent_degree]
    omega
  have hc := hQ (Finsupp.single (actualGraphParameterIndex t) N+α) hdeg
  rw [MvPolynomial.X_pow_eq_monomial,MvPolynomial.coeff_monomial_mul,one_mul] at hc
  exact hc

theorem actualGraphPolynomial_parameter_power_raise (d t L k : ℕ)
    (Q : MvPolynomial (Fin (1+t)) (HolGerm (ComplexModel d)))
    (hQ : Q ∈ actualPolynomialNormalIdeal d (1+t)^L) :
    MvPolynomial.X (actualGraphParameterIndex t)^k*Q ∈ actualPolynomialNormalIdeal d (1+t)^(L+k) := by
  have hu : (MvPolynomial.X (actualGraphParameterIndex t) : MvPolynomial (Fin (1+t)) (HolGerm (ComplexModel d))) ∈
      actualPolynomialNormalIdeal d (1+t) := Ideal.subset_span ⟨actualGraphParameterIndex t,rfl⟩
  have hp := Ideal.mul_mem_mul (Ideal.pow_mem_pow hu k) hQ
  simpa only [← pow_add,Nat.add_comm k L] using hp

theorem actualGraph_reconstructed_finite_jet_congruence (d t N k L : ℕ) {ι : Type*}
    (S : Finset ι) (H : MvPolynomial (Fin (1+t)) (HolGerm (ComplexModel d)))
    (A : ι → MvPolynomial (Fin (1+t)) (HolGerm (ComplexModel d)))
    (P : ι → MvPolynomial (Fin t) (HolGerm (ComplexModel d))) (hNL : N ≤ L+k)
    (hR : MvPolynomial.X (actualGraphParameterIndex t)^N*H -
      ∑ i ∈ S, A i*actualGraphPolynomialSubstitution d t (P i) ∈ actualPolynomialNormalIdeal d (1+t)^L) :
    MvPolynomial.X (actualGraphParameterIndex t)^k * actualGraphWeightComponent d t (-(k : ℤ)) H -
      actualGraphPolynomialSubstitution d t (∑ i ∈ S, actualGraphReconstructedCoefficient d t N k (A i)*P i) ∈
        actualPolynomialNormalIdeal d (1+t)^(L+k-N) := by
  have hc := actualGraphWeightComponent_mem_power d t L ((N : ℤ)-k) _ hR
  have hm := actualGraphPolynomial_parameter_power_raise d t L k _ hc
  rw [map_sub,mul_sub,actualGraphWeightComponent_parameter_power,
    actualGraph_finite_relation_reconstruction] at hm
  apply actualGraphPolynomial_parameter_power_cancel d t N (L+k) _ hNL
  convert hm using 1
  ring

end
end Hironaka.HironakaRelativeNormalGraphWeightCancellation
