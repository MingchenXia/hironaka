/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalGraphWeightJets
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-! Actual finite integer weight extraction of whole graph-scaled jets.
Four full mathematical proofs preceded Lean. OWN OFFLIB only.
Reverse central initial ideal/entire Krull passage/nearby cone and ALLq OPEN. -/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaRelativeNormalGraphWeightComponents
noncomputable section
open HolGerm HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalPolynomialJetAlgebra HironakaRelativeNormalGraphWeightJets
  HironakaRelativeNormalAnalyticGraphQuotient

def actualGraphIntegerWeight (t : ℕ) (i : Fin (1+t)) : ℤ :=
  if i = actualGraphParameterIndex t then 1 else -1

theorem actualGraphIntegerWeight_parameter (t : ℕ) :
    actualGraphIntegerWeight t (actualGraphParameterIndex t) = 1 := by
  simp [actualGraphIntegerWeight]

theorem actualGraphIntegerWeight_fiber (t : ℕ) (i : Fin t) :
    actualGraphIntegerWeight t (actualGraphFiberIndex t i) = -1 := by
  have hne : actualGraphFiberIndex t i ≠ actualGraphParameterIndex t := by
    intro h
    have hv := congrArg Fin.val h
    simp only [actualGraphFiberIndex,actualGraphParameterIndex] at hv
    omega
  simp only [actualGraphIntegerWeight,if_neg hne]

theorem actualGraphPolynomialSubstitution_weight_zero (d t : ℕ)
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) :
    MvPolynomial.IsWeightedHomogeneous (actualGraphIntegerWeight t)
      (actualGraphPolynomialSubstitution d t P) 0 := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    rw [actualGraphPolynomialSubstitution,MvPolynomial.aeval_C]
    exact MvPolynomial.isWeightedHomogeneous_C _ a
  | add P Q hP hQ =>
    rw [map_add]
    exact hP.add hQ
  | mul_X P i hP =>
    rw [map_mul]
    have hX : MvPolynomial.IsWeightedHomogeneous (actualGraphIntegerWeight t)
        (actualGraphPolynomialSubstitution d t (MvPolynomial.X i)) 0 := by
      rw [actualGraphPolynomialSubstitution,MvPolynomial.aeval_X]
      have hu := MvPolynomial.isWeightedHomogeneous_X (R := HolGerm (ComplexModel d))
        (actualGraphIntegerWeight t) (actualGraphParameterIndex t)
      have hv := MvPolynomial.isWeightedHomogeneous_X (R := HolGerm (ComplexModel d))
        (actualGraphIntegerWeight t) (actualGraphFiberIndex t i)
      simpa only [actualGraphIntegerWeight_parameter,actualGraphIntegerWeight_fiber,add_neg_cancel] using hu.mul hv
    simpa only [add_zero] using hP.mul hX

theorem actualGraphPolynomialSubstitution_coeff_nonzero_weight (d t : ℕ)
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) (α : Fin (1+t) →₀ ℕ)
    (hα : Finsupp.weight (actualGraphIntegerWeight t) α ≠ 0) :
    MvPolynomial.coeff α (actualGraphPolynomialSubstitution d t P) = 0 :=
  (actualGraphPolynomialSubstitution_weight_zero d t P).coeff_eq_zero α hα

def actualGraphWeightComponent (d t : ℕ) (w : ℤ) :
    MvPolynomial (Fin (1+t)) (HolGerm (ComplexModel d)) →ₗ[HolGerm (ComplexModel d)]
      MvPolynomial (Fin (1+t)) (HolGerm (ComplexModel d)) :=
  MvPolynomial.weightedHomogeneousComponent (actualGraphIntegerWeight t) w

theorem actualGraphWeightComponent_coeff (d t : ℕ) (w : ℤ)
    (A : MvPolynomial (Fin (1+t)) (HolGerm (ComplexModel d))) (α : Fin (1+t) →₀ ℕ) :
    MvPolynomial.coeff α (actualGraphWeightComponent d t w A) =
      if Finsupp.weight (actualGraphIntegerWeight t) α = w then MvPolynomial.coeff α A else 0 :=
  MvPolynomial.coeff_weightedHomogeneousComponent w A α

theorem actualGraphWeightComponent_mul_substitution (d t : ℕ) (w : ℤ)
    (A : MvPolynomial (Fin (1+t)) (HolGerm (ComplexModel d)))
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) :
    actualGraphWeightComponent d t w (A * actualGraphPolynomialSubstitution d t P) =
      actualGraphWeightComponent d t w A * actualGraphPolynomialSubstitution d t P := by
  classical
  apply MvPolynomial.ext
  intro δ
  rw [actualGraphWeightComponent_coeff,MvPolynomial.coeff_mul,MvPolynomial.coeff_mul]
  split_ifs with hδ
  · apply Finset.sum_congr rfl
    intro a ha
    rw [actualGraphWeightComponent_coeff]
    by_cases hs : MvPolynomial.coeff a.2 (actualGraphPolynomialSubstitution d t P) = 0
    · simp only [hs,mul_zero]
    · have hw := actualGraphPolynomialSubstitution_weight_zero d t P hs
      have hadd : a.1+a.2 = δ := Finset.mem_antidiagonal.mp ha
      have hwδ : Finsupp.weight (actualGraphIntegerWeight t) a.1 = w := by
        have he := congrArg (Finsupp.weight (actualGraphIntegerWeight t)) hadd
        rw [map_add,hw,add_zero,hδ] at he
        exact he
      rw [if_pos hwδ]
  · apply Eq.symm
    apply Finset.sum_eq_zero
    intro a ha
    rw [actualGraphWeightComponent_coeff]
    by_cases hs : MvPolynomial.coeff a.2 (actualGraphPolynomialSubstitution d t P) = 0
    · simp only [hs,mul_zero]
    · have hw := actualGraphPolynomialSubstitution_weight_zero d t P hs
      have hadd : a.1+a.2 = δ := Finset.mem_antidiagonal.mp ha
      have hwδ : Finsupp.weight (actualGraphIntegerWeight t) a.1 ≠ w := by
        intro he
        apply hδ
        rw [← hadd,map_add,hw,add_zero,he]
      rw [if_neg hwδ,zero_mul]

theorem actualGraphWeightComponent_sum_products (d t : ℕ) (w : ℤ) {ι : Type*}
    (S : Finset ι) (A : ι → MvPolynomial (Fin (1+t)) (HolGerm (ComplexModel d)))
    (P : ι → MvPolynomial (Fin t) (HolGerm (ComplexModel d))) :
    actualGraphWeightComponent d t w (∑ i ∈ S, A i * actualGraphPolynomialSubstitution d t (P i)) =
      ∑ i ∈ S, actualGraphWeightComponent d t w (A i) * actualGraphPolynomialSubstitution d t (P i) := by
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => actualGraphWeightComponent_mul_substitution d t w (A i) (P i))

theorem actualGraphWeightComponent_mem_power (d t L : ℕ) (w : ℤ)
    (P : MvPolynomial (Fin (1+t)) (HolGerm (ComplexModel d)))
    (hP : P ∈ actualPolynomialNormalIdeal d (1+t) ^ L) :
    actualGraphWeightComponent d t w P ∈ actualPolynomialNormalIdeal d (1+t) ^ L := by
  rw [actualPolynomialNormalIdeal_power_iff_coefficients] at hP ⊢
  intro α hα
  rw [actualGraphWeightComponent_coeff,hP α hα]
  split_ifs <;> rfl

theorem actualGraphWeightComponent_preserves_power_congruence (d t L : ℕ) (w : ℤ)
    (P Q : MvPolynomial (Fin (1+t)) (HolGerm (ComplexModel d)))
    (h : P-Q ∈ actualPolynomialNormalIdeal d (1+t) ^ L) :
    actualGraphWeightComponent d t w P - actualGraphWeightComponent d t w Q ∈
      actualPolynomialNormalIdeal d (1+t) ^ L := by
  rw [← map_sub]
  exact actualGraphWeightComponent_mem_power d t L w (P-Q) h

theorem exists_actual_whole_graph_jet_weight_zero (d t L : ℕ)
    (g : HolGerm (ComplexModel (d+t))) :
    ∃ P : MvPolynomial (Fin (1+t)) (HolGerm (ComplexModel d)),
      MvPolynomial.IsWeightedHomogeneous (actualGraphIntegerWeight t) P 0 ∧
      actualGraphScalingGerm d t g - normalPolynomialEval d (1+t) P ∈ normalIdeal d (1+t) ^ L := by
  classical
  let := tangentAlgebra d (1+t)
  obtain ⟨Q,hQ,heq⟩ := exists_actual_graph_scaled_whole_polynomial_jet d t L g
  refine ⟨actualGraphPolynomialSubstitution d t Q,actualGraphPolynomialSubstitution_weight_zero d t Q,?_⟩
  have h := congrArg (actualPolynomialJetAlgebraEquiv d (1+t) L) heq
  change (actualPolynomialJetAlgebraEquiv d (1+t) L)
    ((actualPolynomialJetAlgebraEquiv d (1+t) L).symm (Ideal.Quotient.mk (normalIdeal d (1+t)^L)
      (actualGraphScalingGerm d t g))) = _ at h
  rw [AlgEquiv.apply_symm_apply,actualPolynomialJetAlgebraEquiv_mk] at h
  exact Ideal.Quotient.eq.mp h

theorem actual_whole_graph_jet_other_nonzero_component_mem (d t L : ℕ)
    (g : HolGerm (ComplexModel (d+t)))
    (Q : MvPolynomial (Fin (1+t)) (HolGerm (ComplexModel d)))
    (hQ : actualGraphScalingGerm d t g - normalPolynomialEval d (1+t) Q ∈ normalIdeal d (1+t)^L)
    (w : ℤ) (hw : w ≠ 0) :
    actualGraphWeightComponent d t w Q ∈ actualPolynomialNormalIdeal d (1+t)^L := by
  obtain ⟨P,hP,hrem⟩ := exists_actual_whole_graph_jet_weight_zero d t L g
  have hd : normalPolynomialEval d (1+t) (Q-P) ∈ normalIdeal d (1+t)^L := by
    have h := (normalIdeal d (1+t)^L).sub_mem hrem hQ
    rw [map_sub]
    convert h using 1
    ring
  have hpoly := (normalPolynomialEval_mem_power_iff d (1+t) L (Q-P)).mp hd
  have hc := actualGraphWeightComponent_preserves_power_congruence d t L w Q P hpoly
  have hz : actualGraphWeightComponent d t w P = 0 := hP.weightedHomogeneousComponent_ne w hw
  simpa only [hz,sub_zero] using hc

end
end Hironaka.HironakaRelativeNormalGraphWeightComponents
