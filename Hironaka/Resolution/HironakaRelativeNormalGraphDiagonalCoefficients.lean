/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalGraphWeightAnalyticReconstruction

/-! Actual diagonal substitution exponents and whole coefficient dictionary.
Three complete mathematical proofs preceded Lean. OWN OFFLIB only;
whole analytic central/Krull/nearby cone/ALLq OPEN. -/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaRelativeNormalGraphDiagonalCoefficients
noncomputable section
open HolGerm HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalGraphWeightJets HironakaRelativeNormalGraphWeightComponents
  HironakaRelativeNormalGraphWeightReconstruction

theorem actualGraphFiberIndex_injective (t : ℕ) : Function.Injective (actualGraphFiberIndex t) := by
  intro i j he
  have hv := congrArg Fin.val he
  apply Fin.ext
  simp only [actualGraphFiberIndex] at hv
  omega

theorem actualGraphFiberIndex_ne_parameter (t : ℕ) (i : Fin t) :
    actualGraphFiberIndex t i ≠ actualGraphParameterIndex t := by
  intro he
  have hv := congrArg Fin.val he
  simp only [actualGraphFiberIndex,actualGraphParameterIndex] at hv
  omega

def actualGraphDiagonalExponent (t : ℕ) (α : Fin t →₀ ℕ) : Fin (1+t) →₀ ℕ :=
  Finsupp.single (actualGraphParameterIndex t) (normalExponentDegree α) +
    ∑ i : Fin t, Finsupp.single (actualGraphFiberIndex t i) (α i)

theorem actualGraphDiagonalExponent_parameter (t : ℕ) (α : Fin t →₀ ℕ) :
    actualGraphDiagonalExponent t α (actualGraphParameterIndex t) = normalExponentDegree α := by
  classical
  simp [actualGraphDiagonalExponent,Finsupp.coe_finsetSum,Finset.sum_apply,
    actualGraphFiberIndex_ne_parameter]

theorem actualGraphDiagonalExponent_fiber (t : ℕ) (α : Fin t →₀ ℕ) (i : Fin t) :
    actualGraphDiagonalExponent t α (actualGraphFiberIndex t i) = α i := by
  classical
  have hne := (actualGraphFiberIndex_ne_parameter t i).symm
  have he (j : Fin t) : actualGraphFiberIndex t j = actualGraphFiberIndex t i ↔ j=i :=
    (actualGraphFiberIndex_injective t).eq_iff
  simp [actualGraphDiagonalExponent,Finsupp.coe_finsetSum,Finset.sum_apply,hne,
    Finsupp.single_apply,he]

theorem actualGraphDiagonalExponent_injective (t : ℕ) :
    Function.Injective (actualGraphDiagonalExponent t) := by
  intro α β he
  apply Finsupp.ext
  intro i
  have hi := congrArg (fun γ : Fin (1+t) →₀ ℕ => γ (actualGraphFiberIndex t i)) he
  simpa only [actualGraphDiagonalExponent_fiber] using hi

theorem actualGraphDiagonalExponent_degree (t : ℕ) (α : Fin t →₀ ℕ) :
    normalExponentDegree (actualGraphDiagonalExponent t α) = 2*normalExponentDegree α := by
  rw [normalExponentDegree,Fin.sum_univ_add]
  have hp : (0 : Fin 1).castAdd t = actualGraphParameterIndex t := Fin.ext rfl
  have hf : ∀ i : Fin t, i.natAdd 1 = actualGraphFiberIndex t i := fun i =>
    Fin.ext (by simp only [actualGraphFiberIndex,Fin.val_natAdd])
  simp only [Fin.sum_univ_one,hp,hf,actualGraphDiagonalExponent_parameter,
    actualGraphDiagonalExponent_fiber]
  change normalExponentDegree α+normalExponentDegree α = _
  omega

theorem actualGraphDiagonalExponent_weight (t : ℕ) (α : Fin t →₀ ℕ) :
    Finsupp.weight (actualGraphIntegerWeight t) (actualGraphDiagonalExponent t α) = 0 := by
  rw [actualGraphIntegerWeight_exponent,actualGraphDiagonalExponent_parameter]
  simp only [actualGraphDiagonalExponent_fiber,← Nat.cast_sum,normalExponentDegree,sub_self]

theorem actualGraphDiagonalExponent_add (t : ℕ) (α β : Fin t →₀ ℕ) :
    actualGraphDiagonalExponent t (α+β) = actualGraphDiagonalExponent t α+actualGraphDiagonalExponent t β := by
  classical
  have hd : normalExponentDegree (α+β) = normalExponentDegree α+normalExponentDegree β := by
    simp only [normalExponentDegree,Finsupp.add_apply,Finset.sum_add_distrib]
  simp only [actualGraphDiagonalExponent,hd,Finsupp.single_add,Finsupp.add_apply,Finset.sum_add_distrib]
  abel

private theorem actual_fiber_product_monomial (d t : ℕ) (α : Fin t →₀ ℕ) (S : Finset (Fin t)) :
    (∏ i ∈ S, (MvPolynomial.X (actualGraphFiberIndex t i) : MvPolynomial (Fin (1+t)) (HolGerm (ComplexModel d)))^α i) =
      MvPolynomial.monomial (∑ i ∈ S, Finsupp.single (actualGraphFiberIndex t i) (α i)) 1 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty,Finset.sum_empty]
    change (1 : MvPolynomial (Fin (1+t)) (HolGerm (ComplexModel d))) = MvPolynomial.C 1
    exact (map_one MvPolynomial.C).symm
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi,Finset.sum_insert hi,ih,MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.monomial_mul,one_mul]

theorem actualGraphPolynomialSubstitution_diagonal_monomial (d t : ℕ)
    (α : Fin t →₀ ℕ) (a : HolGerm (ComplexModel d)) :
    actualGraphPolynomialSubstitution d t (MvPolynomial.monomial α a) =
      MvPolynomial.monomial (actualGraphDiagonalExponent t α) a := by
  classical
  rw [actualGraphPolynomialSubstitution,MvPolynomial.aeval_monomial]
  change MvPolynomial.C a * α.prod (fun i k =>
    (MvPolynomial.X (actualGraphParameterIndex t)*MvPolynomial.X (actualGraphFiberIndex t i))^k) = _
  rw [α.prod_fintype _ (fun _ => pow_zero _)]
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,actual_fiber_product_monomial,
    MvPolynomial.X_pow_eq_monomial,MvPolynomial.monomial_mul,one_mul]
  change MvPolynomial.monomial 0 a * MvPolynomial.monomial (actualGraphDiagonalExponent t α) 1 = _
  rw [MvPolynomial.monomial_mul,zero_add,mul_one]

theorem actualGraphPolynomialSubstitution_diagonal_coeff (d t : ℕ)
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) (α : Fin t →₀ ℕ) :
    MvPolynomial.coeff (actualGraphDiagonalExponent t α) (actualGraphPolynomialSubstitution d t P) =
      MvPolynomial.coeff α P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial β a =>
    rw [actualGraphPolynomialSubstitution_diagonal_monomial]
    simp only [MvPolynomial.coeff_monomial,(actualGraphDiagonalExponent_injective t).eq_iff]
  | add P Q hP hQ => rw [map_add,MvPolynomial.coeff_add,MvPolynomial.coeff_add,hP,hQ]

theorem actualGraphPolynomialSubstitution_off_diagonal_coeff (d t : ℕ)
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) (δ : Fin (1+t) →₀ ℕ)
    (hδ : δ ∉ Set.range (actualGraphDiagonalExponent t)) :
    MvPolynomial.coeff δ (actualGraphPolynomialSubstitution d t P) = 0 := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial β a =>
    rw [actualGraphPolynomialSubstitution_diagonal_monomial,MvPolynomial.coeff_monomial]
    exact if_neg (fun he => hδ ⟨β,he⟩)
  | add P Q hP hQ => rw [map_add,MvPolynomial.coeff_add,hP,hQ,add_zero]

theorem actualGraphPolynomialSubstitution_power_iff (d t k : ℕ)
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) :
    actualGraphPolynomialSubstitution d t P ∈ HironakaRelativeNormalPolynomialJetAlgebra.actualPolynomialNormalIdeal d (1+t)^(2*k) ↔
      P ∈ HironakaRelativeNormalPolynomialJetAlgebra.actualPolynomialNormalIdeal d t^k := by
  rw [HironakaRelativeNormalPolynomialJetAlgebra.actualPolynomialNormalIdeal_power_iff_coefficients,
    HironakaRelativeNormalPolynomialJetAlgebra.actualPolynomialNormalIdeal_power_iff_coefficients]
  constructor
  · intro h α hα
    have hd : normalExponentDegree (actualGraphDiagonalExponent t α) < 2*k := by
      rw [actualGraphDiagonalExponent_degree]; omega
    simpa only [actualGraphPolynomialSubstitution_diagonal_coeff] using h (actualGraphDiagonalExponent t α) hd
  · intro h δ hδ
    by_cases hs : δ ∈ Set.range (actualGraphDiagonalExponent t)
    · obtain ⟨α,rfl⟩ := hs
      rw [actualGraphPolynomialSubstitution_diagonal_coeff]
      apply h
      rw [actualGraphDiagonalExponent_degree] at hδ
      omega
    · exact actualGraphPolynomialSubstitution_off_diagonal_coeff d t P δ hs

theorem actualGraphPolynomialSubstitution_odd_power_iff (d t k : ℕ)
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) :
    actualGraphPolynomialSubstitution d t P ∈ HironakaRelativeNormalPolynomialJetAlgebra.actualPolynomialNormalIdeal d (1+t)^(2*k+1) ↔
      P ∈ HironakaRelativeNormalPolynomialJetAlgebra.actualPolynomialNormalIdeal d t^(k+1) := by
  rw [HironakaRelativeNormalPolynomialJetAlgebra.actualPolynomialNormalIdeal_power_iff_coefficients,
    HironakaRelativeNormalPolynomialJetAlgebra.actualPolynomialNormalIdeal_power_iff_coefficients]
  constructor
  · intro h α hα
    have hd : normalExponentDegree (actualGraphDiagonalExponent t α) < 2*k+1 := by
      rw [actualGraphDiagonalExponent_degree]; omega
    simpa only [actualGraphPolynomialSubstitution_diagonal_coeff] using h (actualGraphDiagonalExponent t α) hd
  · intro h δ hδ
    by_cases hs : δ ∈ Set.range (actualGraphDiagonalExponent t)
    · obtain ⟨α,rfl⟩ := hs
      rw [actualGraphPolynomialSubstitution_diagonal_coeff]
      apply h
      rw [actualGraphDiagonalExponent_degree] at hδ
      omega
    · exact actualGraphPolynomialSubstitution_off_diagonal_coeff d t P δ hs

def actualGraphFiberExponent (t : ℕ) (δ : Fin (1+t) →₀ ℕ) : Fin t →₀ ℕ :=
  ∑ i : Fin t, Finsupp.single i (δ (actualGraphFiberIndex t i))

theorem actualGraphFiberExponent_apply (t : ℕ) (δ : Fin (1+t) →₀ ℕ) (i : Fin t) :
    actualGraphFiberExponent t δ i = δ (actualGraphFiberIndex t i) := by
  classical
  simp [actualGraphFiberExponent,Finsupp.coe_finsetSum,Finset.sum_apply,Finsupp.single_apply]

def actualGraphCentralPolynomial (d t : ℕ) :
    MvPolynomial (Fin (1+t)) (HolGerm (ComplexModel d)) →ₐ[HolGerm (ComplexModel d)]
      MvPolynomial (Fin t) (HolGerm (ComplexModel d)) :=
  MvPolynomial.aeval (fun j => if j = actualGraphParameterIndex t then 0 else actualGraphForgetVariable d t j)

theorem actualGraphCentralPolynomial_parameter (d t : ℕ) :
    actualGraphCentralPolynomial d t (MvPolynomial.X (actualGraphParameterIndex t)) = 0 := by
  simp [actualGraphCentralPolynomial]

theorem actualGraphCentralPolynomial_fiber (d t : ℕ) (i : Fin t) :
    actualGraphCentralPolynomial d t (MvPolynomial.X (actualGraphFiberIndex t i)) = MvPolynomial.X i := by
  rw [actualGraphCentralPolynomial,MvPolynomial.aeval_X,
    if_neg (actualGraphFiberIndex_ne_parameter t i),actualGraphForgetVariable_fiber]

theorem actualGraphCentralPolynomial_monomial (d t : ℕ)
    (δ : Fin (1+t) →₀ ℕ) (a : HolGerm (ComplexModel d)) :
    actualGraphCentralPolynomial d t (MvPolynomial.monomial δ a) =
      if δ (actualGraphParameterIndex t) = 0 then MvPolynomial.monomial (actualGraphFiberExponent t δ) a else 0 := by
  classical
  rw [actualGraph_monomial_parameter_fiber_product,map_mul,map_mul,map_pow,map_prod]
  have hc : actualGraphCentralPolynomial d t (MvPolynomial.C a) = MvPolynomial.C a := by
    rw [actualGraphCentralPolynomial,MvPolynomial.aeval_C]; rfl
  rw [hc,actualGraphCentralPolynomial_parameter]
  simp_rw [map_pow,actualGraphCentralPolynomial_fiber]
  split_ifs with hz
  · rw [hz,pow_zero,one_mul]
    have he : MvPolynomial.monomial (actualGraphFiberExponent t δ) a =
        MvPolynomial.C a * ∏ i : Fin t, MvPolynomial.X i ^ δ (actualGraphFiberIndex t i) := by
      rw [MvPolynomial.monomial_eq]
      rw [(actualGraphFiberExponent t δ).prod_fintype _ (fun _ => pow_zero _)]
      simp only [actualGraphFiberExponent_apply]
    exact he.symm
  · rw [zero_pow hz,zero_mul,mul_zero]

def actualGraphCentralHomogeneousPart (d t k : ℕ) :
    MvPolynomial (Fin (1+t)) (HolGerm (ComplexModel d)) →ₗ[HolGerm (ComplexModel d)]
      MvPolynomial (Fin t) (HolGerm (ComplexModel d)) :=
  (MvPolynomial.weightedHomogeneousComponent (fun _ : Fin t => (1 : ℕ)) k).comp
    (actualGraphCentralPolynomial d t).toLinearMap

theorem actualGraph_unitWeight_degree (t : ℕ) (α : Fin t →₀ ℕ) :
    Finsupp.weight (fun _ : Fin t => (1 : ℕ)) α = normalExponentDegree α := by
  rw [Finsupp.weight_eq_sum]
  simp [normalExponentDegree]

theorem actualGraphCentralHomogeneousPart_monomial (d t k : ℕ)
    (δ : Fin (1+t) →₀ ℕ) (a : HolGerm (ComplexModel d)) :
    actualGraphCentralHomogeneousPart d t k (MvPolynomial.monomial δ a) =
      if δ (actualGraphParameterIndex t) = 0 ∧ normalExponentDegree (actualGraphFiberExponent t δ) = k then
        MvPolynomial.monomial (actualGraphFiberExponent t δ) a else 0 := by
  classical
  change MvPolynomial.weightedHomogeneousComponent (fun _ : Fin t => (1 : ℕ)) k
    (actualGraphCentralPolynomial d t (MvPolynomial.monomial δ a)) = _
  rw [actualGraphCentralPolynomial_monomial]
  by_cases hz : δ (actualGraphParameterIndex t) = 0
  · rw [if_pos hz]
    have hh := MvPolynomial.isWeightedHomogeneous_monomial (fun _ : Fin t => (1 : ℕ))
      (actualGraphFiberExponent t δ) a (actualGraph_unitWeight_degree t _)
    rw [MvPolynomial.weightedHomogeneousComponent_of_mem hh]
    simp only [hz,true_and,eq_comm]
  · rw [if_neg hz,map_zero,if_neg (fun he => hz he.1)]

theorem actualGraphExponent_actual_fiber_degree (t : ℕ) (δ : Fin (1+t) →₀ ℕ) :
    normalExponentDegree δ = δ (actualGraphParameterIndex t)+normalExponentDegree (actualGraphFiberExponent t δ) := by
  rw [normalExponentDegree,Fin.sum_univ_add]
  have hp : (0 : Fin 1).castAdd t = actualGraphParameterIndex t := Fin.ext rfl
  have hf : ∀ i : Fin t, i.natAdd 1 = actualGraphFiberIndex t i := fun i =>
    Fin.ext (by simp only [actualGraphFiberIndex,Fin.val_natAdd])
  simp only [Fin.sum_univ_one,hp,hf,normalExponentDegree,actualGraphFiberExponent_apply]

theorem actualGraphExponent_actual_fiber_weight (t : ℕ) (δ : Fin (1+t) →₀ ℕ) :
    Finsupp.weight (actualGraphIntegerWeight t) δ =
      (δ (actualGraphParameterIndex t) : ℤ)-(normalExponentDegree (actualGraphFiberExponent t δ) : ℤ) := by
  rw [actualGraphIntegerWeight_exponent]
  simp_rw [← actualGraphFiberExponent_apply]
  rw [← Nat.cast_sum]
  rfl

theorem actualGraphForgetParameter_fiber_monomial (d t : ℕ) (δ : Fin (1+t) →₀ ℕ)
    (a : HolGerm (ComplexModel d)) :
    actualGraphForgetParameter d t (MvPolynomial.monomial δ a) =
      MvPolynomial.monomial (actualGraphFiberExponent t δ) a := by
  rw [actualGraphForgetParameter_monomial,MvPolynomial.monomial_eq,
    (actualGraphFiberExponent t δ).prod_fintype _ (fun _ => pow_zero _)]
  simp only [actualGraphFiberExponent_apply]

theorem actualGraph_negative_weight_central_jet_congruence (d t k : ℕ)
    (H : MvPolynomial (Fin (1+t)) (HolGerm (ComplexModel d))) :
    MvPolynomial.X (actualGraphParameterIndex t)^k*actualGraphWeightComponent d t (-(k : ℤ)) H -
      actualGraphPolynomialSubstitution d t (actualGraphCentralHomogeneousPart d t k H) ∈
        HironakaRelativeNormalPolynomialJetAlgebra.actualPolynomialNormalIdeal d (1+t)^(2*k+1) := by
  classical
  induction H using MvPolynomial.induction_on' with
  | monomial δ a =>
    have hw := actualGraphExponent_actual_fiber_weight t δ
    have hd := actualGraphExponent_actual_fiber_degree t δ
    by_cases hweight : Finsupp.weight (actualGraphIntegerWeight t) δ = -(k : ℤ)
    · have hh := MvPolynomial.isWeightedHomogeneous_monomial (actualGraphIntegerWeight t) δ a hweight
      have hpi : actualGraphWeightComponent d t (-(k : ℤ)) (MvPolynomial.monomial δ a) = MvPolynomial.monomial δ a :=
        hh.weightedHomogeneousComponent_same
      rw [hpi,actualGraphCentralHomogeneousPart_monomial]
      rw [hweight] at hw
      by_cases hz : δ (actualGraphParameterIndex t) = 0
      · have hb : normalExponentDegree (actualGraphFiberExponent t δ) = k := by rw [hz] at hw; omega
        rw [if_pos ⟨hz,hb⟩]
        have hr := actualGraph_weighted_natural_parameter_reconstruction d t 0 k (MvPolynomial.monomial δ a)
          (by simpa only [Nat.cast_zero,zero_sub] using hh)
        rw [pow_zero,one_mul,actualGraphForgetParameter_fiber_monomial] at hr
        rw [hr,sub_self]
        exact Ideal.zero_mem _
      · rw [if_neg (fun he => hz he.1),map_zero,sub_zero]
        have hm := HironakaRelativeNormalPolynomialJetAlgebra.actualPolynomialNormalIdeal_monomial_mem d (1+t) δ a
        have hp := HironakaRelativeNormalGraphWeightCancellation.actualGraphPolynomial_parameter_power_raise
          d t (normalExponentDegree δ) k (MvPolynomial.monomial δ a) hm
        exact Ideal.pow_le_pow_right (by omega : 2*k+1 ≤ normalExponentDegree δ+k) hp
    · have hh := MvPolynomial.isWeightedHomogeneous_monomial (actualGraphIntegerWeight t) δ a rfl
      have hpi : actualGraphWeightComponent d t (-(k : ℤ)) (MvPolynomial.monomial δ a) = 0 :=
        hh.weightedHomogeneousComponent_ne _ (Ne.symm hweight)
      have hc : ¬ (δ (actualGraphParameterIndex t) = 0 ∧ normalExponentDegree (actualGraphFiberExponent t δ) = k) := by
        rintro ⟨hz,hb⟩
        apply hweight
        rw [hz,hb] at hw
        simpa only [Nat.cast_zero,zero_sub] using hw
      rw [hpi,mul_zero,actualGraphCentralHomogeneousPart_monomial,if_neg hc,map_zero,sub_zero]
      exact Ideal.zero_mem _
  | add P Q hP hQ =>
    rw [map_add,map_add,map_add,mul_add]
    convert (HironakaRelativeNormalPolynomialJetAlgebra.actualPolynomialNormalIdeal d (1+t)^(2*k+1)).add_mem hP hQ using 1
    ring

end
end Hironaka.HironakaRelativeNormalGraphDiagonalCoefficients
