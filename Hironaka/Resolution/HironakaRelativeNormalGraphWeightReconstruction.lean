/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalGraphWeightComponents
import Mathlib.Algebra.BigOperators.Fin

/-! Actual original polynomial reconstruction of selected integer-weight graph
coefficients. Four full mathematics proofs preceded Lean. OWN OFFLIB only.
Reverse analytic central initial ideal and nearby whole cone/Rees/ALLq OPEN. -/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaRelativeNormalGraphWeightReconstruction
noncomputable section
open HolGerm HironakaRelativeNormalGraphWeightJets
  HironakaRelativeNormalGraphWeightComponents

def actualGraphForgetVariable (d t : ℕ) (j : Fin (1+t)) :
    MvPolynomial (Fin t) (HolGerm (ComplexModel d)) :=
  if h : j.val = 0 then 1 else MvPolynomial.X ⟨j.val-1,by omega⟩

theorem actualGraphForgetVariable_parameter (d t : ℕ) :
    actualGraphForgetVariable d t (actualGraphParameterIndex t) = 1 := by
  simp [actualGraphForgetVariable,actualGraphParameterIndex]

theorem actualGraphForgetVariable_fiber (d t : ℕ) (i : Fin t) :
    actualGraphForgetVariable d t (actualGraphFiberIndex t i) = MvPolynomial.X i := by
  have hn : (actualGraphFiberIndex t i).val ≠ 0 := by simp only [actualGraphFiberIndex]; omega
  rw [actualGraphForgetVariable,dif_neg hn]
  apply congrArg MvPolynomial.X
  exact Fin.ext (by simp only [actualGraphFiberIndex]; omega)

def actualGraphForgetParameter (d t : ℕ) :
    MvPolynomial (Fin (1+t)) (HolGerm (ComplexModel d)) →ₐ[HolGerm (ComplexModel d)]
      MvPolynomial (Fin t) (HolGerm (ComplexModel d)) :=
  MvPolynomial.aeval (actualGraphForgetVariable d t)

theorem actualGraphForgetParameter_substitution (d t : ℕ)
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) :
    actualGraphForgetParameter d t (actualGraphPolynomialSubstitution d t P) = P := by
  have h : (actualGraphForgetParameter d t).comp (actualGraphPolynomialSubstitution d t) =
      AlgHom.id (HolGerm (ComplexModel d)) (MvPolynomial (Fin t) (HolGerm (ComplexModel d))) := by
    apply MvPolynomial.algHom_ext
    intro i
    change actualGraphForgetParameter d t (actualGraphPolynomialSubstitution d t (MvPolynomial.X i)) = _
    rw [actualGraphPolynomialSubstitution,MvPolynomial.aeval_X,map_mul]
    simp only [actualGraphForgetParameter,MvPolynomial.aeval_X,
      actualGraphForgetVariable_parameter,actualGraphForgetVariable_fiber,one_mul,AlgHom.id_apply]
  exact DFunLike.congr_fun h P

theorem actualGraphPolynomialSubstitution_injective (d t : ℕ) :
    Function.Injective (actualGraphPolynomialSubstitution d t) := by
  intro P Q h
  have he := congrArg (actualGraphForgetParameter d t) h
  simpa only [actualGraphForgetParameter_substitution] using he

theorem actualGraphIntegerWeight_exponent (t : ℕ) (α : Fin (1+t) →₀ ℕ) :
    Finsupp.weight (actualGraphIntegerWeight t) α =
      (α (actualGraphParameterIndex t) : ℤ) - ∑ i : Fin t, (α (actualGraphFiberIndex t i) : ℤ) := by
  rw [Finsupp.weight_eq_sum,Fin.sum_univ_add]
  have hp : (0 : Fin 1).castAdd t = actualGraphParameterIndex t := Fin.ext rfl
  have hf : ∀ i : Fin t, i.natAdd 1 = actualGraphFiberIndex t i := fun i => Fin.ext (by simp only [actualGraphFiberIndex,Fin.val_natAdd])
  simp only [Fin.sum_univ_one,hp,hf,actualGraphIntegerWeight_parameter,actualGraphIntegerWeight_fiber]
  simp only [nsmul_eq_mul,mul_one,mul_neg_one,Finset.sum_neg_distrib,sub_eq_add_neg]

theorem actualGraphForgetParameter_monomial (d t : ℕ) (α : Fin (1+t) →₀ ℕ)
    (a : HolGerm (ComplexModel d)) :
    actualGraphForgetParameter d t (MvPolynomial.monomial α a) =
      MvPolynomial.C a * ∏ i : Fin t, MvPolynomial.X i ^ α (actualGraphFiberIndex t i) := by
  classical
  rw [actualGraphForgetParameter,MvPolynomial.aeval_monomial]
  change MvPolynomial.C a * α.prod (fun i k => actualGraphForgetVariable d t i ^ k) = _
  rw [α.prod_fintype _ (fun _ => pow_zero _),Fin.prod_univ_add]
  have hp : (0 : Fin 1).castAdd t = actualGraphParameterIndex t := Fin.ext rfl
  have hf : ∀ i : Fin t, i.natAdd 1 = actualGraphFiberIndex t i := fun i => Fin.ext (by simp only [actualGraphFiberIndex,Fin.val_natAdd])
  simp only [Fin.prod_univ_one,hp,hf,actualGraphForgetVariable_parameter,
    actualGraphForgetVariable_fiber,one_pow,one_mul]

theorem actualGraphSubstitution_forgotten_monomial (d t : ℕ) (α : Fin (1+t) →₀ ℕ)
    (a : HolGerm (ComplexModel d)) :
    actualGraphPolynomialSubstitution d t (actualGraphForgetParameter d t (MvPolynomial.monomial α a)) =
      MvPolynomial.C a * ((MvPolynomial.X (actualGraphParameterIndex t)) ^
        (∑ i : Fin t, α (actualGraphFiberIndex t i)) *
        ∏ i : Fin t, MvPolynomial.X (actualGraphFiberIndex t i) ^ α (actualGraphFiberIndex t i)) := by
  classical
  rw [actualGraphForgetParameter_monomial,map_mul,map_prod]
  have hc : actualGraphPolynomialSubstitution d t (MvPolynomial.C a) = MvPolynomial.C a := by
    rw [actualGraphPolynomialSubstitution,MvPolynomial.aeval_C]
    rfl
  rw [hc]
  simp_rw [map_pow,actualGraphPolynomialSubstitution,MvPolynomial.aeval_X,mul_pow]
  rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]

theorem actualGraph_monomial_parameter_fiber_product (d t : ℕ) (α : Fin (1+t) →₀ ℕ)
    (a : HolGerm (ComplexModel d)) :
    MvPolynomial.monomial α a = MvPolynomial.C a *
      (MvPolynomial.X (actualGraphParameterIndex t) ^ α (actualGraphParameterIndex t) *
        ∏ i : Fin t, MvPolynomial.X (actualGraphFiberIndex t i) ^ α (actualGraphFiberIndex t i)) := by
  classical
  rw [MvPolynomial.monomial_eq]
  rw [α.prod_fintype _ (fun _ => pow_zero _),Fin.prod_univ_add]
  have hp : (0 : Fin 1).castAdd t = actualGraphParameterIndex t := Fin.ext rfl
  have hf : ∀ i : Fin t, i.natAdd 1 = actualGraphFiberIndex t i := fun i => Fin.ext (by simp only [actualGraphFiberIndex,Fin.val_natAdd])
  simp only [Fin.prod_univ_one,hp,hf]

theorem actualGraph_weighted_natural_parameter_reconstruction (d t N k : ℕ)
    (P : MvPolynomial (Fin (1+t)) (HolGerm (ComplexModel d)))
    (hP : MvPolynomial.IsWeightedHomogeneous (actualGraphIntegerWeight t) P ((N : ℤ)-k)) :
    MvPolynomial.X (actualGraphParameterIndex t)^k * P =
      MvPolynomial.X (actualGraphParameterIndex t)^N *
        actualGraphPolynomialSubstitution d t (actualGraphForgetParameter d t P) := by
  classical
  induction hP using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp only [map_zero,mul_zero]
  | add P Q hP hQ ihP ihQ =>
    rw [map_add,map_add,mul_add,mul_add,ihP,ihQ]
  | monomial α a hα =>
    have hw := actualGraphIntegerWeight_exponent t α
    rw [hα] at hw
    have he : k+α (actualGraphParameterIndex t) = N+∑ i : Fin t, α (actualGraphFiberIndex t i) := by
      rw [← Nat.cast_sum] at hw
      omega
    rw [actualGraphSubstitution_forgotten_monomial,actualGraph_monomial_parameter_fiber_product]
    calc
      _ = MvPolynomial.C a * (MvPolynomial.X (actualGraphParameterIndex t) ^
          (k+α (actualGraphParameterIndex t)) * ∏ i : Fin t,
          MvPolynomial.X (actualGraphFiberIndex t i) ^ α (actualGraphFiberIndex t i)) := by rw [pow_add]; ring
      _ = _ := by rw [he,pow_add]; ring

theorem actualGraph_component_natural_parameter_reconstruction (d t N k : ℕ)
    (A : MvPolynomial (Fin (1+t)) (HolGerm (ComplexModel d))) :
    MvPolynomial.X (actualGraphParameterIndex t)^k * actualGraphWeightComponent d t ((N : ℤ)-k) A =
      MvPolynomial.X (actualGraphParameterIndex t)^N * actualGraphPolynomialSubstitution d t
        (actualGraphForgetParameter d t (actualGraphWeightComponent d t ((N : ℤ)-k) A)) :=
  actualGraph_weighted_natural_parameter_reconstruction d t N k _
    (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous _ A)

def actualGraphReconstructedCoefficient (d t N k : ℕ)
    (A : MvPolynomial (Fin (1+t)) (HolGerm (ComplexModel d))) :
    MvPolynomial (Fin t) (HolGerm (ComplexModel d)) :=
  actualGraphForgetParameter d t (actualGraphWeightComponent d t ((N : ℤ)-k) A)

theorem actualGraph_finite_relation_reconstruction (d t N k : ℕ) {ι : Type*}
    (S : Finset ι) (A : ι → MvPolynomial (Fin (1+t)) (HolGerm (ComplexModel d)))
    (P : ι → MvPolynomial (Fin t) (HolGerm (ComplexModel d))) :
    MvPolynomial.X (actualGraphParameterIndex t)^k * actualGraphWeightComponent d t ((N : ℤ)-k)
      (∑ i ∈ S, A i * actualGraphPolynomialSubstitution d t (P i)) =
      MvPolynomial.X (actualGraphParameterIndex t)^N * actualGraphPolynomialSubstitution d t
        (∑ i ∈ S, actualGraphReconstructedCoefficient d t N k (A i) * P i) := by
  rw [actualGraphWeightComponent_sum_products,map_sum,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_mul,← mul_assoc,actualGraph_component_natural_parameter_reconstruction,mul_assoc]
  rfl

theorem actualGraph_reconstructed_relation_mem_original_ideal (d t N k : ℕ) {ι : Type*}
    (S : Finset ι) (A : ι → MvPolynomial (Fin (1+t)) (HolGerm (ComplexModel d)))
    (P : ι → MvPolynomial (Fin t) (HolGerm (ComplexModel d)))
    (I : Ideal (MvPolynomial (Fin t) (HolGerm (ComplexModel d)))) (hP : ∀ i ∈ S, P i ∈ I) :
    (∑ i ∈ S, actualGraphReconstructedCoefficient d t N k (A i) * P i) ∈ I := by
  apply I.sum_mem
  intro i hi
  exact I.mul_mem_left _ (hP i hi)

end
end Hironaka.HironakaRelativeNormalGraphWeightReconstruction
