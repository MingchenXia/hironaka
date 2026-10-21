/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Mathlib.Data.Finsupp.MonomialOrder.DegLex

/-!
# Genuine positive integer weights for all bounded lower deg-lex exponents

One explicitly produced weight works for every lower exponent of bounded
total degree, against arbitrary upper exponents. This is the finite order
ingredient for an actual common-radius analytic vertex division argument.
Blueprint: `hironaka-actual-deg-lex-positive-weights-extension.tex`.
-/
set_option autoImplicit false
open Classical
open scoped BigOperators
namespace Hironaka.HironakaActualDegLexPositiveWeights
noncomputable section

private theorem sum_split_at {n : ℕ} (f : Fin n → ℕ) (j : Fin n) :
    (∑ i,f i)=(∑ i ∈ Finset.univ.filter (fun i : Fin n => i < j),f i)+f j+
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => j < i),f i := by
  have h := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin n => i < j) f
  have he : Finset.univ.filter (fun i : Fin n => ¬i < j)=
      insert j (Finset.univ.filter (fun i : Fin n => j < i)) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert]
    omega
  rw [he,Finset.sum_insert (by simp)] at h
  omega

private theorem radix_tail_bound {n D : ℕ} (a : Fin n →₀ ℕ) (ha : a.degree≤D) (j : Fin n) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => j < i),a i*(D+2)^(n-i.val))<
      (D+2)^(n-j.val) := by
  have hdeg : (∑ i : Fin n,a i)≤D := by simpa only [Finsupp.degree_eq_sum] using ha
  have hsum : (∑ i ∈ Finset.univ.filter (fun i : Fin n => j < i),a i)≤D :=
    (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)).trans hdeg
  have hbound : (∑ i ∈ Finset.univ.filter (fun i : Fin n => j < i),a i*(D+2)^(n-i.val))≤
      D*(D+2)^(n-(j.val+1)) := by
    calc
      _ ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => j < i),a i*(D+2)^(n-(j.val+1)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hji : j.val < i.val := (Finset.mem_filter.mp hi).2
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega : 0<D+2) (by omega))
      _ = (∑ i ∈ Finset.univ.filter (fun i : Fin n => j < i),a i)*(D+2)^(n-(j.val+1)) :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ _ := Nat.mul_le_mul_right _ hsum
  have hexp : n-j.val=n-(j.val+1)+1 := by omega
  apply hbound.trans_lt
  rw [hexp,pow_succ]
  exact (Nat.mul_lt_mul_of_pos_right (by omega : D<D+2) (Nat.pow_pos (by omega))).trans_eq (Nat.mul_comm _ _)

/-- Literal radix weights preserve every lex comparison with a degree-bounded lower exponent. -/
theorem bounded_lex_radix_strict {n D : ℕ} (a b : Fin n →₀ ℕ) (ha : a.degree≤D)
    (hab : toLex a<toLex b) :
    (∑ i : Fin n,a i*(D+2)^(n-i.val))<(∑ i : Fin n,b i*(D+2)^(n-i.val)) := by
  obtain ⟨j,hpre,hj⟩ := Finsupp.Lex.lt_iff.mp hab
  simp only [ofLex_toLex] at hpre hj
  have heq : (∑ i ∈ Finset.univ.filter (fun i : Fin n => i < j),a i*(D+2)^(n-i.val))=
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i < j),b i*(D+2)^(n-i.val) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hpre i (Finset.mem_filter.mp hi).2]
  have htail := radix_tail_bound a ha j
  have hcoord : (a j+1)*(D+2)^(n-j.val)≤b j*(D+2)^(n-j.val) :=
    Nat.mul_le_mul_right _ (by omega)
  have hA := sum_split_at (fun i : Fin n => a i*(D+2)^(n-i.val)) j
  have hB := sum_split_at (fun i : Fin n => b i*(D+2)^(n-i.val)) j
  rw [heq] at hA
  rw [Nat.add_mul,Nat.one_mul] at hcoord
  omega

private theorem radix_bound {n D : ℕ} (a : Fin n →₀ ℕ) (ha : a.degree≤D) :
    (∑ i : Fin n,a i*(D+2)^(n-i.val))≤D*(D+2)^n := by
  calc
    _ ≤ ∑ i : Fin n,a i*(D+2)^n := by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega : 0<D+2) (by omega))
    _ = a.degree*(D+2)^n := by rw [Finsupp.degree_eq_sum,Finset.sum_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ ha

/-- One internally constructed positive integer weight realizes ALL bounded lower deg-lex comparisons. -/
theorem exists_positive_weights_of_bounded_degLex (n D : ℕ) :
    ∃ w : Fin n → ℕ,(∀ i,0<w i) ∧
      ∀ a b : Fin n →₀ ℕ,a.degree≤D →
        (MonomialOrder.degLex (σ := Fin n)).toSyn a<(MonomialOrder.degLex (σ := Fin n)).toSyn b →
          Finsupp.weight w a<Finsupp.weight w b := by
  let M := D*(D+2)^n+1
  let w : Fin n → ℕ := fun i => M+(D+2)^(n-i.val)
  have hw (a : Fin n →₀ ℕ) : Finsupp.weight w a=M*a.degree+∑ i : Fin n,a i*(D+2)^(n-i.val) := by
    simp only [Finsupp.weight_eq_sum,w,nsmul_eq_mul,Nat.cast_id,mul_add,Finset.sum_add_distrib,
      Finsupp.degree_eq_sum,Finset.sum_mul,mul_comm M]
  refine ⟨w,fun i => by dsimp [w,M];omega,?_⟩
  intro a b ha hab
  rw [hw,hw]
  have hr := radix_bound a ha
  change toDegLex a<toDegLex b at hab
  rcases Finsupp.DegLex.lt_iff.mp hab with hd | ⟨hd,hl⟩
  · change a.degree < b.degree at hd
    have hdeg : M*(a.degree+1)≤M*b.degree := Nat.mul_le_mul_left _ (by omega)
    have hrM : (∑ i : Fin n,a i*(D+2)^(n-i.val)) < M := by dsimp [M];omega
    calc
      _ < M*a.degree+M := Nat.add_lt_add_left hrM _
      _ ≤ M*b.degree := by simpa only [Nat.mul_add,Nat.mul_one] using hdeg
      _ ≤ _ := Nat.le_add_right _ _
  · have hlex := bounded_lex_radix_strict a b ha hl
    change a.degree=b.degree at hd
    rw [hd]
    exact Nat.add_lt_add_left hlex _

end
end Hironaka.HironakaActualDegLexPositiveWeights
