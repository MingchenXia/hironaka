/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.Data.Set.Finite.Lattice

/-!
# A genuine domain criterion from principal prime families

Pairwise noncontaining principal prime ideals force arbitrarily high adic order.
Krull intersection then proves the actual ring has no zero divisors.
-/

open IsLocalRing

set_option autoImplicit false

namespace DeJongAlterations.Algebra.RegularLocalDomainPrimeFamily

noncomputable section

variable {R ι : Type*} [CommRing R]

/-- Membership in many distinct principal primes forces the corresponding adic order. -/
theorem mem_pow_card_of_principal_primes (m : Ideal R) (p : ι → R) (S : Finset ι)
    (hp : ∀ i ∈ S, p i ∈ m)
    (hprime : ∀ i ∈ S, (Ideal.span ({p i} : Set R)).IsPrime)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → p i ∉ Ideal.span ({p j} : Set R))
    {a : R} (ha : ∀ i ∈ S, a ∈ Ideal.span ({p i} : Set R)) : a ∈ m ^ S.card := by
  classical
  induction S using Finset.induction_on generalizing a with
  | empty => simp
  | @insert i S hi ih =>
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp (ha i (Finset.mem_insert_self _ _))
    have hbS : ∀ j ∈ S, b ∈ Ideal.span ({p j} : Set R) := by
      intro j hj
      have hj' := hprime j (Finset.mem_insert_of_mem hj)
      have hab : p i * b ∈ Ideal.span ({p j} : Set R) :=
        hb ▸ ha j (Finset.mem_insert_of_mem hj)
      exact (hj'.mem_or_mem hab).resolve_left
        (hsep i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
          (fun hij ↦ hi (hij ▸ hj)))
    have hbpow : b ∈ m ^ S.card := ih
      (fun j hj ↦ hp j (Finset.mem_insert_of_mem hj))
      (fun j hj ↦ hprime j (Finset.mem_insert_of_mem hj))
      (fun j hj k hk hjk ↦ hsep j (Finset.mem_insert_of_mem hj)
        k (Finset.mem_insert_of_mem hk) hjk) hbS
    rw [Finset.card_insert_of_notMem hi, pow_succ']
    exact hb ▸ Ideal.mul_mem_mul (hp i (Finset.mem_insert_self _ _)) hbpow

/-- Infinitely many pairwise noncontaining principal primes characterize a domain locally. -/
theorem isDomain_of_infinite_principal_primes [IsLocalRing R] [IsNoetherianRing R]
    (p : ℕ → R) (hp : ∀ n, p n ∈ maximalIdeal R)
    (hprime : ∀ n, (Ideal.span ({p n} : Set R)).IsPrime)
    (hsep : ∀ n m, n ≠ m → p n ∉ Ideal.span ({p m} : Set R)) : IsDomain R := by
  classical
  have hkill (a : R) (ha : Set.Infinite {n | a ∈ Ideal.span ({p n} : Set R)}) : a = 0 := by
    have hpow : ∀ n : ℕ, a ∈ maximalIdeal R ^ n := by
      intro n
      obtain ⟨S, hS, hcard⟩ := ha.exists_subset_card_eq n
      have h := mem_pow_card_of_principal_primes (maximalIdeal R) p S
        (fun i _ ↦ hp i) (fun i _ ↦ hprime i) (fun i _ j _ hij ↦ hsep i j hij)
        (fun i hi ↦ hS hi)
      simpa only [hcard] using h
    have haInf : a ∈ ⨅ n : ℕ, maximalIdeal R ^ n := (Submodule.mem_iInf _).mpr hpow
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top] at haInf
    exact haInf
  have hz : ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0 := by
    intro a b hab
    by_cases ha : Set.Infinite {n | a ∈ Ideal.span ({p n} : Set R)}
    · exact Or.inl (hkill a ha)
    · apply Or.inr
      apply hkill b
      have hb : {n | a ∈ Ideal.span ({p n} : Set R)} ∪
          {n | b ∈ Ideal.span ({p n} : Set R)} = Set.univ := by
        ext n
        simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        exact (hprime n).mem_or_mem (hab ▸ (Ideal.span ({p n} : Set R)).zero_mem)
      have hinf : Set.Infinite ({n | a ∈ Ideal.span ({p n} : Set R)} ∪
          {n | b ∈ Ideal.span ({p n} : Set R)}) := hb ▸ Set.infinite_univ
      exact (Set.infinite_union.mp hinf).resolve_left ha
  let : NoZeroDivisors R := ⟨fun {a b} ↦ hz a b⟩
  exact { (inferInstance : Nontrivial R), (inferInstance : IsCancelMulZero R) with }

end

end DeJongAlterations.Algebra.RegularLocalDomainPrimeFamily
