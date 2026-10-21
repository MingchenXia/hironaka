/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Mathlib.RingTheory.Ideal.Operations

set_option autoImplicit false
namespace Hironaka.HironakaStrictFilteredRegularElement

variable {R : Type*} [CommRing R]

/-- An actual regular degree-one symbol gives exact successor division for the ENTIRE original ideal denominators. -/
theorem mem_successor_iff_mem_current_of_regular_symbol
    (I N : Ideal R) (v : R) (hv : v ∈ N)
    (hreg : ∀ q : ℕ, ∀ b ∈ N^q, v*b ∈ I ⊔ N^(q+2) → b ∈ I ⊔ N^(q+1))
    (q : ℕ) (a : R) : v*a ∈ I ⊔ N^(q+1) ↔ a ∈ I ⊔ N^q := by
  have hmul (q : ℕ) (a : R) (ha : a ∈ I ⊔ N^q) : v*a ∈ I ⊔ N^(q+1) := by
    obtain ⟨i, hi, b, hb, he⟩ := Submodule.mem_sup.mp ha
    rw [← he, mul_add]
    apply (I ⊔ N^(q+1)).add_mem
    · exact (le_sup_left : I ≤ I ⊔ N^(q+1)) (I.mul_mem_left v hi)
    · apply (le_sup_right : N^(q+1) ≤ I ⊔ N^(q+1))
      rw [pow_succ']
      exact Ideal.mul_mem_mul hv hb
  induction q generalizing a with
  | zero =>
      constructor
      · intro _
        simp
      · exact hmul 0 a
  | succ q ih =>
      constructor
      · intro h
        have hlow : v*a ∈ I ⊔ N^(q+1) := by
          have hp : N^(q+2) ≤ N^(q+1) := by
            rw [pow_succ]
            exact Ideal.mul_le_left
          exact (sup_le_sup le_rfl hp : I ⊔ N^(q+2) ≤ I ⊔ N^(q+1)) h
        obtain ⟨i, hi, b, hb, he⟩ := Submodule.mem_sup.mp ((ih a).mp hlow)
        have hIb : v*b ∈ I ⊔ N^(q+2) := by
          have hEq : v*b = v*a-v*i := by rw [← he, mul_add, add_sub_cancel_left]
          rw [hEq]
          exact (I ⊔ N^(q+2)).sub_mem h ((le_sup_left : I ≤ I ⊔ N^(q+2)) (I.mul_mem_left v hi))
        rw [← he]
        exact (I ⊔ N^(q+1)).add_mem ((le_sup_left : I ≤ I ⊔ N^(q+1)) hi) (hreg q b hb hIb)
      · exact hmul (q+1) a

/-- The ENTIRE principal image meets every actual ideal-power denominator strictly, with no separatedness hypothesis. -/
theorem sup_pow_inf_principal_of_regular_symbol
    (I N : Ideal R) (v : R) (hv : v ∈ N)
    (hreg : ∀ q : ℕ, ∀ b ∈ N^q, v*b ∈ I ⊔ N^(q+2) → b ∈ I ⊔ N^(q+1))
    (q : ℕ) :
    (I ⊔ N^(q+1)) ⊓ (I ⊔ Ideal.span ({v} : Set R)) =
      I ⊔ Ideal.span ({v} : Set R)*N^q := by
  have hs : Ideal.span ({v} : Set R) ≤ N := by
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hv)
  apply le_antisymm
  · intro x hx
    obtain ⟨i, hi, j, hj, he⟩ := Submodule.mem_sup.mp hx.2
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hj
    have hva : v*a ∈ I ⊔ N^(q+1) := by
      have hEq : v*a=x-i := by rw [← he, add_sub_cancel_left]
      rw [hEq]
      exact (I ⊔ N^(q+1)).sub_mem hx.1 ((le_sup_left : I ≤ I ⊔ N^(q+1)) hi)
    obtain ⟨j, hj, b, hb, hba⟩ := Submodule.mem_sup.mp
      ((mem_successor_iff_mem_current_of_regular_symbol I N v hv hreg q a).mp hva)
    have hxEq : x=(i+v*j)+v*b := by rw [← he, ← hba, mul_add, add_assoc]
    rw [hxEq]
    apply (I ⊔ Ideal.span ({v} : Set R)*N^q).add_mem
    · exact (le_sup_left : I ≤ I ⊔ Ideal.span ({v} : Set R)*N^q)
        (I.add_mem hi (I.mul_mem_left v hj))
    · apply (le_sup_right : Ideal.span ({v} : Set R)*N^q ≤ I ⊔ Ideal.span ({v} : Set R)*N^q)
      exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self v) hb
  · apply sup_le
    · exact le_inf le_sup_left le_sup_left
    · apply le_inf
      · apply Ideal.mul_le.mpr
        intro a ha b hb
        apply (le_sup_right : N^(q+1) ≤ I ⊔ N^(q+1))
        rw [pow_succ']
        exact Ideal.mul_mem_mul (hs ha) hb
      · exact le_trans Ideal.mul_le_left le_sup_right

end Hironaka.HironakaStrictFilteredRegularElement
