/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.Order
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Hironaka.Algebra.Local.Regular
import Hironaka.Scheme.Snc.Coordinates
import Hironaka.Scheme.Snc.ParameterSubset
import Hironaka.Scheme.Snc.TrivialTotalTransform

/-!
# Parameter algebra in a regular local ring

Divisibility facts about a regular system of parameters `z` of a regular local ring `R`
[Kol07, Definition 24]: a parameter is a nonzero prime element; distinct parameters do not divide
each other; powers of distinct parameters dividing `f` divide `f` jointly; a divisor of `z_c^N` not
divisible by `z_c` is a unit. Then the membership half of the order along a subvariety
[Kol07, Definition 47] for a principal prime (`le_pow_of_le_ordAlong_span_singleton`:
`m ≤ ord_{(p)} I ⟹ I ⊆ (p)^m`), its `(p) = P` form, the joint divisibility by pairwise non-dividing
prime powers, and `ordElem_parameter` (a parameter has order one). These are the ring-level facts
behind the splitting of an ideal into its monomial and non-monomial parts along the boundary
(`Hironaka.Resolution.Algebraic.MarkedOrderReduction.Split`, Step 3 of the proof of [Kol07, Theorem
107]) and behind the components of a boundary (`Hironaka.Resolution.Algebraic.Snc.ComponentStalks`,
`Hironaka.Resolution.Algebraic.Snc.DictionaryRegular`,
`Hironaka.Resolution.Algebraic.Kol07.UnionIdealInvertible`). The names live in the namespace
`Hironaka.BMO` of the order-reduction modules that use them.
-/

public section

universe u

open IsLocalRing Ideal

namespace AlgebraicGeometry

/-! ### A. Parameters of a regular local ring -/

section Parameters

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] {n : ℕ} {z : Fin n → R}
  (hz : maximalIdeal R = span (Set.range z)) (hn : (n : WithBot ℕ∞) = ringKrullDim R)
include hz hn

/-- A member of a regular system of parameters is nonzero (it lies outside `𝔪²`). -/
theorem ne_zero_of_parameters (c : Fin n) : z c ≠ 0 := fun h =>
  (mem_maximalIdeal_and_notMem_sq_of_span_eq ⟨hz.symm, hn⟩ c).2
    (h ▸ Ideal.zero_mem _)

/-- A member of a regular system of parameters is a prime element
(`isPrime_span_singleton_of_parameters`). -/
theorem prime_of_parameters (c : Fin n) : Prime (z c) :=
  (Ideal.span_singleton_prime (ne_zero_of_parameters hz hn c)).mp
    (isPrime_span_singleton_of_parameters hz hn c)

/-- Distinct parameters do not divide each other (`notMem_span_image_of_notMem` of
`Hironaka.Scheme.Snc.ParameterSubset`). -/
theorem not_dvd_of_ne {c d : Fin n} (h : c ≠ d) : ¬ z c ∣ z d := fun hdvd =>
  notMem_span_image_of_notMem hz hn (s := {c}) (j := d)
    (fun hmem => h (Finset.mem_singleton.mp hmem).symm)
    (by rw [Finset.coe_singleton, Set.image_singleton]; exact Ideal.mem_span_singleton.mpr hdvd)

/-- A parameter outside `s` does not divide a monomial in the parameters of `s`. -/
theorem not_dvd_prod_pow {s : Finset (Fin n)} {d : Fin n} (hd : d ∉ s) (a : Fin n → ℕ) :
    ¬ z d ∣ ∏ c ∈ s, z c ^ a c := by
  intro h
  obtain ⟨c, hc, hdc⟩ := (Prime.dvd_finsetProd_iff (prime_of_parameters hz hn d) _).mp h
  exact not_dvd_of_ne hz hn (fun e => hd (by rw [e]; exact hc))
    ((prime_of_parameters hz hn d).dvd_of_dvd_pow hdc)

/-- Powers of distinct parameters dividing `f` divide `f` jointly: the intersection of the ideals
`(z_c^{a_c})` is the ideal of their product. -/
theorem prod_pow_dvd_of_forall_dvd (s : Finset (Fin n)) (a : Fin n → ℕ) {f : R}
    (h : ∀ c ∈ s, z c ^ a c ∣ f) : (∏ c ∈ s, z c ^ a c) ∣ f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert d s hd ih =>
    rw [Finset.prod_insert hd]
    obtain ⟨g, hg⟩ := ih fun c hc => h c (Finset.mem_insert_of_mem hc)
    have h1 : z d ^ a d ∣ (∏ c ∈ s, z c ^ a c) * g := hg ▸ h d (Finset.mem_insert_self d s)
    have h2 : z d ^ a d ∣ g :=
      (prime_of_parameters hz hn d).pow_dvd_of_dvd_mul_left (a d) (not_dvd_prod_pow hz hn hd a) h1
    rw [hg, mul_comm (z d ^ a d)]
    exact mul_dvd_mul_left _ h2

/-- A divisor of a power of the parameter `z_c` not divisible by `z_c` is a unit. -/
theorem isUnit_of_dvd_pow_of_not_dvd {c : Fin n} {g : R} (hg : ¬ z c ∣ g) {N : ℕ}
    (h : g ∣ z c ^ N) : IsUnit g := by
  obtain ⟨i, -, hassoc⟩ := (dvd_prime_pow (prime_of_parameters hz hn c) N).mp h
  cases i with
  | zero => exact associated_one_iff_isUnit.mp (by simpa using hassoc)
  | succ i => exact absurd ((dvd_pow_self (z c) (Nat.succ_ne_zero i)).trans hassoc.symm.dvd) hg

end Parameters

/-! ### E. Local algebra: membership from the order along a principal prime -/

section LocalAlgebra

variable {R : Type u} [CommRing R] [IsDomain R]

/-- The membership half of the order along a subvariety [Kol07, Definition 47] for a principal
prime: for a prime element `p`, `m ≤ ord_{(p)} I` (the order of `I` in the localization at `(p)`)
gives `I ⊆ (p)^m` — an element `f ∈ I` has `t s f ∈ (p^m)` with `t, s ∉ (p)`, and `p^m ∣ f` since
`p` is prime. -/
theorem le_pow_of_le_ordAlong_span_singleton {p : R} (hp : Prime p) (I : Ideal R) (m : ℕ)
    [hP : (Ideal.span {p}).IsPrime]
    (h : (m : ℕ∞) ≤ ordAlong (Ideal.span {p}) I) : I ≤ Ideal.span {p} ^ m := by
  intro f hf
  rw [ordAlong, le_ord_iff,
    ← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow, Ideal.map_le_iff_le_comap] at h
  have hf' := h hf
  rw [Ideal.mem_comap, IsLocalization.mem_map_algebraMap_iff (Ideal.span {p}).primeCompl] at hf'
  obtain ⟨⟨⟨a, ha⟩, ⟨s, hs⟩⟩, hfa⟩ := hf'
  rw [← map_mul, IsLocalization.eq_iff_exists (Ideal.span {p}).primeCompl] at hfa
  obtain ⟨⟨t, ht⟩, ht'⟩ := hfa
  have hmem : t * s * f ∈ Ideal.span {p} ^ m := by
    have h1 : t * (f * s) = t * a := ht'
    rw [show t * s * f = t * (f * s) by ring, h1]
    exact Ideal.mul_mem_left _ _ ha
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem ⊢
  have hts : ¬ p ∣ t * s := fun hd => by
    rcases hp.dvd_or_dvd hd with h | h
    · exact ht (Ideal.mem_span_singleton.mpr h)
    · exact hs (Ideal.mem_span_singleton.mpr h)
  exact hp.pow_dvd_of_dvd_mul_left m hts hmem

/-- `le_pow_of_le_ordAlong_span_singleton` for a prime ideal given as `(p)`. -/
theorem le_pow_of_le_ordAlong_of_eq_span {P : Ideal R} [P.IsPrime] {p : R} (hp : Prime p)
    (hPp : P = Ideal.span {p}) (I : Ideal R) (m : ℕ)
    (h : (m : ℕ∞) ≤ ordAlong P I) : I ≤ P ^ m := by
  subst hPp
  exact le_pow_of_le_ordAlong_span_singleton hp I m h

/-- Powers of pairwise non-dividing primes (or units) dividing `f` divide `f` jointly. -/
theorem prod_dvd_of_forall_dvd_of_pairwise {ι : Type*} (S : Finset ι) (q : ι → R)
    (hq : ∀ d ∈ S, IsUnit (q d) ∨
      ∃ p : R, Prime p ∧ (∃ a : ℕ, q d = p ^ a) ∧ ∀ i ∈ S, i ≠ d → ¬ p ∣ q i)
    {f : R} (h : ∀ i ∈ S, q i ∣ f) : (∏ i ∈ S, q i) ∣ f := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert d S hd ih =>
    rw [Finset.prod_insert hd]
    have hS : ∀ d' ∈ S, IsUnit (q d') ∨
        ∃ p : R, Prime p ∧ (∃ a : ℕ, q d' = p ^ a) ∧ ∀ i ∈ S, i ≠ d' → ¬ p ∣ q i := by
      intro d' hd'
      rcases hq d' (Finset.mem_insert_of_mem hd') with hu | ⟨p, hp, ha, hnot⟩
      · exact Or.inl hu
      · exact Or.inr ⟨p, hp, ha, fun i hi => hnot i (Finset.mem_insert_of_mem hi)⟩
    obtain ⟨g, hg⟩ := ih hS fun i hi => h i (Finset.mem_insert_of_mem hi)
    rcases hq d (Finset.mem_insert_self d S) with hu | ⟨p, hp, ⟨a, hqa⟩, hnot⟩
    · exact hu.mul_left_dvd.mpr ⟨g, hg⟩
    · have h1 : q d ∣ (∏ i ∈ S, q i) * g := hg ▸ h d (Finset.mem_insert_self d S)
      have hnp : ¬ p ∣ ∏ i ∈ S, q i := fun hd' => by
        obtain ⟨i, hi, hpi⟩ := (Prime.dvd_finsetProd_iff hp _).mp hd'
        exact hnot i (Finset.mem_insert_of_mem hi) (fun e => hd (e ▸ hi)) hpi
      rw [hqa] at h1 ⊢
      have h2 : p ^ a ∣ g := hp.pow_dvd_of_dvd_mul_left a hnp h1
      rw [hg, mul_comm (p ^ a)]
      exact mul_dvd_mul_left _ h2

end LocalAlgebra

/-- A member of a regular system of parameters has order one. -/
theorem ordElem_parameter {R : Type u} [CommRing R] [IsRegularLocalRing R] {n : ℕ} {z : Fin n → R}
    (hz : Ideal.span (Set.range z) = maximalIdeal R ∧ (n : WithBot ℕ∞) = ringKrullDim R)
    (c : Fin n) : ordElem (z c) = 1 :=
  ordElem_eq_one_iff.mpr (mem_maximalIdeal_and_notMem_sq_of_span_eq hz c)

end AlgebraicGeometry
