import DeJongAlterations.Algebra.RegularQuotient
import DeJongAlterations.Algebra.RegularLocalDomain
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain

/-!
# Elements vanishing only on a normal crossings divisor are monomials

This file proves the elementary commutative algebra step of de Jong's local description of a
semi-stable curve over a base with a strict normal crossings divisor
(de Jong 1996, 3.3, `references/dejong96-alterations/tex/page-0014.tex`):

> By assumption we have `V(h) ⊂ V(t_1 ⋯ t_r)`. Therefore we see that
> `h = ε · t_1^{n_1} ⋯ t_r^{n_r}`, `ε ∈ (A')^*`.

## Main results

* `exists_unit_mul_prod_pow_of_forall_isPrime`: in a Noetherian domain `R`, let `t_i` be prime
  elements and let `h` be an element such that every prime ideal containing `h` contains some
  `t_i`. Then `h = ε ∏ t_i ^ n_i` with `ε` a unit.
* `exists_unit_mul_prod_pow_of_mem_radical`: the same with the hypothesis written as
  `∏ t_i ∈ √(h)`, i.e. `V(h) ⊆ V(t_1 ⋯ t_r)`.
* `prime_of_mem_maximalIdeal_of_not_mem_sq`: an element of `𝔪 ∖ 𝔪²` of a regular local ring is a
  prime element. This applies to the members `t_i` of a regular system of parameters, which is how
  the local equations of the components of a strict normal crossings divisor occur.

The proof does not use that regular local rings are factorial. If `h` is not a unit, take a prime
`𝔭` minimal over `h`; it contains some `t_i`, and Krull's principal ideal theorem gives
`ht 𝔭 ≤ 1`, so the nonzero prime `(t_i) ⊆ 𝔭` equals `𝔭` and `t_i ∣ h`. Divide and conclude by
well-founded induction on strict divisibility (a Noetherian domain is a `WfDvdMonoid`).
-/

namespace DeJongAlterations.StableModification.Resolution

open IsLocalRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]

/-- In a Noetherian domain, a nonunit `h` such that every prime ideal containing `h` contains one
of the prime elements `t_i` is divisible by one of the `t_i` (Krull's principal ideal theorem). -/
theorem exists_dvd_of_forall_isPrime {ι : Type*} (t : ι → R) (ht : ∀ i, Prime (t i))
    {h : R} (hh : ¬ IsUnit h)
    (hV : ∀ P : Ideal R, P.IsPrime → h ∈ P → ∃ i, t i ∈ P) : ∃ i, t i ∣ h := by
  have hne : Ideal.span {h} ≠ ⊤ := by
    rwa [Ne, Ideal.span_singleton_eq_top]
  obtain ⟨P, hP⟩ := Ideal.nonempty_minimalPrimes hne
  have hPprime : P.IsPrime := hP.1.1
  have hhP : h ∈ P := (Ideal.span_singleton_le_iff_mem P).mp hP.1.2
  obtain ⟨i, hi⟩ := hV P hPprime hhP
  have hti : (Ideal.span {t i}).IsPrime := Ideal.isPrime_span_singleton_of_prime (ht i)
  have hle : Ideal.span {t i} ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr hi
  have heq : Ideal.span {t i} = P := by
    by_contra hneq
    have hlt : Ideal.span {t i} < P := lt_of_le_of_ne hle hneq
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    have h2 : P.height ≤ 1 :=
      Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {h}) P hP
    have h3 : (Ideal.span {t i}).height = 0 := by
      have h4 : (Ideal.span {t i}).height + 1 ≤ 1 := h1.trans h2
      generalize (Ideal.span {t i}).height = a at h4
      induction a using ENat.recTopCoe with
      | top => simp at h4
      | coe a =>
        have : (a : ℕ∞) + 1 = ((a + 1 : ℕ) : ℕ∞) := by push_cast; rfl
        rw [this] at h4
        have : a + 1 ≤ 1 := by exact_mod_cast h4
        have : a = 0 := by omega
        simp [this]
    rw [Ideal.height_eq_zero_iff_eq_bot, Ideal.span_singleton_eq_bot] at h3
    exact (ht i).ne_zero h3
  refine ⟨i, ?_⟩
  rw [← Ideal.mem_span_singleton, heq]
  exact hhP

/-- **de Jong 3.3, monomial step.** In a Noetherian domain, if every prime ideal containing `h`
contains one of the prime elements `t_i`, then `h` is a unit times a monomial in the `t_i`.
No factoriality of the ring and no pairwise non-association of the `t_i` is needed. -/
theorem exists_unit_mul_prod_pow_of_forall_isPrime {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ι → R) (ht : ∀ i, Prime (t i)) (h : R)
    (hV : ∀ P : Ideal R, P.IsPrime → h ∈ P → ∃ i, t i ∈ P) :
    ∃ (ε : Rˣ) (n : ι → ℕ), h = ε * ∏ i, t i ^ n i := by
  have h0 : h ≠ 0 := by
    intro h0
    obtain ⟨i, hi⟩ := hV ⊥ Ideal.isPrime_bot (h0 ▸ Ideal.zero_mem _)
    exact (ht i).ne_zero ((Submodule.mem_bot R).mp hi)
  refine (wellFounded_dvdNotUnit (α := R)).induction
    (C := fun h => h ≠ 0 → (∀ P : Ideal R, P.IsPrime → h ∈ P → ∃ i, t i ∈ P) →
      ∃ (ε : Rˣ) (n : ι → ℕ), h = ε * ∏ i, t i ^ n i) h ?_ h0 hV
  intro h ih h0 hV
  by_cases hu : IsUnit h
  · exact ⟨hu.unit, 0, by simp⟩
  obtain ⟨i, g, rfl⟩ := exists_dvd_of_forall_isPrime t ht hu hV
  have hg0 : g ≠ 0 := right_ne_zero_of_mul h0
  have hdvd : DvdNotUnit g (t i * g) := ⟨hg0, t i, (ht i).not_isUnit, mul_comm _ _⟩
  have hVg : ∀ P : Ideal R, P.IsPrime → g ∈ P → ∃ j, t j ∈ P :=
    fun P hP hgP => hV P hP (P.mul_mem_left _ hgP)
  obtain ⟨ε, n, hn⟩ := ih g hdvd hg0 hVg
  refine ⟨ε, n + Pi.single i 1, ?_⟩
  have hsingle : ∏ j, t j ^ (Pi.single i 1 : ι → ℕ) j = t i := by
    rw [Fintype.prod_eq_single i (fun j hj => by simp [hj])]
    simp
  simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib, hsingle, hn]
  ring

/-- **de Jong 3.3, monomial step**, in the form `V(h) ⊆ V(t_1 ⋯ t_r)`, i.e.
`t_1 ⋯ t_r ∈ √(h)`. -/
theorem exists_unit_mul_prod_pow_of_mem_radical {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ι → R) (ht : ∀ i, Prime (t i)) (h : R)
    (hV : ∏ i, t i ∈ (Ideal.span {h}).radical) :
    ∃ (ε : Rˣ) (n : ι → ℕ), h = ε * ∏ i, t i ^ n i := by
  refine exists_unit_mul_prod_pow_of_forall_isPrime t ht h fun P hP hhP => ?_
  have hle : (Ideal.span {h}).radical ≤ P :=
    hP.radical_le_iff.mpr ((Ideal.span_singleton_le_iff_mem P).mpr hhP)
  obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_mem_iff (p := P)).mp (hle hV)
  exact ⟨i, hi⟩

omit [IsDomain R] [IsNoetherianRing R] in
/-- A unit times a monomial lying in the maximal ideal has positive total degree. -/
theorem one_le_sum_of_unit_mul_prod_pow_mem_maximalIdeal [IsLocalRing R] {ι : Type*}
    [Fintype ι] (t : ι → R) (ε : Rˣ) (n : ι → ℕ)
    (hh : (ε : R) * ∏ i, t i ^ n i ∈ maximalIdeal R) : 1 ≤ ∑ i, n i := by
  by_contra hlt
  have hzero : ∀ i, n i = 0 := by
    intro i
    have := Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i)
    omega
  simp [hzero] at hh

/-- An element of `𝔪 ∖ 𝔪²` of a regular local ring is prime: the quotient by it is again a
regular local ring (`Algebra.RegularQuotient.isRegularLocalRing_quotient_parameter`), hence a
domain (`Algebra.RegularLocalDomain.isDomain_of_isRegularLocalRing`). -/
theorem prime_of_mem_maximalIdeal_of_not_mem_sq {A : Type*} [CommRing A] [IsRegularLocalRing A]
    {t : A} (ht : t ∈ maximalIdeal A) (ht2 : t ∉ maximalIdeal A ^ 2) : Prime t := by
  have hreg := Algebra.RegularQuotient.isRegularLocalRing_quotient_parameter A t ht ht2
  have hdom : IsDomain (A ⧸ Ideal.span {t}) :=
    Algebra.RegularLocalDomain.isDomain_of_isRegularLocalRing _
  have h0 : t ≠ 0 := by
    rintro rfl
    exact ht2 (Ideal.zero_mem _)
  exact (Ideal.span_singleton_prime h0).mp ((Ideal.Quotient.isDomain_iff_prime _).mp hdom)

end DeJongAlterations.StableModification.Resolution
