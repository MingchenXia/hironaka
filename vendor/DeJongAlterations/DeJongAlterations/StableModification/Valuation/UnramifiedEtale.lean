import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.Unramified.LocalStructure
import DeJongAlterations.StableModification.Valuation.Unramified

/-!
# Over a base of finite height, standard-unramified implies standard étale

This file formalizes, in ring form, Lemma 2.1.1 (`finhtlem`) and Lemma 2.1.6 (`etalelem`) of
M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), §2.1
(`semi-stable.tex`, lines 1904–1915 and 2035–2043).

* **Lemma 2.1.1 (ring form).** If a ring `C` has only finitely many prime ideals, then each
  localization `C_𝔮` at a prime is a localization `C_g` at a single element
  (`exists_isLocalization_away_of_isLocalization_atPrime`). For `C` quasi-finite over a ring `A`
  with finite spectrum (for instance a valuation ring of finite height), `C` has finitely many
  primes (`exists_isLocalization_away_of_quasiFinite`). Temkin's proof: "since `X_x` is obtained
  from `X` by removing finitely many points, `𝒪_{X,x}` can be obtained by localizing `A` by a
  single element"; here the element is found by prime avoidance.
* **Lemma 2.1.6 (direction used).** If `A = B ∩ k` has finite height and `l/k` is
  standard-unramified at `B`, then `B` is a standard étale `A`-algebra
  (`IsStdUnramified.isStandardEtale`), in particular étale (`IsStdUnramified.etale`): by
  `IsStdUnramifiedGenerator.isLocalization`, `B` is a localization of the standard étale algebra
  `A[X]_{f'}/(f)` at a prime; that algebra is quasi-finite over `A`, so by Lemma 2.1.1 the
  localization is at one element, and a localization of a standard étale algebra at one element
  is standard étale.

The converse of Lemma 2.1.6 (étale implies unramified) is not needed by the route of
`PLAN-SM-VAL.md` and is not formalized.
-/

noncomputable section

open IsLocalRing

namespace DeJongAlterations.StableModification.Valuation

section FiniteSpectrum

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- In a ring with finitely many primes, for every prime `q` there is `g ∉ q` lying in all primes
not contained in `q`. -/
theorem exists_not_mem_forall_mem_of_finite [Finite (PrimeSpectrum R)] (q : Ideal R)
    [q.IsPrime] : ∃ g ∉ q, ∀ P : Ideal R, P.IsPrime → ¬ P ≤ q → g ∈ P := by
  classical
  let T : Finset (PrimeSpectrum R) :=
    (Set.toFinite {P : PrimeSpectrum R | ¬ P.asIdeal ≤ q}).toFinset
  have hT : ¬ T.inf (fun P ↦ P.asIdeal) ≤ q := by
    rw [Ideal.IsPrime.inf_le' inferInstance]
    rintro ⟨P, hP, hPq⟩
    rw [Set.Finite.mem_toFinset] at hP
    exact hP hPq
  obtain ⟨g, hgI, hgq⟩ := SetLike.not_le_iff_exists.mp hT
  refine ⟨g, hgq, fun P hP hPq ↦ ?_⟩
  have hmem : (⟨P, hP⟩ : PrimeSpectrum R) ∈ T := by
    rw [Set.Finite.mem_toFinset]
    exact hPq
  exact Finset.inf_le (f := fun P : PrimeSpectrum R ↦ P.asIdeal) hmem hgI

/-- If `g` lies in every prime not contained in `q`, then every `n ∉ q` divides a power of
`g`. -/
theorem exists_pow_eq_mul_of_forall_mem {q : Ideal R} {g : R}
    (hg : ∀ P : Ideal R, P.IsPrime → ¬ P ≤ q → g ∈ P) {n : R} (hn : n ∉ q) :
    ∃ (m : ℕ) (u : R), g ^ m = u * n := by
  have hrad : g ∈ (Ideal.span {n}).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro J ⟨hnJ, hJ⟩
    refine hg J hJ fun hJq ↦ hn (hJq ?_)
    exact hnJ (Ideal.mem_span_singleton_self n)
  obtain ⟨m, hm⟩ := hrad
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp hm
  exact ⟨m, u, hu.symm⟩

/-- **Temkin, Lemma 2.1.1 (ring form).** If `R` has finitely many prime ideals, then the
localization of `R` at a prime `q` is the localization at a single element `g ∉ q`. -/
theorem exists_isLocalization_away_of_isLocalization_atPrime [Finite (PrimeSpectrum R)]
    (q : Ideal R) [q.IsPrime] [IsLocalization.AtPrime S q] :
    ∃ g ∉ q, IsLocalization.Away g S := by
  obtain ⟨g, hgq, hg⟩ := exists_not_mem_forall_mem_of_finite q
  have hpow : ∀ m : ℕ, g ^ m ∉ q := fun m h ↦ hgq (Ideal.IsPrime.mem_of_pow_mem inferInstance m h)
  refine ⟨g, hgq, ?_⟩
  rw [IsLocalization.Away, isLocalization_iff]
  refine ⟨fun ⟨y, hy⟩ ↦ ?_, fun z ↦ ?_, fun {a b} h ↦ ?_⟩
  · obtain ⟨m, rfl⟩ := hy
    exact IsLocalization.map_units S (⟨g ^ m, hpow m⟩ : q.primeCompl)
  · obtain ⟨⟨r, n⟩, hrn⟩ := IsLocalization.surj q.primeCompl z
    obtain ⟨m, u, hmu⟩ := exists_pow_eq_mul_of_forall_mem hg n.2
    refine ⟨⟨r * u, ⟨g ^ m, m, rfl⟩⟩, ?_⟩
    change z * algebraMap R S (g ^ m) = algebraMap R S (r * u)
    rw [hmu, map_mul, map_mul, mul_comm (algebraMap R S u), ← mul_assoc, hrn]
  · obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq (M := q.primeCompl) h
    obtain ⟨m, u, hmu⟩ := exists_pow_eq_mul_of_forall_mem hg c.2
    refine ⟨⟨g ^ m, m, rfl⟩, ?_⟩
    change g ^ m * a = g ^ m * b
    rw [hmu, mul_assoc, mul_assoc, hc]

/-- **Temkin, Lemma 2.1.1 (ring form, quasi-finite version).** Let `C` be quasi-finite over a
ring `A` with finitely many primes (e.g. a valuation ring of finite height). Then every
localization of `C` at a prime is a localization at a single element. -/
theorem exists_isLocalization_away_of_quasiFinite (A : Type*) [CommRing A]
    [Algebra A R] [Finite (PrimeSpectrum A)] [Algebra.QuasiFinite A R]
    (q : Ideal R) [q.IsPrime] [IsLocalization.AtPrime S q] :
    ∃ g ∉ q, IsLocalization.Away g S := by
  have := Algebra.QuasiFinite.finite_primeSpectrum A R
  exact exists_isLocalization_away_of_isLocalization_atPrime q

end FiniteSpectrum

section StandardEtale

variable {k l : Type*} [Field k] [Field l] [Algebra k l] {B : ValuationSubring l}

/-- **Temkin, Lemma 2.1.6** (`semi-stable.tex` l. 2035–2043), the direction used: if `A = B ∩ k`
has finite height and `x` is a standard-unramified generator, then `B` is a standard étale
`A`-algebra. -/
theorem IsStdUnramifiedGenerator.isStandardEtale
    [Finite (PrimeSpectrum (B.comap (algebraMap k l)))] {x : l}
    (hx : IsStdUnramifiedGenerator k B x) :
    Algebra.IsStandardEtale (B.comap (algebraMap k l)) B := by
  let := hx.toValuationSubring.toRingHom.toAlgebra
  have hloc := hx.isLocalization
  obtain ⟨g, -, hg⟩ := exists_isLocalization_away_of_quasiFinite (B.comap (algebraMap k l))
    (S := B) ((maximalIdeal B).comap hx.toValuationSubring)
  have : IsScalarTower (B.comap (algebraMap k l)) hx.stdEtalePair.Ring B :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (hx.toValuationSubring.commutes a).symm
  exact Algebra.IsStandardEtale.of_isLocalizationAway g

/-- **Temkin, Lemma 2.1.6**: over a base of finite height, a standard-unramified extension gives a
standard étale extension of valuation rings. -/
theorem IsStdUnramified.isStandardEtale [Finite (PrimeSpectrum (B.comap (algebraMap k l)))]
    (h : IsStdUnramified k B) : Algebra.IsStandardEtale (B.comap (algebraMap k l)) B :=
  h.choose_spec.isStandardEtale

/-- **Temkin, Lemma 2.1.6**: over a base of finite height, a standard-unramified extension gives an
étale extension of valuation rings. -/
theorem IsStdUnramified.etale [Finite (PrimeSpectrum (B.comap (algebraMap k l)))]
    (h : IsStdUnramified k B) : Algebra.Etale (B.comap (algebraMap k l)) B :=
  have := h.isStandardEtale
  inferInstance

end StandardEtale

end DeJongAlterations.StableModification.Valuation
