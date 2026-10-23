/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.ValuationRing.ElementaryDivisors
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.Polynomial.SeparableDegree
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
# Algebra for Zariski's connectedness theorem over a valuation ring

Three algebraic inputs of the proof that the fibres of a flat projective scheme over a valuation
ring of finite height with connected generic fibre are connected (blueprint
`sm-cohomology-connected.tex`; it replaces Temkin's appeal to Zariski's connectedness theorem
"over a noetherian base" in the proof of Lemma 4.4.2, Temkin, *Stable modification of relative
curves*, J. Algebraic Geom. 19 (2010), `semi-stable.tex` lines 3125–3133).

* **Bounded torsion** (`exists_pow_smul_eq_zero_of_finitePresentation`, blueprint
  `lem:sm-conn-bounded-torsion`): let `W` be a valuation ring and `c ∈ W` nonzero such that every
  nonzero element of `W` divides a power of `c` (`W` has height at most one and `c` is a
  pseudo-uniformizer). Then the `c`-power torsion of a finitely presented `W`-module is killed by a
  single power `c ^ N`. The proof uses the elementary divisor form `M ≅ ∏ W ⧸ (aᵢ)` of finitely
  presented modules over a valuation ring (`ValuationRing.exists_basis_span_eq`).
* **Cocycles** (`exists_d_eq_pow_smul_of_finitePresentation_homology`): the same statement read on
  the first cohomology of a cochain complex: if `c ^ n • b` is a coboundary, so is `c ^ N • b`.
* **Integral elements** (`exists_pow_sub_isNilpotent_of_isIntegral`, blueprint
  `lem:sm-conn-integral-idempotent`): if `F` is a separably closed field and `S` an `F`-algebra
  without nontrivial idempotents, then every element `x ∈ S` integral over `F` satisfies
  `x ^ m - λ` nilpotent for some `m ≥ 1` and `λ ∈ F` (`m` a power of the exponential
  characteristic). The minimal polynomial of `x` is a power of one irreducible polynomial (a second
  coprime factor would give an idempotent, by the Chinese remainder theorem;
  `exists_irreducible_isNilpotent_aeval`), and irreducible polynomials over a separably closed
  field are `X ^ m - λ` up to a unit. Over an algebraically closed field `m = 1`
  (`exists_sub_isNilpotent_of_isIntegral`).
* **Two primes** (`dvd_pow_of_mem_maximalIdeal`, `exists_dvd_pow_of_ne_zero`): in a local ring whose
  only prime ideals are `⊥` and the maximal ideal, a nonzero element `c` of the maximal ideal
  divides a power of every element of the maximal ideal, and every nonzero element divides a power
  of `c`.
-/

universe u

open Polynomial

namespace DeJongAlterations.StableModification.Cohomology.Connected

section BoundedTorsion

variable {W : Type*} [CommRing W] [IsDomain W] [ValuationRing W]

/-- **Bounded torsion over a valuation ring of height one** (blueprint
`lem:sm-conn-bounded-torsion`): if every nonzero element of the valuation ring `W` divides a power
of `c ≠ 0`, the `c`-power torsion of a finitely presented `W`-module is killed by one power of
`c`. -/
theorem exists_pow_smul_eq_zero_of_finitePresentation {c : W} (hc0 : c ≠ 0)
    (hc : ∀ a : W, a ≠ 0 → ∃ n : ℕ, a ∣ c ^ n) (M : Type*) [AddCommGroup M] [Module W M]
    [Module.FinitePresentation W M] :
    ∃ N : ℕ, ∀ x : M, (∃ n : ℕ, c ^ n • x = 0) → c ^ N • x = 0 := by
  classical
  obtain ⟨n, K, e, hK⟩ := Module.FinitePresentation.exists_fin W M
  obtain ⟨b, a, hKa⟩ := ValuationRing.exists_basis_span_eq n (Pi.basisFun W (Fin n)) K hK
  let e' : M ≃ₗ[W] ((i : Fin n) → W ⧸ Ideal.span {a i}) :=
    e.trans ((Submodule.quotEquivOfEq _ _ hKa).trans (ValuationRing.quotientEquivPi b a))
  have hcomp : ∀ i, ∃ N : ℕ, ∀ y : W ⧸ Ideal.span {a i}, (∃ k : ℕ, c ^ k • y = 0) →
      c ^ N • y = 0 := by
    intro i
    by_cases hai : a i = 0
    · refine ⟨0, fun y ⟨k, hk⟩ => ?_⟩
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hai,
        Ideal.mem_span_singleton, zero_dvd_iff, smul_eq_mul] at hk
      have hz : z = 0 := (mul_eq_zero.mp hk).resolve_left (pow_ne_zero _ hc0)
      rw [hz, pow_zero, one_smul]
      rfl
    · obtain ⟨N, hN⟩ := hc (a i) hai
      refine ⟨N, fun y _ => ?_⟩
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton,
        smul_eq_mul]
      exact dvd_mul_of_dvd_left hN z
  choose N hN using hcomp
  refine ⟨Finset.univ.sup N, fun x ⟨k, hk⟩ => ?_⟩
  apply e'.injective
  rw [map_smul, map_zero]
  funext i
  have hki : c ^ k • e' x i = 0 := by
    have := congrFun (congrArg e' hk) i
    rwa [map_smul, map_zero] at this
  have hle : N i ≤ Finset.univ.sup N := Finset.le_sup (Finset.mem_univ i)
  change c ^ Finset.univ.sup N • e' x i = 0
  rw [← Nat.sub_add_cancel hle, pow_add, mul_smul, hN i _ ⟨k, hki⟩, smul_zero]

/-- **Bounded torsion of the first cohomology of a complex**: if `H¹(C)` is finitely presented
over the valuation ring `W` of height at most one, there is `N` such that a cocycle `b` with
`c ^ n • b` a coboundary for some `n` has `c ^ N • b` a coboundary. -/
theorem exists_d_eq_pow_smul_of_finitePresentation_homology {W : Type u} [CommRing W] [IsDomain W]
    [ValuationRing W] (C : CochainComplex (ModuleCat.{u} W) ℕ)
    [Module.FinitePresentation W (C.homology 1)] {c : W} (hc0 : c ≠ 0)
    (hc : ∀ a : W, a ≠ 0 → ∃ n : ℕ, a ∣ c ^ n) :
    ∃ N : ℕ, ∀ b : C.X 1, (C.d 1 2).hom b = 0 → ∀ (n : ℕ) (a : C.X 0),
      (C.d 0 1).hom a = c ^ n • b → ∃ t : C.X 0, (C.d 0 1).hom t = c ^ N • b := by
  let S := C.sc' 0 1 2
  let eH : C.homology 1 ≅ S.moduleCatLeftHomologyData.H :=
    C.homologyIsoSc' 0 1 2 (by simp) (by simp) ≪≫ S.moduleCatHomologyIso
  have hfp : Module.FinitePresentation W
      (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) :=
    Module.FinitePresentation.of_equiv eH.toLinearEquiv
  obtain ⟨N, hN⟩ := exists_pow_smul_eq_zero_of_finitePresentation hc0 hc
    (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles)
  refine ⟨N, fun b hb n a ha => ?_⟩
  have hb' : b ∈ LinearMap.ker S.g.hom := hb
  have h1 : c ^ n • (Submodule.Quotient.mk ⟨b, hb'⟩ :
      LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) = 0 := by
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨a, Subtype.ext ha⟩
  have h2 := hN _ ⟨n, h1⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h2
  obtain ⟨t, ht⟩ := h2
  exact ⟨t, congrArg Subtype.val ht⟩

end BoundedTorsion

section Integral

/-- If `S` is an algebra over a field `F` whose only idempotents are `0` and `1`, then every
`x ∈ S` integral over `F` is a root up to nilpotents of an irreducible polynomial over `F`: the
minimal polynomial of `x` is a power of one irreducible factor, since a second coprime factor would
give a nontrivial idempotent (Chinese remainder theorem). -/
theorem exists_irreducible_isNilpotent_aeval {F S : Type*} [Field F] [CommRing S] [Algebra F S]
    [Nontrivial S] (hS : ∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1) {x : S}
    (hx : IsIntegral F x) : ∃ r : F[X], Irreducible r ∧ IsNilpotent (aeval x r) := by
  classical
  set μ := minpoly F x with hμdef
  have hμ0 : μ ≠ 0 := minpoly.ne_zero hx
  have hμu : ¬IsUnit μ := minpoly.not_isUnit F x
  have hμx : aeval x μ = 0 := minpoly.aeval F x
  obtain ⟨r, hr, hrμ⟩ := WfDvdMonoid.exists_irreducible_factor hμu hμ0
  obtain ⟨k, s, hrs, hμ⟩ := WfDvdMonoid.max_power_factor hμ0 hr
  have hcop : IsCoprime (r ^ k) s := ((hr.coprime_iff_not_dvd).mpr hrs).pow_left
  obtain ⟨u, v, huv⟩ := hcop
  have hsum : aeval x (u * r ^ k) + aeval x (v * s) = 1 := by
    rw [← map_add, huv, map_one]
  have hprod : aeval x (u * r ^ k) * aeval x (v * s) = 0 := by
    rw [← map_mul, show u * r ^ k * (v * s) = u * v * (r ^ k * s) by ring, ← hμ, map_mul, hμx,
      mul_zero]
  have he : IsIdempotentElem (aeval x (u * r ^ k)) := by
    have h := hprod
    rw [eq_sub_of_add_eq' hsum] at h
    unfold IsIdempotentElem
    rw [mul_sub, mul_one, sub_eq_zero] at h
    exact h.symm
  -- the cofactor `s` is a unit
  have hsu : IsUnit s := by
    rcases hS _ he with h0 | h1
    · have hdvd : μ ∣ u * r ^ k := minpoly.dvd F x h0
      have hs : s ∣ u * r ^ k := (Dvd.intro_left _ hμ.symm).trans hdvd
      have hsu' : s ∣ u := by
        have hcop' : IsCoprime s (r ^ k) := (((hr.coprime_iff_not_dvd).mpr hrs).pow_left).symm
        exact hcop'.dvd_of_dvd_mul_right hs
      apply isUnit_of_dvd_one
      rw [← huv]
      exact dvd_add (dvd_mul_of_dvd_left hsu' _) (dvd_mul_left _ _)
    · exfalso
      have hvs : aeval x (v * s) = 0 := by
        rw [eq_sub_of_add_eq' hsum, h1, sub_self]
      have hdvd : μ ∣ v * s := minpoly.dvd F x hvs
      have hrk : r ^ k ∣ v * s := (Dvd.intro _ hμ.symm).trans hdvd
      have hrv : r ^ k ∣ v := (((hr.coprime_iff_not_dvd).mpr hrs).pow_left).dvd_of_dvd_mul_right hrk
      have hunit : IsUnit (r ^ k) := by
        apply isUnit_of_dvd_one
        rw [← huv]
        exact dvd_add (dvd_mul_left _ _) (dvd_mul_of_dvd_left hrv _)
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        rw [pow_zero, one_mul] at hμ
        exact hrs (hμ ▸ hrμ)
      · exact hr.not_isUnit (isUnit_of_dvd_unit (dvd_pow_self r hk.ne') hunit)
  refine ⟨r, hr, k, ?_⟩
  have h := hμx
  rw [hμ, map_mul, map_pow] at h
  exact (hsu.map (aeval x)).mul_left_eq_zero.mp h

/-- **Integral elements over a separably closed field** (blueprint
`lem:sm-conn-integral-idempotent`): if `S` is an algebra over a separably closed field `F` whose
only idempotents are `0` and `1`, then for every `x ∈ S` integral over `F` there are `m ≥ 1` and
`λ ∈ F` with `x ^ m - λ` nilpotent. -/
theorem exists_pow_sub_isNilpotent_of_isIntegral {F S : Type*} [Field F] [IsSepClosed F]
    [CommRing S] [Algebra F S] (hS : ∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1) {x : S}
    (hx : IsIntegral F x) :
    ∃ m : ℕ, 0 < m ∧ ∃ l : F, IsNilpotent (x ^ m - algebraMap F S l) := by
  classical
  rcases subsingleton_or_nontrivial S with hS0 | hS0
  · exact ⟨1, one_pos, 0, ⟨1, Subsingleton.elim _ _⟩⟩
  obtain ⟨r, hr, hrx⟩ := exists_irreducible_isNilpotent_aeval hS hx
  -- `r` is `C a * X ^ m + C b` with `a ≠ 0`
  obtain ⟨q, hq⟩ : ∃ q : ℕ, ExpChar F q := ⟨ringExpChar F, inferInstance⟩
  obtain ⟨g, hgsep, j, hgr⟩ := hr.hasSeparableContraction q
  have hq0 : q ≠ 0 := expChar_ne_zero F q
  have hgirr : Irreducible g := of_irreducible_expand (pow_ne_zero j hq0) (hgr ▸ hr)
  have hdeg : g.degree = 1 := IsSepClosed.degree_eq_one_of_irreducible F hgirr hgsep
  have hglc : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hgirr.ne_zero
  have hg := eq_X_add_C_of_degree_eq_one hdeg
  have hrform : aeval x r = algebraMap F S g.leadingCoeff * x ^ q ^ j +
      algebraMap F S (g.coeff 0) := by
    rw [← hgr]
    conv_lhs => rw [hg]
    simp [map_add, map_mul, expand_C, expand_X, aeval_C, aeval_X]
  refine ⟨q ^ j, pow_pos (Nat.pos_of_ne_zero hq0) j, -(g.coeff 0 / g.leadingCoeff), ?_⟩
  have heq : x ^ q ^ j - algebraMap F S (-(g.coeff 0 / g.leadingCoeff)) =
      algebraMap F S g.leadingCoeff⁻¹ * aeval x r := by
    rw [hrform, mul_add, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hglc, map_one, one_mul,
      ← map_mul, map_neg, sub_neg_eq_add, div_eq_inv_mul]
  rw [heq]
  obtain ⟨n, hn⟩ := hrx
  exact ⟨n, by rw [mul_pow, hn, mul_zero]⟩

/-- **Integral elements over an algebraically closed field**: if `S` is an algebra over an
algebraically closed field `F` whose only idempotents are `0` and `1`, every `x ∈ S` integral
over `F` is a constant up to a nilpotent. -/
theorem exists_sub_isNilpotent_of_isIntegral {F S : Type*} [Field F] [IsAlgClosed F]
    [CommRing S] [Algebra F S] (hS : ∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1) {x : S}
    (hx : IsIntegral F x) : ∃ l : F, IsNilpotent (x - algebraMap F S l) := by
  classical
  rcases subsingleton_or_nontrivial S with hS0 | hS0
  · exact ⟨0, ⟨1, Subsingleton.elim _ _⟩⟩
  obtain ⟨r, hr, hrx⟩ := exists_irreducible_isNilpotent_aeval hS hx
  have hdeg : r.degree = 1 := IsAlgClosed.degree_eq_one_of_irreducible F hr
  have hrlc : r.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hr.ne_zero
  have hrform : aeval x r = algebraMap F S r.leadingCoeff * x + algebraMap F S (r.coeff 0) := by
    conv_lhs => rw [eq_X_add_C_of_degree_eq_one hdeg]
    simp [map_add, map_mul, aeval_C, aeval_X]
  refine ⟨-(r.coeff 0 / r.leadingCoeff), ?_⟩
  have heq : x - algebraMap F S (-(r.coeff 0 / r.leadingCoeff)) =
      algebraMap F S r.leadingCoeff⁻¹ * aeval x r := by
    rw [hrform, mul_add, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hrlc, map_one, one_mul,
      ← map_mul, map_neg, sub_neg_eq_add, div_eq_inv_mul]
  rw [heq]
  obtain ⟨n, hn⟩ := hrx
  exact ⟨n, by rw [mul_pow, hn, mul_zero]⟩

end Integral

section TwoPrimes

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- In a local ring whose only primes are `⊥` and the maximal ideal, a nonzero element `c` of the
maximal ideal divides a power of every element of the maximal ideal. -/
theorem dvd_pow_of_mem_maximalIdeal
    (hR : ∀ P : Ideal R, P.IsPrime → P = ⊥ ∨ P = IsLocalRing.maximalIdeal R) {c : R} (hc0 : c ≠ 0)
    {a : R} (ha : a ∈ IsLocalRing.maximalIdeal R) : ∃ n : ℕ, c ∣ a ^ n := by
  have hrad : a ∈ (Ideal.span {c}).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨hcP, hP⟩
    rcases hR P hP with h | h
    · exact absurd (Ideal.mem_bot.mp (h ▸ hcP (Ideal.mem_span_singleton_self c))) hc0
    · exact h ▸ ha
  obtain ⟨n, hn⟩ := hrad
  exact ⟨n, Ideal.mem_span_singleton.mp hn⟩

/-- In a local ring whose only primes are `⊥` and the maximal ideal, every nonzero element divides a
power of each element `c` of the maximal ideal. -/
theorem exists_dvd_pow_of_ne_zero
    (hR : ∀ P : Ideal R, P.IsPrime → P = ⊥ ∨ P = IsLocalRing.maximalIdeal R) {c : R}
    (hc : c ∈ IsLocalRing.maximalIdeal R) {a : R} (ha0 : a ≠ 0) : ∃ n : ℕ, a ∣ c ^ n := by
  have hrad : c ∈ (Ideal.span {a}).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨haP, hP⟩
    rcases hR P hP with h | h
    · exact absurd (Ideal.mem_bot.mp (h ▸ haP (Ideal.mem_span_singleton_self a))) ha0
    · exact h ▸ hc
  obtain ⟨n, hn⟩ := hrad
  exact ⟨n, Ideal.mem_span_singleton.mp hn⟩

end TwoPrimes

end DeJongAlterations.StableModification.Cohomology.Connected
