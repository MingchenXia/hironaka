/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.CurvesField.DualityLattice
import DeJongAlterations.StableModification.CurvesField.DualityDifferent
import DeJongAlterations.StableModification.CurvesField.RiemannRochAlgebra

/-!
# Serre duality for a curve with a finite separable map to the projective line

Let `k` be an algebraically closed field and let `X` be a curve covered by two affine opens
`U = Spec A`, `V = Spec B` with `U ∩ V = Spec W`, where `A` is a finite `k[t]`-algebra, `B` a
finite `k[s]`-algebra, and `W = A[t⁻¹] = B[s⁻¹]` with `s t = 1` (the charts of a finite morphism
`X → ℙ¹_k`). Suppose `A`, `B` are integrally closed with torsion free differentials (`X` smooth)
and the function field `K` is separable over `k(t)`. The two-term Čech complexes
`A × B → W` (of `𝒪_X`) and `Ω¹_{A/k} × Ω¹_{B/k} → Ω¹_{W/k}` (of `Ω¹_X`) compute the
cohomology of `𝒪_X` and `Ω¹_X`. This file proves the numerical Serre duality
`h⁰(Ω¹_X) = h¹(𝒪_X)` and `h¹(Ω¹_X) = h⁰(𝒪_X)`
(`finrank_H0_kaehler`, `finrank_H1_kaehler`), hence `χ(Ω¹_X) = -χ(𝒪_X)` (`euler_kaehler`),
`deg Ω¹_X = χ(Ω¹_X) - χ(𝒪_X) = 2 g - 2` for `g = 1 - χ(𝒪_X)` (`deg_kaehler`), and
`h⁰(Ω¹_X) = g` when `h⁰(𝒪_X) = 1` (`finrank_H0_kaehler_eq_genus`). All four spaces are
finite-dimensional (`finiteDimensional_H0_kaehler`, ...). The hypotheses are met by `ℙ¹` itself
(`DualityP1`).

The proof combines the duality of vector bundles on `ℙ¹` in coordinates (`DualityLattice`)
with Dedekind's theorem `Ω¹_{A/k} = A^∨ dt` (`DualityDifferent`): in the coordinates of a
`k[t]`-basis `(eᵢ)` of `A`, `A` and `B` give the lattices `k[t]ⁿ` and `N` of the bundle
`f_* 𝒪_X` on `ℙ¹`, and, in the coordinates of the trace-dual basis, `Ω¹_A` and `Ω¹_B` give
`k[t]ⁿ` and the Serre dual lattice `N'` (`f_* Ω¹_X ≅ (f_* 𝒪_X)^∨ ⊗ Ω¹_{ℙ¹}`). Dedekind's theorem is
applied twice: to `A` over `k[t]`, and to `B` over `k[s]` through the type synonyms `Flip L`,
`Flip K`, which carry the `k[s]`-algebra structures `s ↦ t⁻¹` (`mem_range_kaehler_B_iff`).

## Main definitions

* `Duality.resO`, `Duality.resΩ`: the restriction maps of the two-chart complexes.
* `Duality.coordW`, `Duality.coordΩ`: coordinates `W ≅ k[t, t⁻¹]ⁿ`, `Ω¹_W ≅ k[t, t⁻¹]ⁿ`.
* `Duality.latticeB`: the lattice of `B` in these coordinates.

## Main results

* `Duality.map_coordW_A`, `Duality.map_coordΩ_A`, `Duality.map_coordΩ_B`,
  `Duality.isLattice_latticeB`.
* `Duality.finrank_H0_kaehler`, `Duality.finrank_H1_kaehler`, `Duality.euler_kaehler`,
  `Duality.deg_kaehler`, `Duality.finrank_H0_kaehler_eq_genus`.

This is the duality input for the degree of the dualizing sheaf on the components of a
semistable curve (M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19
(2010), Thm 1.1, `references/temkin10-stable-modification/source/semi-stable.tex`,
lines 1717–1741). Blueprint: `sm-omega-degree.tex`, `thm:sm-serre-duality-finite`.
-/

universe u

open Polynomial LaurentPolynomial Module

set_option linter.unusedSectionVars false

namespace DeJongAlterations.StableModification.CurvesField.Duality

noncomputable section

/-! ### Two-term complexes with injective restrictions -/

section TwoTerm

variable {k : Type*} [Field k] {MU MV MW : Type*} [AddCommGroup MU] [Module k MU]
  [AddCommGroup MV] [Module k MV] [AddCommGroup MW] [Module k MW]
  (ρU : MU →ₗ[k] MW) (ρV : MV →ₗ[k] MW)

lemma range_twistDiff_id :
    LinearMap.range (twistDiff ρU ρV LinearMap.id) =
      LinearMap.range ρU ⊔ LinearMap.range ρV := by
  apply le_antisymm
  · rintro _ ⟨⟨a, b⟩, rfl⟩
    rw [twistDiff_apply, LinearMap.id_apply]
    exact Submodule.sub_mem _ (Submodule.mem_sup_right ⟨b, rfl⟩)
      (Submodule.mem_sup_left ⟨a, rfl⟩)
  · rw [sup_le_iff]
    constructor
    · rintro _ ⟨a, rfl⟩
      exact ⟨(-a, 0), by simp⟩
    · rintro _ ⟨b, rfl⟩
      exact ⟨(0, b), by simp⟩

/-- `H¹` of a two-term complex is `MW ⧸ (im ρU + im ρV)`. -/
def H1EquivQuot :
    H1 ρU ρV LinearMap.id ≃ₗ[k] MW ⧸ (LinearMap.range ρU ⊔ LinearMap.range ρV) :=
  Submodule.quotEquivOfEq _ _ (range_twistDiff_id ρU ρV)

variable {ρU ρV}

lemma mem_H0_iff {p : MU × MV} : p ∈ H0 ρU ρV LinearMap.id ↔ ρV p.2 = ρU p.1 := by
  rw [LinearMap.mem_ker, twistDiff_apply, LinearMap.id_apply, sub_eq_zero]

/-- `H⁰` of a two-term complex with injective restrictions is `im ρU ∩ im ρV`. -/
def H0EquivInf (hU : Function.Injective ρU) (hV : Function.Injective ρV) :
    H0 ρU ρV LinearMap.id ≃ₗ[k]
      (LinearMap.range ρU ⊓ LinearMap.range ρV : Submodule k MW) :=
  LinearEquiv.ofBijective
    ((ρU ∘ₗ LinearMap.fst k MU MV ∘ₗ (H0 ρU ρV LinearMap.id).subtype).codRestrict _
      (fun p => Submodule.mem_inf.mpr ⟨LinearMap.mem_range.mpr ⟨p.1.1, rfl⟩,
        LinearMap.mem_range.mpr ⟨p.1.2, (mem_H0_iff.mp p.2)⟩⟩))
    ⟨fun p q h => by
      have h1 : ρU p.1.1 = ρU q.1.1 := congrArg Subtype.val h
      have hp := mem_H0_iff.mp p.2
      have hq := mem_H0_iff.mp q.2
      apply Subtype.ext
      apply Prod.ext
      · exact hU h1
      · exact hV (by rw [hp, hq, h1]),
     fun z => by
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := z.2
      refine ⟨⟨(a, b), mem_H0_iff.mpr (by rw [ha, hb])⟩, Subtype.ext ha⟩⟩

end TwoTerm

/-! ### Transport along a linear equivalence -/

section Transport

variable {k : Type*} [Field k] {M V : Type*} [AddCommGroup M] [Module k M] [AddCommGroup V]
  [Module k V] (e : M ≃ₗ[k] V) (S T : Submodule k M)

lemma finrank_inf_map :
    finrank k (S ⊓ T : Submodule k M) =
      finrank k (S.map (e : M →ₗ[k] V) ⊓ T.map (e : M →ₗ[k] V) : Submodule k V) := by
  rw [← Submodule.map_inf _ e.injective, LinearEquiv.finrank_map_eq]

/-- The quotients `M ⧸ (S + T)` and `V ⧸ (e S + e T)` are isomorphic. -/
def quotSupEquiv : (M ⧸ (S ⊔ T)) ≃ₗ[k]
    V ⧸ (S.map (e : M →ₗ[k] V) ⊔ T.map (e : M →ₗ[k] V)) :=
  Submodule.Quotient.equiv _ _ e (by rw [Submodule.map_sup])

lemma finiteDimensional_inf_of_map
    (h : FiniteDimensional k (S.map (e : M →ₗ[k] V) ⊓ T.map (e : M →ₗ[k] V) : Submodule k V)) :
    FiniteDimensional k (S ⊓ T : Submodule k M) := by
  rw [← Submodule.map_inf _ e.injective] at h
  exact Module.Finite.equiv (e.submoduleMap (S ⊓ T)).symm

lemma finiteDimensional_quot_of_map
    (h : FiniteDimensional k (V ⧸ (S.map (e : M →ₗ[k] V) ⊔ T.map (e : M →ₗ[k] V)))) :
    FiniteDimensional k (M ⧸ (S ⊔ T)) :=
  Module.Finite.equiv (quotSupEquiv e S T).symm

end Transport

/-! ### Laurent polynomials inside `k(t)` -/

section Laurent

variable {k : Type u} [Field k]

lemma coeff_toLaurent_of_neg (p : k[X]) {c : ℤ} (hc : c < 0) : (toLaurent p).coeff c = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, coeff_add, hp, hq, add_zero]
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.toLaurent_C_mul_X_pow,
      ← LaurentPolynomial.smul_eq_C_mul, coeff_smul, T, coeff_single, if_neg (by omega),
      mul_zero]

/-- `f ∈ k[t]` iff `f` has no coefficients in negative degrees. -/
lemma mem_range_toLaurent_iff (f : k[T;T⁻¹]) :
    f ∈ Set.range (toLaurent (R := k)) ↔ ∀ c : ℤ, c < 0 → f.coeff c = 0 := by
  constructor
  · rintro ⟨p, rfl⟩ c hc
    exact coeff_toLaurent_of_neg p hc
  · intro h
    rw [eq_sum_single f f.coeff.support (fun j hj => Finsupp.notMem_support_iff.mp hj)]
    refine ⟨∑ j ∈ f.coeff.support, Polynomial.monomial j.toNat (f.coeff j), ?_⟩
    rw [map_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj0 : 0 ≤ j := by
      by_contra hneg
      exact (Finsupp.mem_support_iff.mp hj) (h j (by omega))
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.toLaurent_C_mul_X_pow,
      Int.toNat_of_nonneg hj0, single_eq_C_mul_T', LaurentPolynomial.smul_eq_C_mul]

/-- `f ∈ k[s] = k[t⁻¹]` iff `f` has no coefficients in positive degrees. -/
lemma mem_range_invert_toLaurent_iff (f : k[T;T⁻¹]) :
    f ∈ Set.range (fun p : k[X] => invert (toLaurent p)) ↔
      ∀ c : ℤ, 0 < c → f.coeff c = 0 := by
  constructor
  · rintro ⟨p, rfl⟩ c hc
    rw [invert_apply]
    exact coeff_toLaurent_of_neg p (by omega)
  · intro h
    obtain ⟨p, hp⟩ := (mem_range_toLaurent_iff (invert f)).mpr (fun c hc => by
      rw [invert_apply]; exact h _ (by omega))
    refine ⟨p, ?_⟩
    change invert (toLaurent p) = f
    rw [hp]
    exact involutive_invert f

variable (L : Type*) [Field L] [Algebra k[X] L] [IsFractionRing k[X] L]

lemma algebraMap_X_ne_zero : algebraMap k[X] L X ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective k[X] L)).mpr (Polynomial.X_ne_zero (R := k))

/-- The embedding `k[t, t⁻¹] → k(t)`. -/
def laurentToField : k[T;T⁻¹] →+* L :=
  @IsLocalization.lift k[X] _ (Submonoid.powers X) k[T;T⁻¹] _ _ L _ LaurentPolynomial.isLocalization
    (algebraMap k[X] L) (fun y => by
      obtain ⟨n, hn⟩ := y.2
      rw [← hn, map_pow]
      exact (IsUnit.mk0 _ (algebraMap_X_ne_zero L)).pow n)

lemma laurentToField_toLaurent (p : k[X]) :
    laurentToField L (toLaurent p) = algebraMap k[X] L p := by
  rw [← algebraMap_eq_toLaurent]
  exact IsLocalization.lift_eq _ p

lemma laurentToField_T (n : ℤ) :
    laurentToField L (T n : k[T;T⁻¹]) = (algebraMap k[X] L X) ^ n := by
  have hpos : ∀ m : ℕ, laurentToField L (T (m : ℤ) : k[T;T⁻¹]) = (algebraMap k[X] L X) ^ m := by
    intro m
    rw [← Polynomial.toLaurent_X_pow, laurentToField_toLaurent, map_pow]
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [hpos, zpow_natCast]
  · have h1 : laurentToField L (T (-(m : ℤ)) : k[T;T⁻¹]) *
        laurentToField L (T (m : ℤ) : k[T;T⁻¹]) = 1 := by
      rw [← map_mul, ← T_add, neg_add_cancel, T_zero, map_one]
    rw [hpos] at h1
    rw [zpow_neg, zpow_natCast]
    exact eq_inv_of_mul_eq_one_left h1

lemma laurentToField_injective : Function.Injective (laurentToField L (k := k)) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  obtain ⟨n, p, hp⟩ := exists_T_pow f
  have : laurentToField L (toLaurent p) = 0 := by rw [hp, map_mul, hf, zero_mul]
  rw [laurentToField_toLaurent, map_eq_zero_iff _ (IsFractionRing.injective k[X] L)] at this
  rw [this, map_zero] at hp
  have h2 : f = f * T n * T (-(n : ℤ)) := by rw [mul_assoc, ← T_add, add_neg_cancel, T_zero,
    mul_one]
  rw [h2, ← hp, zero_mul]

variable [Algebra k L] [IsScalarTower k k[X] L]

lemma laurentToField_C (r : k) : laurentToField L (C r : k[T;T⁻¹]) = algebraMap k L r := by
  rw [← Polynomial.toLaurent_C, laurentToField_toLaurent,
    show Polynomial.C r = algebraMap k k[X] r from rfl, ← IsScalarTower.algebraMap_apply]

lemma laurentToField_invert_toLaurent (p : k[X]) :
    laurentToField L (invert (toLaurent p)) = aeval (algebraMap k[X] L X)⁻¹ p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq, map_add]
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.toLaurent_C_mul_X_pow, map_mul,
      invert_C, invert_T, map_mul, laurentToField_T, laurentToField_C, map_mul, aeval_C,
      map_pow, aeval_X, zpow_neg, zpow_natCast, inv_pow]

/-- `f ∈ k[t, t⁻¹]` lies in `k[s] = k[t⁻¹]` inside `k(t)` iff it has no coefficients in positive
degrees. -/
lemma laurentToField_mem_range_aeval_iff (f : k[T;T⁻¹]) :
    laurentToField L f ∈ Set.range (aeval (R := k) (algebraMap k[X] L X)⁻¹) ↔
      ∀ c : ℤ, 0 < c → f.coeff c = 0 := by
  rw [← mem_range_invert_toLaurent_iff]
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p, laurentToField_injective L ?_⟩
    rw [laurentToField_invert_toLaurent, hp]
  · rintro ⟨p, rfl⟩
    exact ⟨p, (laurentToField_invert_toLaurent L p).symm⟩

/-- `p(t⁻¹) tᴺ = (reflect N p)(t)` for `deg p ≤ N`. -/
lemma aeval_inv_mul_pow (N : ℕ) (p : k[X]) (hp : p.natDegree ≤ N) :
    aeval (R := k) (algebraMap k[X] L X)⁻¹ p * algebraMap k[X] L X ^ N =
      algebraMap k[X] L (reflect N p) := by
  have hu := algebraMap_X_ne_zero L (k := k)
  let : Invertible (algebraMap k[X] L X) := invertibleOfNonzero hu
  have h := eval₂_reflect_mul_pow (algebraMap k L) (algebraMap k[X] L X) N (reflect N p)
    (natDegree_reflect_le.trans (max_le le_rfl hp))
  rw [reflect_reflect, invOf_eq_inv] at h
  rw [aeval_def, h, ← aeval_def, aeval_algebraMap_apply, aeval_X_left_apply]

/-- `(reflect N p)(t⁻¹) tᴺ = p(t)` for `deg p ≤ N`. -/
lemma aeval_inv_reflect_mul_pow (N : ℕ) (p : k[X]) (hp : p.natDegree ≤ N) :
    aeval (R := k) (algebraMap k[X] L X)⁻¹ (reflect N p) * algebraMap k[X] L X ^ N =
      algebraMap k[X] L p := by
  rw [aeval_inv_mul_pow L N _ (natDegree_reflect_le.trans (max_le le_rfl hp)), reflect_reflect]

/-- `k(t)` is also a fraction field of `k[s]` via `s ↦ t⁻¹`: a `k[X]`-algebra `L'` which is
isomorphic to `L` compatibly with `p ↦ p(t⁻¹)` is a fraction field of `k[X]`. -/
lemma isFractionRing_of_aeval_inv (L' : Type*) [Field L'] [Algebra k[X] L'] (e : L' ≃+* L)
    (he : ∀ p : k[X], e (algebraMap k[X] L' p) = aeval (R := k) (algebraMap k[X] L X)⁻¹ p) :
    IsFractionRing k[X] L' := by
  have hu := algebraMap_X_ne_zero L (k := k)
  have hinj : Function.Injective (aeval (R := k) (algebraMap k[X] L X)⁻¹) := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    have h := aeval_inv_mul_pow L p.natDegree p le_rfl
    rw [hp, zero_mul, eq_comm, map_eq_zero_iff _ (IsFractionRing.injective k[X] L),
      reflect_eq_zero_iff] at h
    exact h
  have hinj' : Function.Injective (algebraMap k[X] L') := by
    intro p q hpq
    apply hinj
    rw [← he, ← he, hpq]
  have : FaithfulSMul k[X] L' := (faithfulSMul_iff_algebraMap_injective k[X] L').mpr hinj'
  refine IsFractionRing.of_field k[X] L' fun z => ?_
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := k[X]) (e z)
  set N := max a.natDegree b.natDegree
  refine ⟨reflect N a, reflect N b, e.injective ?_⟩
  rw [map_div₀, he, he, ← hab, ← aeval_inv_reflect_mul_pow L N a (le_max_left _ _),
    ← aeval_inv_reflect_mul_pow L N b (le_max_right _ _),
    mul_div_mul_right _ _ (pow_ne_zero N hu)]

/-- `k[t, t⁻¹] → k(t)` as a `k`-linear map. -/
def laurentToFieldₗ : k[T;T⁻¹] →ₗ[k] L where
  toFun := laurentToField L
  map_add' := map_add _
  map_smul' r f := by
    rw [LaurentPolynomial.smul_eq_C_mul, map_mul, laurentToField_C, RingHom.id_apply,
      Algebra.smul_def]

lemma laurentToFieldₗ_apply (f : k[T;T⁻¹]) : laurentToFieldₗ L f = laurentToField L f := rfl

end Laurent

/-! ### Coordinates with values in `k[t, t⁻¹]` -/

section CoordEquiv

variable {k : Type u} [Field k] {L K : Type*} [Field L] [Field K] [Algebra k[X] L]
  [IsFractionRing k[X] L] [Algebra k L] [IsScalarTower k k[X] L] [Algebra L K] [Algebra k K]
  [IsScalarTower k L K] {n : ℕ} {M : Type*} [AddCommGroup M] [Module k M]
  (b : Basis (Fin n) L K) (f : M →ₗ[k] K) (hf : Function.Injective f)
  (hrange : ∀ y : K, y ∈ LinearMap.range f ↔
    ∀ i, b.repr y i ∈ Set.range (laurentToField L (k := k)))

variable (L) in
/-- `k[t, t⁻¹] ≅ j(k[t, t⁻¹]) ⊆ k(t)`. -/
def laurentRangeEquiv : k[T;T⁻¹] ≃ₗ[k] LinearMap.range (laurentToFieldₗ L (k := k)) :=
  LinearEquiv.ofInjective _ (laurentToField_injective L)

variable (L) in
lemma laurentRangeEquiv_symm_apply (y : LinearMap.range (laurentToFieldₗ L (k := k))) :
    laurentToField L ((laurentRangeEquiv L).symm y) = y := by
  have := (laurentRangeEquiv L (k := k)).apply_symm_apply y
  exact congrArg Subtype.val this

omit [IsScalarTower k L K] in
include hrange in
lemma coord_mem_range (m : M) (i : Fin n) :
    b.repr (f m) i ∈ LinearMap.range (laurentToFieldₗ L (k := k)) := by
  obtain ⟨r, hr⟩ := (hrange (f m)).mp ⟨m, rfl⟩ i
  exact ⟨r, hr⟩

/-- The coordinates of `f m` in the basis `b`, read in `k[t, t⁻¹]`. -/
def coordMap : M →ₗ[k] Vec k n :=
  LinearMap.pi fun i => (laurentRangeEquiv L).symm.toLinearMap ∘ₗ
    ((LinearMap.proj i ∘ₗ (b.equivFun.toLinearMap.restrictScalars k) ∘ₗ f).codRestrict _
      (fun m => by
        have := coord_mem_range b f hrange m i
        rwa [← Basis.equivFun_apply] at this))

lemma laurentToField_coordMap (m : M) (i : Fin n) :
    laurentToField L (coordMap b f hrange m i) = b.repr (f m) i := by
  change laurentToField L ((laurentRangeEquiv L).symm _) = _
  rw [laurentRangeEquiv_symm_apply]
  rfl

include hf in
lemma coordMap_bijective : Function.Bijective (coordMap b f hrange) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro m hm
    apply hf
    rw [map_zero]
    apply b.repr.injective
    ext i
    have := laurentToField_coordMap b f hrange m i
    rw [hm, Pi.zero_apply, map_zero] at this
    rw [← this, map_zero, Finsupp.zero_apply]
  · intro v
    set y : K := b.equivFun.symm (fun i => laurentToField L (v i))
    have hy : ∀ i, b.repr y i = laurentToField L (v i) := fun i => by
      rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    obtain ⟨m, hm⟩ := (hrange y).mpr (fun i => ⟨v i, (hy i).symm⟩)
    refine ⟨m, funext fun i => laurentToField_injective L ?_⟩
    rw [laurentToField_coordMap, hm, hy]

/-- The coordinate isomorphism `M ≅ k[t, t⁻¹]ⁿ`. -/
def coordEquiv : M ≃ₗ[k] Vec k n :=
  LinearEquiv.ofBijective (coordMap b f hrange) (coordMap_bijective b f hf hrange)

lemma laurentToField_coordEquiv (m : M) (i : Fin n) :
    laurentToField L (coordEquiv b f hf hrange m i) = b.repr (f m) i :=
  laurentToField_coordMap b f hrange m i

end CoordEquiv

/-! ### Fraction fields of localizations -/

/-- If `S = R[x⁻¹]` for a nonzero `x` of the domain `R`, a fraction field of `S` is one of
`R`. -/
theorem isFractionRing_of_away {R S T : Type*} [CommRing R] [IsDomain R] [CommRing S] [Field T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T] {x : R} (hx : x ≠ 0)
    [IsLocalization.Away x S] [IsFractionRing S T] : IsFractionRing R T := by
  have hRS : Function.Injective (algebraMap R S) :=
    IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors hx)
  have hST : Function.Injective (algebraMap S T) := IsFractionRing.injective S T
  have hinj : Function.Injective (algebraMap R T) := by
    rw [IsScalarTower.algebraMap_eq R S T]; exact hST.comp hRS
  have hxu : IsUnit (algebraMap R S x) := IsLocalization.Away.algebraMap_isUnit x
  have : Nontrivial S := hRS.nontrivial
  refine ⟨fun y => ?_, fun z => ?_, fun {a b} h => ⟨1, by rw [hinj h]⟩⟩
  · exact IsUnit.mk0 _ ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero y.2))
  · obtain ⟨⟨s₁, s₂⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors S) z
    obtain ⟨m₁, r₁, hr₁⟩ := IsLocalization.Away.surj x s₁
    obtain ⟨m₂, r₂, hr₂⟩ := IsLocalization.Away.surj x (s₂ : S)
    have hr₂0 : r₂ ≠ 0 := by
      rintro rfl
      rw [map_zero] at hr₂
      exact nonZeroDivisors.ne_zero s₂.2 ((hxu.pow m₂).mul_left_eq_zero.mp hr₂)
    refine ⟨⟨r₁ * x ^ m₂, ⟨r₂ * x ^ m₁, mem_nonZeroDivisors_of_ne_zero
      (mul_ne_zero hr₂0 (pow_ne_zero _ hx))⟩⟩, ?_⟩
    simp only [IsScalarTower.algebraMap_apply R S T, map_mul, map_pow, ← hr₁, ← hr₂]
    rw [← hs]
    ring

/-! ### The restriction maps of the two-chart complexes -/

section Res

variable (k : Type u) [Field k] (A W : Type u) [CommRing A] [CommRing W] [Algebra k A]
  [Algebra k W] [Algebra A W] [IsScalarTower k A W]

/-- The restriction `𝒪(U) = A → W = 𝒪(U ∩ V)` as a `k`-linear map. -/
abbrev resO : A →ₗ[k] W := (IsScalarTower.toAlgHom k A W).toLinearMap

/-- The restriction `Ω¹(U) = Ω¹_{A/k} → Ω¹_{W/k} = Ω¹(U ∩ V)` as a `k`-linear map. -/
abbrev resΩ : Ω[A⁄k] →ₗ[k] Ω[W⁄k] := (KaehlerDifferential.map k k A W).restrictScalars k

end Res

/-! ### A type synonym for the chart at infinity -/

/-- A type synonym, used to equip `k(t)` and `K` with the `k[s]`-algebra structures of the chart
at infinity (`s ↦ t⁻¹`) without clashing with their `k[t]`-algebra structures. -/
def Flip (α : Type*) : Type _ := α

instance {α : Type*} [h : Field α] : Field (Flip α) := h

/-! ### The curve -/

section Curve

variable {k : Type u} [Field k]
  {A B W : Type u} [CommRing A] [CommRing B] [CommRing W] [IsDomain A] [IsDomain B]
  [Algebra k A] [Algebra k B] [Algebra k W] [Algebra A W] [Algebra B W]
  [IsScalarTower k A W] [IsScalarTower k B W]
  [Algebra k[X] A] [IsScalarTower k k[X] A] [Algebra k[X] B] [IsScalarTower k k[X] B]
  [Module.Finite k[X] A] [Module.Finite k[X] B] [Module.IsTorsionFree k[X] A]
  [Module.IsTorsionFree k[X] B]
  [IsLocalization.Away (algebraMap k[X] A X) W] [IsLocalization.Away (algebraMap k[X] B X) W]
  {L K : Type u} [Field L] [Field K] [Algebra k[X] L] [IsFractionRing k[X] L] [Algebra k L]
  [IsScalarTower k k[X] L] [Algebra W K] [IsFractionRing W K] [Algebra A K] [IsScalarTower A W K]
  [Algebra B K] [IsScalarTower B W K] [Algebra L K] [Algebra k[X] K] [IsScalarTower k[X] L K]
  [IsScalarTower k[X] A K] [Algebra k K] [IsScalarTower k W K] [IsScalarTower k L K]
  [IsScalarTower k k[X] K] [IsScalarTower k A K] [IsScalarTower k B K]
  [FiniteDimensional L K] [Algebra.IsSeparable L K]

variable (A) in
lemma algebraMap_X_ne_zero' : algebraMap k[X] A X ≠ 0 := by
  intro h
  have : (X : k[X]) • (1 : A) = 0 := by rw [Algebra.smul_def, h, zero_mul]
  rcases smul_eq_zero.mp this with h' | h'
  · exact X_ne_zero h'
  · exact one_ne_zero h'

variable (A W) in
include k in
lemma algebraMap_injective_away : Function.Injective (algebraMap A W) :=
  IsLocalization.injective W (powers_le_nonZeroDivisors_of_noZeroDivisors
    (algebraMap_X_ne_zero' (k := k) A))

include k W in
lemma isFractionRing_A : IsFractionRing A K :=
  isFractionRing_of_away (S := W) (algebraMap_X_ne_zero' (k := k) A)

include k W in
lemma isFractionRing_B : IsFractionRing B K :=
  isFractionRing_of_away (S := W) (algebraMap_X_ne_zero' (k := k) B)

lemma algebraMap_W_A (a : A) : algebraMap W K (algebraMap A W a) = algebraMap A K a :=
  (IsScalarTower.algebraMap_apply A W K a).symm

lemma algebraMap_W_B (b : B) : algebraMap W K (algebraMap B W b) = algebraMap B K b :=
  (IsScalarTower.algebraMap_apply B W K b).symm

lemma algebraMap_tA : algebraMap A K (algebraMap k[X] A X) = algebraMap k[X] K X :=
  (IsScalarTower.algebraMap_apply k[X] A K X).symm

lemma algebraMap_tL : algebraMap L K (algebraMap k[X] L X) = algebraMap k[X] K X :=
  (IsScalarTower.algebraMap_apply k[X] L K X).symm

variable (hts : algebraMap A W (algebraMap k[X] A X) * algebraMap B W (algebraMap k[X] B X) = 1)

include hts in
lemma algebraMap_sB : algebraMap B K (algebraMap k[X] B X) = (algebraMap k[X] K X)⁻¹ := by
  have h := congrArg (algebraMap W K) hts
  rw [map_mul, map_one, ← IsScalarTower.algebraMap_apply A W K,
    ← IsScalarTower.algebraMap_apply B W K, ← IsScalarTower.algebraMap_apply k[X] A K] at h
  exact eq_inv_of_mul_eq_one_right h

include A W in
lemma tK_ne_zero : algebraMap k[X] K X ≠ 0 := by
  rw [← algebraMap_tA (A := A)]
  have := isFractionRing_A (k := k) (W := W) (A := A) (K := K)
  exact (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr (algebraMap_X_ne_zero' A)

/-! #### A basis of `A` over `k[t]` and the trace-dual basis -/

/-- A finite torsion free `k[t]`-module is free (`k[t]` is a PID). -/
local instance free_A : Module.Free k[X] A := Module.free_of_finite_type_torsion_free'

variable (k A) in
/-- A `k[t]`-basis of `A`. -/
def eA : Basis (Fin (finrank k[X] A)) k[X] A := Module.finBasis k[X] A

include W L in
lemma isLocalization_K [IsIntegrallyClosed A] :
    IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors k[X])) K := by
  have := isFractionRing_A (k := k) (W := W) (A := A) (K := K)
  have : Algebra.IsIntegral k[X] A := Algebra.IsIntegral.of_finite k[X] A
  have : IsIntegralClosure A k[X] K := IsIntegralClosure.of_isIntegrallyClosed A k[X] K
  exact IsIntegralClosure.isLocalization k[X] L K A

variable (k A W L K) in
/-- The `k(t)`-basis of `K` given by `eA`. -/
def eK [IsIntegrallyClosed A] : Basis (Fin (finrank k[X] A)) L K :=
  have := isLocalization_K (k := k) (A := A) (W := W) (L := L) (K := K)
  (eA k A).localizationLocalization L (nonZeroDivisors k[X]) K

variable (k A W L) in
lemma eK_apply [IsIntegrallyClosed A] (i : Fin (finrank k[X] A)) :
    eK k A W L K i = algebraMap A K (eA k A i) := by
  have := isLocalization_K (k := k) (A := A) (W := W) (L := L) (K := K)
  exact Basis.localizationLocalization_apply _ _ _ _ _

variable (k A W L) in
lemma eK_repr_algebraMap [IsIntegrallyClosed A] (a : A) (i : Fin (finrank k[X] A)) :
    (eK k A W L K).repr (algebraMap A K a) i = algebraMap k[X] L ((eA k A).repr a i) := by
  have := isLocalization_K (k := k) (A := A) (W := W) (L := L) (K := K)
  exact Basis.localizationLocalization_repr_algebraMap _ _ _ _ _ _

variable (k A W L) in
/-- Elements of `K` whose `eK`-coordinates lie in `k[t]` lie in `A`. -/
lemma mem_range_A_of_repr [IsIntegrallyClosed A] (y : K)
    (h : ∀ i, (eK k A W L K).repr y i ∈ Set.range (algebraMap k[X] L)) :
    ∃ a : A, algebraMap A K a = y := by
  choose q hq using h
  refine ⟨∑ i, q i • eA k A i, ?_⟩
  conv_rhs => rw [← (eK k A W L K).sum_repr y]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hq, eK_apply k A W L, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply k[X] L K, Algebra.smul_def]

variable (k A W L) in
lemma repr_mul_pow (y : K) (m : ℕ) (i : Fin (finrank k[X] A)) [IsIntegrallyClosed A] :
    (eK k A W L K).repr (y * algebraMap k[X] K X ^ m) i =
      algebraMap k[X] L X ^ m * (eK k A W L K).repr y i := by
  rw [← algebraMap_tL (L := L), ← map_pow, mul_comm, ← Algebra.smul_def, LinearEquiv.map_smul,
    Finsupp.smul_apply, smul_eq_mul]

/-! #### Coordinates of `W` -/

include k in
omit [Algebra k L] [IsScalarTower k k[X] L] in
/-- Finitely many elements of `j(k[t, t⁻¹])` have a common denominator `tᵐ`. -/
lemma exists_pow_mul_mem {ι : Type*} [Fintype ι] (c : ι → L)
    (hc : ∀ i, c i ∈ Set.range (laurentToField L (k := k))) :
    ∃ m : ℕ, ∀ i, algebraMap k[X] L X ^ m * c i ∈ Set.range (algebraMap k[X] L) := by
  choose r hr using hc
  choose n p hp using fun i => exists_T_pow (r i)
  refine ⟨Finset.univ.sup n, fun i => ?_⟩
  have hle : n i ≤ Finset.univ.sup n := Finset.le_sup (Finset.mem_univ i)
  refine ⟨X ^ (Finset.univ.sup n - n i) * p i, ?_⟩
  rw [map_mul, map_pow, ← laurentToField_toLaurent L (p i), hp, map_mul, laurentToField_T, hr,
    zpow_natCast]
  conv_rhs => rw [← Nat.sub_add_cancel hle, pow_add]
  ring

omit [Algebra k L] [IsScalarTower k k[X] L] in
lemma mem_range_laurentToField_of_pow_mul (z : L) (m : ℕ)
    (h : algebraMap k[X] L X ^ m * z ∈ Set.range (algebraMap k[X] L)) :
    z ∈ Set.range (laurentToField L (k := k)) := by
  obtain ⟨p, hp⟩ := h
  refine ⟨T (-(m : ℤ)) * toLaurent p, ?_⟩
  rw [map_mul, laurentToField_toLaurent, hp, laurentToField_T, ← mul_assoc, zpow_neg,
    zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ (algebraMap_X_ne_zero L)), one_mul]

include k in
/-- The image of `t` in `W` is a unit, with inverse mapping to `t⁻¹`. -/
lemma exists_inv_t : ∃ v : W, algebraMap A W (algebraMap k[X] A X) * v = 1 ∧
    algebraMap W K v = (algebraMap k[X] K X)⁻¹ := by
  obtain ⟨u, hu⟩ := IsLocalization.Away.algebraMap_isUnit (S := W) (algebraMap k[X] A X)
  refine ⟨↑u⁻¹, by rw [← hu, Units.mul_inv], ?_⟩
  have h := congrArg (algebraMap W K) (Units.mul_inv u)
  rw [map_mul, map_one, hu, algebraMap_W_A, algebraMap_tA] at h
  exact eq_inv_of_mul_eq_one_right h

variable (k A W L K) in
/-- `W ⊆ K` is the set of elements with `eK`-coordinates in `k[t, t⁻¹]`. -/
lemma mem_range_W_iff [IsIntegrallyClosed A] (y : K) :
    y ∈ LinearMap.range (IsScalarTower.toAlgHom k W K).toLinearMap ↔
      ∀ i, (eK k A W L K).repr y i ∈ Set.range (laurentToField L (k := k)) := by
  constructor
  · rintro ⟨w, rfl⟩ i
    obtain ⟨m, a, ha⟩ := IsLocalization.Away.surj (algebraMap k[X] A X) w
    have h := congrArg (algebraMap W K) ha
    rw [map_mul, map_pow, algebraMap_W_A, algebraMap_tA, algebraMap_W_A] at h
    apply mem_range_laurentToField_of_pow_mul _ m
    rw [← repr_mul_pow k A W L, AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom', h,
      eK_repr_algebraMap k A W L]
    exact ⟨_, rfl⟩
  · intro h
    obtain ⟨m, hm⟩ := exists_pow_mul_mem (k := k) _ h
    obtain ⟨a, ha⟩ := mem_range_A_of_repr k A W L (y * algebraMap k[X] K X ^ m) (fun i => by
      rw [repr_mul_pow k A W L]; exact hm i)
    obtain ⟨v, -, hv⟩ := exists_inv_t (k := k) (A := A) (W := W) (K := K)
    refine ⟨algebraMap A W a * v ^ m, ?_⟩
    rw [AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom', map_mul, map_pow, hv,
      algebraMap_W_A, ha, mul_assoc, ← mul_pow, mul_inv_cancel₀ (tK_ne_zero (A := A) (W := W)),
      one_pow, mul_one]

variable (k A W L K) in
/-- **Coordinates of `W`**: `W ≅ k[t, t⁻¹]ⁿ` via the basis `eK`. -/
def coordW [IsIntegrallyClosed A] : W ≃ₗ[k] Vec k (finrank k[X] A) :=
  coordEquiv (eK k A W L K) (IsScalarTower.toAlgHom k W K).toLinearMap
    (IsFractionRing.injective W K) (mem_range_W_iff k A W L K)

lemma laurentToField_coordW [IsIntegrallyClosed A] (w : W) (i : Fin (finrank k[X] A)) :
    laurentToField L (coordW k A W L K w i) = (eK k A W L K).repr (algebraMap W K w) i :=
  laurentToField_coordEquiv _ _ _ _ w i

/-! #### Coordinates of `Ω¹_W` -/

open Different

variable (D : Derivation k K K) (hD : D (algebraMap k[X] K X) = 1)

lemma kaehlerToField_map (ω : Ω[A⁄k]) :
    kaehlerToField (A := W) D (KaehlerDifferential.map k k A W ω) =
      kaehlerToField (A := A) D ω := by
  have hω : ω ∈ Submodule.span A (Set.range (KaehlerDifferential.D k A)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hω using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨a, rfl⟩ := h
    rw [KaehlerDifferential.map_D, kaehlerToField_D, kaehlerToField_D, algebraMap_W_A]
  | zero => simp
  | add ω₁ ω₂ _ _ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add]
  | smul a ω _ h =>
    rw [map_smul, ← algebraMap_smul W a (KaehlerDifferential.map k k A W ω), LinearMap.map_smul, h,
      map_smul, Algebra.smul_def, Algebra.smul_def, algebraMap_W_A]

include L hD in
/-- `ω ↦ ω / dt` is injective on `Ω¹_{W/k}`. -/
lemma kaehlerToField_W_injective [Module.IsTorsionFree A Ω[A⁄k]] :
    Function.Injective (kaehlerToField (A := W) D) := by
  have := isFractionRing_A (k := k) (W := W) (A := A) (K := K)
  rw [injective_iff_map_eq_zero]
  intro ω hω
  obtain ⟨⟨ω₀, ⟨_, ⟨m, rfl⟩⟩⟩, h⟩ := IsLocalizedModule.surj
    (Submonoid.powers (algebraMap k[X] A X)) (KaehlerDifferential.map k k A W) ω
  simp only at h
  have h1 := congrArg (kaehlerToField (A := W) D) h
  rw [kaehlerToField_map, LinearMap.map_smul_of_tower, hω, smul_zero] at h1
  have h2 : ω₀ = 0 := kaehlerToField_injective (L := L) D hD h1.symm
  rw [h2, map_zero, Submonoid.smul_def] at h
  have hu : IsUnit (algebraMap A W (algebraMap k[X] A X ^ m)) := by
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit (S := W) (algebraMap k[X] A X)).pow m
  rw [← algebraMap_smul W] at h
  exact hu.smul_eq_zero.mp h

lemma basis_repr_mul_pow {ι : Type*} (b : Basis ι L K) (y : K) (m : ℕ) (i : ι) :
    b.repr (y * algebraMap k[X] K X ^ m) i = algebraMap k[X] L X ^ m * b.repr y i := by
  rw [← algebraMap_tL (L := L), ← map_pow, mul_comm, ← Algebra.smul_def, LinearEquiv.map_smul,
    Finsupp.smul_apply, smul_eq_mul]

variable (k A W L K) in
/-- Membership in the trace dual `A^∨` in the coordinates of the trace-dual basis. -/
lemma mem_traceDual_iff_repr [IsIntegrallyClosed A] (y : K) :
    y ∈ Submodule.traceDual k[X] L (1 : Submodule A K) ↔
      ∀ i, (eK k A W L K).traceDual.repr y i ∈ Set.range (algebraMap k[X] L) := by
  rw [Submodule.mem_traceDual]
  constructor
  · intro h i
    rw [Basis.traceDual_repr_apply, eK_apply k A W L]
    obtain ⟨c, hc⟩ := h _ (Submodule.mem_one.mpr ⟨eA k A i, rfl⟩)
    exact ⟨c, hc⟩
  · intro h x hx
    obtain ⟨a, rfl⟩ := Submodule.mem_one.mp hx
    rw [← (eK k A W L K).sum_repr (algebraMap A K a), map_sum]
    refine Subring.sum_mem _ fun i _ => ?_
    rw [map_smul, eK_repr_algebraMap k A W L, smul_eq_mul]
    refine Subring.mul_mem _ ⟨_, rfl⟩ ?_
    obtain ⟨c, hc⟩ := h i
    rw [Basis.traceDual_repr_apply] at hc
    exact ⟨c, hc⟩

variable (k A W L K) in
include hD in
/-- `Ω¹_W ⊆ K` is the set of elements with trace-dual coordinates in `k[t, t⁻¹]`. -/
lemma mem_range_kaehler_W_iff [IsAlgClosed k] [IsIntegrallyClosed A]
    [Module.IsTorsionFree A Ω[A⁄k]] (y : K) :
    y ∈ LinearMap.range ((kaehlerToField (A := W) D).restrictScalars k) ↔
      ∀ i, (eK k A W L K).traceDual.repr y i ∈ Set.range (laurentToField L (k := k)) := by
  have := isFractionRing_A (k := k) (W := W) (A := A) (K := K)
  have hded := range_kaehlerToField_eq_traceDual (k := k) (A := A) (L := L) (K := K) D hD
  constructor
  · rintro ⟨ω, rfl⟩ i
    obtain ⟨⟨ω₀, ⟨_, ⟨m, rfl⟩⟩⟩, h⟩ := IsLocalizedModule.surj
      (Submonoid.powers (algebraMap k[X] A X)) (KaehlerDifferential.map k k A W) ω
    simp only [Submonoid.smul_def] at h
    have h1 := congrArg (kaehlerToField (A := W) D) h
    rw [kaehlerToField_map, ← algebraMap_smul W, LinearMap.map_smul, Algebra.smul_def,
      map_pow, map_pow, algebraMap_W_A, algebraMap_tA] at h1
    have hmem : kaehlerToField (A := A) D ω₀ ∈ Submodule.traceDual k[X] L (1 : Submodule A K) :=
      hded ▸ ⟨ω₀, rfl⟩
    rw [mem_traceDual_iff_repr k A W L K, ← h1, mul_comm] at hmem
    apply mem_range_laurentToField_of_pow_mul _ m
    rw [← basis_repr_mul_pow]
    exact hmem i
  · intro h
    obtain ⟨m, hm⟩ := exists_pow_mul_mem (k := k) _ h
    have hz : y * algebraMap k[X] K X ^ m ∈ Submodule.traceDual k[X] L (1 : Submodule A K) := by
      rw [mem_traceDual_iff_repr k A W L K]
      intro i
      rw [basis_repr_mul_pow]
      exact hm i
    rw [← hded] at hz
    obtain ⟨ω₀, hω₀⟩ := hz
    obtain ⟨v, -, hv⟩ := exists_inv_t (k := k) (A := A) (W := W) (K := K)
    refine ⟨v ^ m • KaehlerDifferential.map k k A W ω₀, ?_⟩
    rw [LinearMap.restrictScalars_apply, LinearMap.map_smul, kaehlerToField_map, hω₀,
      Algebra.smul_def, map_pow, hv, mul_comm, mul_assoc, ← mul_pow,
      mul_inv_cancel₀ (tK_ne_zero (A := A) (W := W)), one_pow, mul_one]

variable (k A W L K) in
/-- **Coordinates of `Ω¹_W`**: `Ω¹_W ≅ k[t, t⁻¹]ⁿ` via `ω ↦ ω / dt` and the trace-dual basis. -/
def coordΩ [IsAlgClosed k] [IsIntegrallyClosed A] [Module.IsTorsionFree A Ω[A⁄k]] :
    Ω[W⁄k] ≃ₗ[k] Vec k (finrank k[X] A) := by
  refine coordEquiv (eK k A W L K).traceDual ((kaehlerToField (A := W) D).restrictScalars k)
    ?_ ?_
  · rw [LinearMap.coe_restrictScalars]
    exact kaehlerToField_W_injective (A := A) (L := L) D hD
  · exact mem_range_kaehler_W_iff k A W L K D hD

lemma laurentToField_coordΩ [IsAlgClosed k] [IsIntegrallyClosed A]
    [Module.IsTorsionFree A Ω[A⁄k]] (ω : Ω[W⁄k]) (i : Fin (finrank k[X] A)) :
    laurentToField L (coordΩ k A W L K D hD ω i) =
      Algebra.trace L K (kaehlerToField (A := W) D ω * eK k A W L K i) := by
  rw [coordΩ, laurentToField_coordEquiv, Basis.traceDual_repr_apply, Algebra.traceForm_apply,
    LinearMap.restrictScalars_apply]

/-! #### The images of `A`, `Ω¹_A` and the pairing -/

omit [Algebra k L] [IsScalarTower k k[X] L] in
lemma laurentToField_mem_range_iff (r : k[T;T⁻¹]) :
    laurentToField L r ∈ Set.range (algebraMap k[X] L) ↔ r ∈ Set.range (toLaurent (R := k)) := by
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p, laurentToField_injective L ?_⟩
    rw [laurentToField_toLaurent, hp]
  · rintro ⟨p, rfl⟩
    exact ⟨p, (laurentToField_toLaurent L p).symm⟩

lemma mem_upper_iff_forall {n : ℕ} (x : Vec k n) :
    x ∈ upper k n 0 ↔ ∀ i, x i ∈ Set.range (toLaurent (R := k)) := by
  simp only [mem_supportedIn, mem_range_toLaurent_iff, Set.mem_Ici, not_le]

/-- A submodule is the image of another under a linear equivalence iff membership corresponds. -/
lemma map_eq_of_forall {R M V : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid V] [Module R V] (e : M ≃ₗ[R] V) (S : Submodule R M) (T : Submodule R V)
    (h : ∀ m, e m ∈ T ↔ m ∈ S) : S.map (e : M →ₗ[R] V) = T := by
  ext v
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact (h m).mpr hm
  · intro hv
    exact ⟨e.symm v, (h _).mp (by simpa using hv), by simp⟩

/-- `A ⊆ W` corresponds to `k[t]ⁿ` under `coordW`. -/
lemma coordW_mem_upper_iff [IsIntegrallyClosed A] (w : W) :
    coordW k A W L K w ∈ upper k (finrank k[X] A) 0 ↔
      w ∈ LinearMap.range (IsScalarTower.toAlgHom k A W).toLinearMap := by
  rw [mem_upper_iff_forall]
  simp_rw [← laurentToField_mem_range_iff (L := L), laurentToField_coordW]
  constructor
  · intro h
    obtain ⟨a, ha⟩ := mem_range_A_of_repr k A W L _ h
    refine ⟨a, IsFractionRing.injective W K ?_⟩
    rw [AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom', algebraMap_W_A, ha]
  · rintro ⟨a, rfl⟩ i
    rw [AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom', algebraMap_W_A,
      eK_repr_algebraMap k A W L]
    exact ⟨_, rfl⟩

variable (k A W L K) in
lemma map_coordW_A [IsIntegrallyClosed A] :
    (LinearMap.range (IsScalarTower.toAlgHom k A W).toLinearMap).map
      (coordW k A W L K : W →ₗ[k] Vec k (finrank k[X] A)) = upper k (finrank k[X] A) 0 :=
  map_eq_of_forall _ _ _ fun w => coordW_mem_upper_iff w

include hD in
/-- `Ω¹_A ⊆ Ω¹_W` corresponds to `k[t]ⁿ` under `coordΩ` (Dedekind's theorem). -/
lemma coordΩ_mem_upper_iff [IsAlgClosed k] [IsIntegrallyClosed A]
    [Module.IsTorsionFree A Ω[A⁄k]] (ω : Ω[W⁄k]) :
    coordΩ k A W L K D hD ω ∈ upper k (finrank k[X] A) 0 ↔
      ω ∈ LinearMap.range ((KaehlerDifferential.map k k A W).restrictScalars k) := by
  have := isFractionRing_A (k := k) (W := W) (A := A) (K := K)
  have hded := range_kaehlerToField_eq_traceDual (k := k) (A := A) (L := L) (K := K) D hD
  rw [mem_upper_iff_forall]
  simp_rw [← laurentToField_mem_range_iff (L := L), laurentToField_coordΩ]
  have key : (∀ i, Algebra.trace L K (kaehlerToField (A := W) D ω * eK k A W L K i) ∈
      Set.range (algebraMap k[X] L)) ↔
      kaehlerToField (A := W) D ω ∈ Submodule.traceDual k[X] L (1 : Submodule A K) := by
    rw [mem_traceDual_iff_repr k A W L K]
    simp_rw [Basis.traceDual_repr_apply, Algebra.traceForm_apply]
  rw [key, ← hded]
  constructor
  · rintro ⟨ω₀, hω₀⟩
    refine ⟨ω₀, kaehlerToField_W_injective (A := A) (L := L) D hD ?_⟩
    rw [LinearMap.restrictScalars_apply, kaehlerToField_map, hω₀]
  · rintro ⟨ω₀, rfl⟩
    exact ⟨ω₀, (kaehlerToField_map D ω₀).symm⟩

variable (k A W L K) in
lemma map_coordΩ_A [IsAlgClosed k] [IsIntegrallyClosed A] [Module.IsTorsionFree A Ω[A⁄k]] :
    (LinearMap.range ((KaehlerDifferential.map k k A W).restrictScalars k)).map
      (coordΩ k A W L K D hD : Ω[W⁄k] →ₗ[k] Vec k (finrank k[X] A)) =
        upper k (finrank k[X] A) 0 :=
  map_eq_of_forall _ _ _ fun ω => coordΩ_mem_upper_iff D hD ω

/-- **The pairing**: `Tr(w · ω/dt) = j ⟨coordW w, coordΩ ω⟩`. -/
lemma trace_mul_eq_dot [IsAlgClosed k] [IsIntegrallyClosed A] [Module.IsTorsionFree A Ω[A⁄k]]
    (w : W) (ω : Ω[W⁄k]) :
    Algebra.trace L K (algebraMap W K w * kaehlerToField (A := W) D ω) =
      laurentToField L (dot (coordW k A W L K w) (coordΩ k A W L K D hD ω)) := by
  conv_lhs => rw [← (eK k A W L K).sum_repr (algebraMap W K w)]
  rw [Finset.sum_mul, map_sum, dot, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul (laurentToField L), laurentToField_coordW, laurentToField_coordΩ, smul_mul_assoc,
    LinearMap.map_smul, smul_eq_mul, mul_comm (kaehlerToField D ω)]

/-! #### The lattice of `B` -/

omit [IsDomain A] in
lemma shift_apply {n : ℕ} (j : ℤ) (x : Vec k n) (i : Fin n) : shift j x i = T j * x i := rfl

include hts in
/-- Multiplication by `s = t⁻¹` is the shift `T⁻¹` in coordinates. -/
lemma coordW_sB_mul [IsIntegrallyClosed A] (w : W) :
    coordW k A W L K (algebraMap B W (algebraMap k[X] B X) * w) =
      shift (-1) (coordW k A W L K w) := by
  funext i
  apply laurentToField_injective L
  rw [laurentToField_coordW, shift_apply]
  rw [map_mul (laurentToField L), laurentToField_T, laurentToField_coordW,
    map_mul (algebraMap W K), algebraMap_W_B, algebraMap_sB hts, ← algebraMap_tL (L := L),
    ← map_inv₀, ← Algebra.smul_def,
    LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul, zpow_neg_one]

include hts in
lemma coordW_sB_pow_mul [IsIntegrallyClosed A] (m : ℕ) (w : W) :
    coordW k A W L K (algebraMap B W (algebraMap k[X] B X) ^ m * w) =
      shift (-(m : ℤ)) (coordW k A W L K w) := by
  induction m with
  | zero => rw [pow_zero, one_mul, Nat.cast_zero, neg_zero, shift_zero]
  | succ m ih =>
    rw [pow_succ', mul_assoc, coordW_sB_mul hts, ih, shift_shift,
      show (-1 : ℤ) + -(m : ℤ) = -((m + 1 : ℕ) : ℤ) by push_cast; ring]

/-- The image of a basis vector is a unit vector. -/
lemma coordW_eA [IsIntegrallyClosed A] (i : Fin (finrank k[X] A)) :
    coordW k A W L K (algebraMap A W (eA k A i)) = unit i 0 := by
  funext i'
  apply laurentToField_injective L
  rw [laurentToField_coordW, algebraMap_W_A, eK_repr_algebraMap k A W L, Basis.repr_self,
    unit, T_zero]
  by_cases h : i = i'
  · subst h
    rw [Finsupp.single_eq_same, Pi.single_eq_same, map_one, map_one]
  · rw [Finsupp.single_apply, if_neg h, Pi.single_eq_of_ne (Ne.symm h), map_zero, map_zero]

lemma exists_mem_lower {n : ℕ} (x : Vec k n) : ∃ m : ℕ, x ∈ lower k n m := by
  classical
  set S := Finset.univ.biUnion fun i => (x i).coeff.support
  refine ⟨S.sup Int.toNat, fun i c hc => ?_⟩
  rw [Set.mem_Iic, not_le] at hc
  by_contra hne
  have hcS : c ∈ S := Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finsupp.mem_support_iff.mpr hne⟩
  have := Finset.le_sup (f := Int.toNat) hcS
  omega

lemma shift_neg_one_mem_lower {n : ℕ} {m : ℤ} {x : Vec k n} (hx : x ∈ lower k n m) :
    shift (-1) x ∈ lower k n m := by
  intro i c hc
  rw [coeff_shift]
  exact hx i _ (by rw [Set.mem_Iic] at hc ⊢; omega)

/-- A vector is the sum of its monomials. -/
lemma eq_sum_unit {n : ℕ} (x : Vec k n) :
    x = ∑ i, ∑ c ∈ (x i).coeff.support, (x i).coeff c • (unit i c : Vec k n) := by
  funext i'
  rw [Finset.sum_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, unit]
  rw [Finset.sum_eq_single i']
  · simp only [Pi.single_eq_same]
    conv_lhs => rw [eq_sum_single (x i') (x i').coeff.support
      (fun j hj => Finsupp.notMem_support_iff.mp hj)]
    refine Finset.sum_congr rfl fun c _ => single_eq_C_mul_T' _ _
  · intro b _ hb
    simp [Pi.single_eq_of_ne' hb]
  · simp

variable (k A B W L K) in
/-- The `k[s]`-lattice of `B` in the coordinates of `W`. -/
def latticeB [IsIntegrallyClosed A] : Submodule k (Vec k (finrank k[X] A)) :=
  (LinearMap.range (IsScalarTower.toAlgHom k B W).toLinearMap).map
    (coordW k A W L K : W →ₗ[k] Vec k (finrank k[X] A))

omit [IsDomain A] in
lemma shift_unit {n : ℕ} (j : ℤ) (i : Fin n) (c : ℤ) :
    shift j (unit i c : Vec k n) = unit i (j + c) := by
  funext i'
  rw [shift_apply]
  by_cases h : i' = i
  · subst h
    simp only [unit, Pi.single_eq_same]
    rw [← T_add]
  · simp [unit, h]

include hts in
/-- The image of `B` is a `k[s]`-lattice in `Rⁿ`. -/
lemma isLattice_latticeB [IsIntegrallyClosed A] :
    IsLattice k (finrank k[X] A) (latticeB k A B W L K) := by
  classical
  have hshift : ∀ x ∈ latticeB k A B W L K, shift (-1) x ∈ latticeB k A B W L K := by
    rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
    refine ⟨algebraMap B W (algebraMap k[X] B X * b), ⟨_, rfl⟩, ?_⟩
    simp only [AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom', LinearEquiv.coe_coe]
    rw [map_mul, coordW_sB_mul hts]
  have hshift' : ∀ j : ℕ, ∀ x ∈ latticeB k A B W L K,
      shift (-(j : ℤ)) x ∈ latticeB k A B W L K := by
    intro j
    induction j with
    | zero => intro x hx; rwa [Nat.cast_zero, neg_zero, shift_zero]
    | succ j ih =>
      intro x hx
      have := hshift _ (ih x hx)
      rwa [shift_shift, show (-1 : ℤ) + -(j : ℤ) = -((j + 1 : ℕ) : ℤ) by push_cast; ring] at this
  -- upper bound from finitely many generators of `B` over `k[s]`
  obtain ⟨G, hG⟩ := (Module.Finite.fg_top (R := k[X]) (M := B))
  choose mg hmg using fun g : B => exists_mem_lower (coordW k A W L K (algebraMap B W g))
  set M₁ := G.sup mg
  let S : Submodule k[X] B :=
    { carrier := {b | coordW k A W L K (algebraMap B W b) ∈ lower k (finrank k[X] A) M₁}
      add_mem' := by
        intro a b ha hb
        show coordW k A W L K (algebraMap B W (a + b)) ∈ lower k (finrank k[X] A) M₁
        rw [map_add, map_add]
        exact add_mem ha hb
      zero_mem' := by
        show coordW k A W L K (algebraMap B W 0) ∈ lower k (finrank k[X] A) M₁
        rw [map_zero, map_zero]
        exact zero_mem _
      smul_mem' := by
        intro p b hb
        have hb' : coordW k A W L K (algebraMap B W b) ∈ lower k (finrank k[X] A) M₁ := hb
        show coordW k A W L K (algebraMap B W (p • b)) ∈ lower k (finrank k[X] A) M₁
        rw [Algebra.smul_def]
        clear hb
        induction p using Polynomial.induction_on generalizing b with
        | C c =>
          rw [show algebraMap k[X] B (Polynomial.C c) = algebraMap k B c from
            (IsScalarTower.algebraMap_apply k k[X] B c).symm, map_mul,
            ← IsScalarTower.algebraMap_apply k B W, ← Algebra.smul_def, map_smul]
          exact Submodule.smul_mem _ c hb'
        | add p q hp hq =>
          rw [map_add, add_mul, map_add, map_add]
          exact add_mem (hp hb') (hq hb')
        | monomial n c ih =>
          have h' := ih (b := algebraMap k[X] B X * b) (by
            rw [map_mul, coordW_sB_mul hts]; exact shift_neg_one_mem_lower hb')
          have e : algebraMap k[X] B (Polynomial.C c * X ^ (n + 1)) * b =
              algebraMap k[X] B (Polynomial.C c * X ^ n) * (algebraMap k[X] B X * b) := by
            simp only [map_mul, map_pow]; ring
          rw [e]
          exact h' }
  have hS : (⊤ : Submodule k[X] B) ≤ S := by
    rw [← hG, Submodule.span_le]
    intro g hg
    exact lower_mono (by exact_mod_cast Finset.le_sup (f := mg) hg) (hmg g)
  have hup : latticeB k A B W L K ≤ lower k (finrank k[X] A) M₁ := by
    rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
    exact hS Submodule.mem_top
  -- lower bound from the basis of `A`
  choose me be hbe using fun i : Fin (finrank k[X] A) =>
    IsLocalization.Away.surj (algebraMap k[X] B X) (algebraMap A W (eA k A i))
  set M₂ := Finset.univ.sup me
  have hunit : ∀ i, ∀ c : ℤ, c ≤ -(M₂ : ℤ) →
      (unit i c : Vec k (finrank k[X] A)) ∈ latticeB k A B W L K := by
    intro i c hc
    have h0 : (unit i (-(me i : ℤ)) : Vec k (finrank k[X] A)) ∈ latticeB k A B W L K := by
      refine ⟨algebraMap B W (be i), ⟨be i, rfl⟩, ?_⟩
      simp only [LinearEquiv.coe_coe]
      rw [← hbe i, mul_comm, coordW_sB_pow_mul hts, coordW_eA, shift_unit, add_zero]
    have hle : me i ≤ M₂ := Finset.le_sup (f := me) (Finset.mem_univ i)
    obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = -c - me i :=
      ⟨(-c - me i).toNat, Int.toNat_of_nonneg (by omega)⟩
    have := hshift' j _ h0
    rwa [shift_unit, hj, show -(-c - (me i : ℤ)) + -(me i : ℤ) = c by ring] at this
  have hlow : lower k (finrank k[X] A) (-(M₂ : ℤ)) ≤ latticeB k A B W L K := by
    intro x hx
    rw [eq_sum_unit x]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun c hc =>
      Submodule.smul_mem _ _ (hunit i c ?_)
    by_contra h
    exact Finsupp.mem_support_iff.mp hc (hx i c (by rw [Set.mem_Iic]; omega))
  refine ⟨hshift, max M₁ M₂, le_trans (lower_mono ?_) hlow, le_trans hup (lower_mono ?_)⟩
  · push_cast; omega
  · push_cast; omega

/-! #### Dedekind's theorem for `B` over `k[s]` -/

lemma kaehlerToField_map_B (ω : Ω[B⁄k]) :
    kaehlerToField (A := W) D (KaehlerDifferential.map k k B W ω) =
      kaehlerToField (A := B) D ω := by
  have hω : ω ∈ Submodule.span B (Set.range (KaehlerDifferential.D k B)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hω using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨b, rfl⟩ := h
    rw [KaehlerDifferential.map_D, kaehlerToField_D, kaehlerToField_D, algebraMap_W_B]
  | zero => simp
  | add ω₁ ω₂ _ _ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add]
  | smul b ω _ h =>
    rw [map_smul, ← algebraMap_smul W b (KaehlerDifferential.map k k B W ω), LinearMap.map_smul, h,
      map_smul, Algebra.smul_def, Algebra.smul_def, algebraMap_W_B]

include hts hD in
/-- **Dedekind's theorem at infinity**: `y = ω / dt` comes from `Ω¹_{B/k}` iff
`Tr(t² y b) ∈ k[s]` for all `b ∈ B` (note `ω / ds = -t² ω / dt`). The proof applies
`range_kaehlerToField_eq_traceDual` to `B` over `k[s]`, through the synonyms `Flip L`, `Flip K`
carrying the `k[s]`-structures. -/
lemma mem_range_kaehler_B_iff [IsAlgClosed k] [IsIntegrallyClosed B]
    [Module.IsTorsionFree B Ω[B⁄k]] (y : K) :
    y ∈ LinearMap.range (kaehlerToField (A := B) D) ↔
      ∀ b : B, Algebra.trace L K (algebraMap k[X] K X ^ 2 * y * algebraMap B K b) ∈
        Set.range (aeval (R := k) (algebraMap k[X] L X)⁻¹) := by
  classical
  have hB := isFractionRing_B (k := k) (W := W) (B := B) (K := K)
  have htne : algebraMap k[X] K X ≠ 0 := tK_ne_zero (A := A) (W := W)
  set c : K := -(algebraMap k[X] K X ^ 2) with hc
  have hc0 : c ≠ 0 := neg_ne_zero.mpr (pow_ne_zero 2 htne)
  let iL : Algebra k[X] (Flip L) := (aeval (R := k) (algebraMap k[X] L X)⁻¹).toRingHom.toAlgebra
  let iBK : Algebra B (Flip K) := ‹Algebra B K›
  let iLK : Algebra (Flip L) (Flip K) := ‹Algebra L K›
  let ikK : Algebra k (Flip K) := ‹Algebra k K›
  let iXK : Algebra k[X] (Flip K) := ((algebraMap B K).comp (algebraMap k[X] B)).toAlgebra
  have : IsFractionRing k[X] (Flip L) :=
    isFractionRing_of_aeval_inv L (Flip L) (RingEquiv.refl L) (fun _ => rfl)
  have : IsFractionRing B (Flip K) := hB
  have : IsScalarTower k[X] (Flip L) (Flip K) := IsScalarTower.of_algebraMap_eq fun p => by
    show algebraMap B K (algebraMap k[X] B p) =
      algebraMap L K (aeval (R := k) (algebraMap k[X] L X)⁻¹ p)
    have e : (IsScalarTower.toAlgHom k B K).comp (IsScalarTower.toAlgHom k k[X] B) =
        (IsScalarTower.toAlgHom k L K).comp (aeval (R := k) (algebraMap k[X] L X)⁻¹) := by
      apply Polynomial.algHom_ext
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', aeval_X]
      rw [algebraMap_sB hts, map_inv₀, algebraMap_tL]
    exact DFunLike.congr_fun e p
  have : IsScalarTower k[X] B (Flip K) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower k B (Flip K) := ‹IsScalarTower k B K›
  have : IsScalarTower k k[X] (Flip K) := IsScalarTower.of_algebraMap_eq fun r => by
    show algebraMap k K r = algebraMap B K (algebraMap k[X] B (algebraMap k k[X] r))
    rw [← IsScalarTower.algebraMap_apply k k[X] B, ← IsScalarTower.algebraMap_apply k B K]
  have : FiniteDimensional (Flip L) (Flip K) := ‹FiniteDimensional L K›
  have : Algebra.IsSeparable (Flip L) (Flip K) := ‹Algebra.IsSeparable L K›
  let Ds : Derivation k (Flip K) (Flip K) := (c • D : Derivation k K K)
  have hDs : Ds (algebraMap k[X] (Flip K) X) = 1 := by
    show c * D (algebraMap B K (algebraMap k[X] B X)) = 1
    rw [algebraMap_sB hts, Derivation.leibniz_inv, hD, smul_eq_mul, mul_one, hc, neg_mul_neg,
      inv_pow, mul_inv_cancel₀ (pow_ne_zero 2 htne)]
  have hded := range_kaehlerToField_eq_traceDual (k := k) (A := B) (L := Flip L) (K := Flip K)
    Ds hDs
  have hψ : ∀ ω₀ : Ω[B⁄k],
      (kaehlerToField (A := B) Ds ω₀ : K) = c * kaehlerToField (A := B) D ω₀ := by
    intro ω₀
    have hω : ω₀ ∈ Submodule.span B (Set.range (KaehlerDifferential.D k B)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction hω using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨b, rfl⟩ := h
      rw [kaehlerToField_D, kaehlerToField_D]
      rfl
    | zero =>
      rw [map_zero, map_zero, mul_zero]
      rfl
    | add ω₁ ω₂ _ _ h₁ h₂ =>
      rw [map_add, map_add, mul_add, ← h₁, ← h₂]
      rfl
    | smul b ω _ h =>
      rw [LinearMap.map_smul, LinearMap.map_smul, Algebra.smul_def, Algebra.smul_def, h]
      exact mul_left_comm _ _ _
  constructor
  · rintro ⟨ω₀, rfl⟩ b
    have hmem : kaehlerToField (A := B) Ds ω₀ ∈
        Submodule.traceDual k[X] (Flip L) (1 : Submodule B (Flip K)) := hded ▸ ⟨ω₀, rfl⟩
    rw [Submodule.mem_traceDual] at hmem
    obtain ⟨p, hp⟩ := hmem _ (Submodule.mem_one.mpr ⟨b, rfl⟩)
    rw [Algebra.traceForm_apply] at hp
    have hp' : aeval (R := k) (algebraMap k[X] L X)⁻¹ p =
        Algebra.trace L K (c * kaehlerToField (A := B) D ω₀ * algebraMap B K b) := by
      rw [← hψ]
      exact hp
    refine ⟨-p, ?_⟩
    rw [map_neg, hp', hc, neg_mul, neg_mul, map_neg, neg_neg]
  · intro h
    have hmem : @id (Flip K) (c * y) ∈
        Submodule.traceDual k[X] (Flip L) (1 : Submodule B (Flip K)) := by
      rw [Submodule.mem_traceDual]
      intro a ha
      obtain ⟨b, rfl⟩ := Submodule.mem_one.mp ha
      obtain ⟨p, hp⟩ := h b
      refine ⟨-p, ?_⟩
      rw [Algebra.traceForm_apply]
      show aeval (R := k) (algebraMap k[X] L X)⁻¹ (-p) =
        Algebra.trace L K (c * y * algebraMap B K b)
      rw [map_neg, hp, hc, neg_mul, neg_mul, map_neg]
    rw [← hded] at hmem
    obtain ⟨ω₀, hω₀⟩ := hmem
    refine ⟨ω₀, mul_left_cancel₀ hc0 ?_⟩
    rw [← hψ]
    exact hω₀

include hts hD in
/-- `Ω¹_B ⊆ Ω¹_W` corresponds to the Serre dual of the lattice of `B` under `coordΩ`. -/
lemma coordΩ_mem_serreDual_iff [IsAlgClosed k] [IsIntegrallyClosed A]
    [Module.IsTorsionFree A Ω[A⁄k]] [IsIntegrallyClosed B] [Module.IsTorsionFree B Ω[B⁄k]]
    (ω : Ω[W⁄k]) :
    coordΩ k A W L K D hD ω ∈ serreDual k (finrank k[X] A) (latticeB k A B W L K) ↔
      ω ∈ LinearMap.range ((KaehlerDifferential.map k k B W).restrictScalars k) := by
  have h1 : ω ∈ LinearMap.range ((KaehlerDifferential.map k k B W).restrictScalars k) ↔
      kaehlerToField (A := W) D ω ∈ LinearMap.range (kaehlerToField (A := B) D) := by
    constructor
    · rintro ⟨ω₀, rfl⟩
      exact ⟨ω₀, (kaehlerToField_map_B D ω₀).symm⟩
    · rintro ⟨ω₀, hω₀⟩
      refine ⟨ω₀, kaehlerToField_W_injective (A := A) (L := L) D hD ?_⟩
      rw [LinearMap.restrictScalars_apply, kaehlerToField_map_B, hω₀]
  have h2 : ∀ b : B, Algebra.trace L K
      (algebraMap k[X] K X ^ 2 * kaehlerToField (A := W) D ω * algebraMap B K b) =
      laurentToField L
        (T 2 * dot (coordW k A W L K (algebraMap B W b)) (coordΩ k A W L K D hD ω)) := by
    intro b
    rw [map_mul (laurentToField L), laurentToField_T, ← trace_mul_eq_dot, algebraMap_W_B,
      mul_assoc, ← algebraMap_tL (L := L), ← map_pow, ← Algebra.smul_def, LinearMap.map_smul,
      smul_eq_mul, mul_comm (kaehlerToField (A := W) D ω),
      show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]
  rw [h1, mem_range_kaehler_B_iff (L := L) hts D hD]
  simp_rw [h2, laurentToField_mem_range_aeval_iff, coeff_T_mul]
  constructor
  · intro hy b c hc
    have hy' : ∀ x ∈ latticeB k A B W L K, ∀ j, -1 ≤ j →
        (dot x (coordΩ k A W L K D hD ω)).coeff j = 0 := hy
    exact hy' _ ⟨algebraMap B W b, ⟨b, rfl⟩, rfl⟩ _ (by omega)
  · rintro h _ ⟨_, ⟨b, rfl⟩, rfl⟩ j hj
    have := h b (j + 2) (by omega)
    rwa [add_sub_cancel_right] at this

variable (k A B W L K) in
include hts in
/-- `Ω¹_B` gives the Serre dual lattice `N'` (`f_* Ω¹_X ≅ (f_* 𝒪_X)^∨ ⊗ Ω¹_{ℙ¹}` at `∞`). -/
lemma map_coordΩ_B [IsAlgClosed k] [IsIntegrallyClosed A] [Module.IsTorsionFree A Ω[A⁄k]]
    [IsIntegrallyClosed B] [Module.IsTorsionFree B Ω[B⁄k]] :
    (LinearMap.range ((KaehlerDifferential.map k k B W).restrictScalars k)).map
      (coordΩ k A W L K D hD : Ω[W⁄k] →ₗ[k] Vec k (finrank k[X] A)) =
        serreDual k (finrank k[X] A) (latticeB k A B W L K) :=
  map_eq_of_forall _ _ _ fun ω => coordΩ_mem_serreDual_iff hts D hD ω

/-! #### Numerical Serre duality -/

variable (k A W) in
include k in
/-- `Ω¹_A → Ω¹_W` is injective when `Ω¹_A` is torsion free (`W` is a localization of `A`). -/
lemma kaehler_map_injective_A [Module.IsTorsionFree A Ω[A⁄k]] :
    Function.Injective (KaehlerDifferential.map k k A W) := by
  rw [injective_iff_map_eq_zero]
  intro ω hω
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := IsLocalizedModule.exists_of_eq
    (S := Submonoid.powers (algebraMap k[X] A X)) (f := KaehlerDifferential.map k k A W)
    (hω.trans (map_zero _).symm)
  rw [smul_zero, Submonoid.smul_def] at hm
  exact (smul_eq_zero.mp hm).resolve_left (pow_ne_zero _ (algebraMap_X_ne_zero' (k := k) A))

variable (k B W) in
include k in
/-- `Ω¹_B → Ω¹_W` is injective when `Ω¹_B` is torsion free. -/
lemma kaehler_map_injective_B [Module.IsTorsionFree B Ω[B⁄k]] :
    Function.Injective (KaehlerDifferential.map k k B W) := by
  rw [injective_iff_map_eq_zero]
  intro ω hω
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := IsLocalizedModule.exists_of_eq
    (S := Submonoid.powers (algebraMap k[X] B X)) (f := KaehlerDifferential.map k k B W)
    (hω.trans (map_zero _).symm)
  rw [smul_zero, Submonoid.smul_def] at hm
  exact (smul_eq_zero.mp hm).resolve_left (pow_ne_zero _ (algebraMap_X_ne_zero' (k := k) B))

variable (L K) in
lemma finrank_H0_structure [IsIntegrallyClosed A] :
    finrank k (H0 (resO k A W) (resO k B W) LinearMap.id) =
      finrank k (upper k (finrank k[X] A) 0 ⊓ latticeB k A B W L K : Submodule k _) := by
  rw [(H0EquivInf (algebraMap_injective_away (k := k) A W)
    (algebraMap_injective_away (k := k) B W)).finrank_eq, finrank_inf_map (coordW k A W L K),
    map_coordW_A k A W L K]
  rfl

variable (L K) in
lemma finrank_H1_structure [IsIntegrallyClosed A] :
    finrank k (H1 (resO k A W) (resO k B W) LinearMap.id) =
      finrank k (Vec k (finrank k[X] A) ⧸ (upper k (finrank k[X] A) 0 ⊔ latticeB k A B W L K)) := by
  rw [(H1EquivQuot _ _).finrank_eq, (quotSupEquiv (coordW k A W L K) _ _).finrank_eq,
    map_coordW_A k A W L K]
  rfl

include hts hD in
lemma finrank_H0_kaehler_eq [IsAlgClosed k] [IsIntegrallyClosed A]
    [Module.IsTorsionFree A Ω[A⁄k]] [IsIntegrallyClosed B] [Module.IsTorsionFree B Ω[B⁄k]] :
    finrank k (H0 (resΩ k A W) (resΩ k B W) LinearMap.id) =
      finrank k (upper k (finrank k[X] A) 0 ⊓
        serreDual k (finrank k[X] A) (latticeB k A B W L K) : Submodule k _) := by
  rw [(H0EquivInf (kaehler_map_injective_A k A W) (kaehler_map_injective_B k B W)).finrank_eq,
    finrank_inf_map (coordΩ k A W L K D hD), map_coordΩ_A k A W L K D hD,
    map_coordΩ_B k A B W L K hts D hD]

include hts hD in
lemma finrank_H1_kaehler_eq [IsAlgClosed k] [IsIntegrallyClosed A]
    [Module.IsTorsionFree A Ω[A⁄k]] [IsIntegrallyClosed B] [Module.IsTorsionFree B Ω[B⁄k]] :
    finrank k (H1 (resΩ k A W) (resΩ k B W) LinearMap.id) =
      finrank k (Vec k (finrank k[X] A) ⧸ (upper k (finrank k[X] A) 0 ⊔
        serreDual k (finrank k[X] A) (latticeB k A B W L K))) := by
  rw [(H1EquivQuot _ _).finrank_eq, (quotSupEquiv (coordΩ k A W L K D hD) _ _).finrank_eq,
    map_coordΩ_A k A W L K D hD, map_coordΩ_B k A B W L K hts D hD]

variable (L K) in
include L K hts in
/-- `H⁰(X, 𝒪_X)` is finite-dimensional. -/
theorem finiteDimensional_H0_structure [IsIntegrallyClosed A] :
    FiniteDimensional k (H0 (resO k A W) (resO k B W) LinearMap.id) := by
  have h := (isLattice_latticeB (L := L) (K := K) hts).finiteDimensional_inf
  rw [latticeB, ← map_coordW_A k A W L K] at h
  have := finiteDimensional_inf_of_map (coordW k A W L K) _ _ h
  exact Module.Finite.equiv (H0EquivInf (algebraMap_injective_away (k := k) A W)
    (algebraMap_injective_away (k := k) B W)).symm

variable (L K) in
include L K hts in
/-- `H¹(X, 𝒪_X)` is finite-dimensional. -/
theorem finiteDimensional_H1_structure [IsIntegrallyClosed A] :
    FiniteDimensional k (H1 (resO k A W) (resO k B W) LinearMap.id) := by
  have h := (isLattice_latticeB (L := L) (K := K) hts).finiteDimensional_quot
  rw [latticeB, ← map_coordW_A k A W L K] at h
  have := finiteDimensional_quot_of_map (coordW k A W L K) _ _ h
  exact Module.Finite.equiv (H1EquivQuot _ _).symm

variable (L K) in
include L K hts in
/-- `H⁰(X, Ω¹_X)` is finite-dimensional. -/
theorem finiteDimensional_H0_kaehler [IsAlgClosed k] [IsIntegrallyClosed A]
    [Module.IsTorsionFree A Ω[A⁄k]] [IsIntegrallyClosed B] [Module.IsTorsionFree B Ω[B⁄k]] :
    FiniteDimensional k (H0 (resΩ k A W) (resΩ k B W) LinearMap.id) := by
  have h := (isLattice_latticeB (L := L) (K := K) hts).serreDual.finiteDimensional_inf
  rw [← map_coordΩ_A k A W L K _ (ddt_X k L K),
    ← map_coordΩ_B k A B W L K hts _ (ddt_X k L K)] at h
  have := finiteDimensional_inf_of_map (coordΩ k A W L K _ (ddt_X k L K)) _ _ h
  exact Module.Finite.equiv (H0EquivInf (kaehler_map_injective_A k A W)
    (kaehler_map_injective_B k B W)).symm

variable (L K) in
include L K hts in
/-- `H¹(X, Ω¹_X)` is finite-dimensional. -/
theorem finiteDimensional_H1_kaehler [IsAlgClosed k] [IsIntegrallyClosed A]
    [Module.IsTorsionFree A Ω[A⁄k]] [IsIntegrallyClosed B] [Module.IsTorsionFree B Ω[B⁄k]] :
    FiniteDimensional k (H1 (resΩ k A W) (resΩ k B W) LinearMap.id) := by
  have h := (isLattice_latticeB (L := L) (K := K) hts).serreDual.finiteDimensional_quot
  rw [← map_coordΩ_A k A W L K _ (ddt_X k L K),
    ← map_coordΩ_B k A B W L K hts _ (ddt_X k L K)] at h
  have := finiteDimensional_quot_of_map (coordΩ k A W L K _ (ddt_X k L K)) _ _ h
  exact Module.Finite.equiv (H1EquivQuot _ _).symm

variable (L K) in
include L K hts in
/-- **Serre duality, `H⁰` part**: `h⁰(X, Ω¹_X) = h¹(X, 𝒪_X)`. -/
theorem finrank_H0_kaehler [IsAlgClosed k] [IsIntegrallyClosed A]
    [Module.IsTorsionFree A Ω[A⁄k]] [IsIntegrallyClosed B] [Module.IsTorsionFree B Ω[B⁄k]] :
    finrank k (H0 (resΩ k A W) (resΩ k B W) LinearMap.id) =
      finrank k (H1 (resO k A W) (resO k B W) LinearMap.id) := by
  rw [finrank_H0_kaehler_eq (L := L) hts _ (ddt_X k L K),
    finrank_inf_serreDual (isLattice_latticeB (L := L) (K := K) hts), finrank_H1_structure L K]

variable (L K) in
include L K hts in
/-- **Serre duality, `H¹` part**: `h¹(X, Ω¹_X) = h⁰(X, 𝒪_X)`. -/
theorem finrank_H1_kaehler [IsAlgClosed k] [IsIntegrallyClosed A]
    [Module.IsTorsionFree A Ω[A⁄k]] [IsIntegrallyClosed B] [Module.IsTorsionFree B Ω[B⁄k]] :
    finrank k (H1 (resΩ k A W) (resΩ k B W) LinearMap.id) =
      finrank k (H0 (resO k A W) (resO k B W) LinearMap.id) := by
  rw [finrank_H1_kaehler_eq (L := L) hts _ (ddt_X k L K),
    finrank_quot_serreDual (isLattice_latticeB (L := L) (K := K) hts), finrank_H0_structure L K]

variable (L K) in
include L K hts in
/-- **`χ(Ω¹_X) = -χ(𝒪_X)`.** -/
theorem euler_kaehler [IsAlgClosed k] [IsIntegrallyClosed A]
    [Module.IsTorsionFree A Ω[A⁄k]] [IsIntegrallyClosed B] [Module.IsTorsionFree B Ω[B⁄k]] :
    (finrank k (H0 (resΩ k A W) (resΩ k B W) LinearMap.id) : ℤ) -
        finrank k (H1 (resΩ k A W) (resΩ k B W) LinearMap.id) =
      -((finrank k (H0 (resO k A W) (resO k B W) LinearMap.id) : ℤ) -
        finrank k (H1 (resO k A W) (resO k B W) LinearMap.id)) := by
  rw [finrank_H0_kaehler L K hts, finrank_H1_kaehler L K hts]
  ring

variable (L K) in
include L K hts in
/-- **`deg Ω¹_X = 2g - 2`**: with `deg Ω¹_X := χ(Ω¹_X) - χ(𝒪_X)` (the degree of a line bundle
in Riemann–Roch form) and the arithmetic genus `g := 1 - χ(𝒪_X)`. -/
theorem deg_kaehler [IsAlgClosed k] [IsIntegrallyClosed A]
    [Module.IsTorsionFree A Ω[A⁄k]] [IsIntegrallyClosed B] [Module.IsTorsionFree B Ω[B⁄k]] :
    ((finrank k (H0 (resΩ k A W) (resΩ k B W) LinearMap.id) : ℤ) -
        finrank k (H1 (resΩ k A W) (resΩ k B W) LinearMap.id)) -
      ((finrank k (H0 (resO k A W) (resO k B W) LinearMap.id) : ℤ) -
        finrank k (H1 (resO k A W) (resO k B W) LinearMap.id)) =
      2 * (1 - ((finrank k (H0 (resO k A W) (resO k B W) LinearMap.id) : ℤ) -
        finrank k (H1 (resO k A W) (resO k B W) LinearMap.id))) - 2 := by
  rw [euler_kaehler L K hts]
  ring

variable (L K) in
include L K hts in
/-- **`h⁰(Ω¹_X) = g`** when `h⁰(𝒪_X) = 1` (e.g. `X` proper and connected over `k = k̄`), with
`g = 1 - χ(𝒪_X) = h¹(𝒪_X)`; then also `h¹(Ω¹_X) = 1`. -/
theorem finrank_H0_kaehler_eq_genus [IsAlgClosed k] [IsIntegrallyClosed A]
    [Module.IsTorsionFree A Ω[A⁄k]] [IsIntegrallyClosed B] [Module.IsTorsionFree B Ω[B⁄k]]
    (h1 : finrank k (H0 (resO k A W) (resO k B W) LinearMap.id) = 1) :
    (finrank k (H0 (resΩ k A W) (resΩ k B W) LinearMap.id) : ℤ) =
        1 - ((finrank k (H0 (resO k A W) (resO k B W) LinearMap.id) : ℤ) -
          finrank k (H1 (resO k A W) (resO k B W) LinearMap.id)) ∧
      finrank k (H1 (resΩ k A W) (resΩ k B W) LinearMap.id) = 1 := by
  refine ⟨?_, by rw [finrank_H1_kaehler L K hts, h1]⟩
  rw [finrank_H0_kaehler L K hts, h1]
  push_cast
  ring

end Curve

end

end DeJongAlterations.StableModification.CurvesField.Duality
