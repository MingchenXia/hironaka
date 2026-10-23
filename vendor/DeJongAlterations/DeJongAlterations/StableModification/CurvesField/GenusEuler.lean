/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Mathlib.Algebra.Homology.EulerCharacteristic
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Finiteness.Finsupp

/-!
# Euler characteristics of cochain complexes of vector spaces

The homological algebra behind the genus formula (Lemma B.1 of M. Temkin, *Stable modification
of relative curves*, J. Algebraic Geom. 19 (2010), `references/temkin10-stable-modification`,
`semi-stable.tex`, lines 4413–4433): Temkin computes `p_a` by "computing the dimensions of the
cohomology groups" in the long exact sequence of `0 → 𝒪_C → π_*𝒪_{C̃} → π_*𝒪_{C̃}/𝒪_C → 0`.
For `ℕ`-indexed cochain complexes of vector spaces over a field `k` whose homology vanishes from
some degree `N` on, this file proves:

* `sum_finrank_homology_eq_sum_finrank_X`: for a complex of finite-dimensional spaces with
  `C^i = 0` for `i ≥ N`, `∑_{i<N} (-1)^i dim H^i(C) = ∑_{i<N} (-1)^i dim C^i`;
* `sum_finrank_homology_of_shortExact`: for a short exact sequence `0 → A → B → C → 0` of
  complexes with finite-dimensional homology and `H^i(A) = 0` for `i ≥ N`, the alternating sums
  of the dimensions of homology satisfy `χ_{<N}(B) = χ_{<N}(A) + χ_{<N}(C)`;
* `finiteDimensional_homology_X₂`: in such a sequence, finite-dimensional homology of `A` and `C`
  gives finite-dimensional homology of `B`.

The Euler characteristics of Mathlib (`HomologicalComplex.eulerChar`,
`HomologicalComplex.homologyEulerChar`) are compared with these finite sums by
`homologyEulerChar_eq_sum` and `eulerChar_eq_sum`. Blueprint: `sm-curves-fields-genus.tex`,
`lem:sm-euler-additive`, `lem:sm-euler-terms`.
-/

namespace DeJongAlterations.StableModification.CurvesField.Genus

open CategoryTheory Module Finset

set_option autoImplicit false

universe u

variable {k : Type u} [Field k]

section LinearAlgebra

variable {V₁ V₂ V₃ : Type*} [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
  [AddCommGroup V₃] [Module k V₃] {f : V₁ →ₗ[k] V₂} {g : V₂ →ₗ[k] V₃}

/-- **Rank–nullity in the middle of an exact sequence**: `dim V₂ = rk f + rk g`. -/
theorem finrank_eq_add_of_exact [FiniteDimensional k V₂] (h : Function.Exact f g) :
    finrank k V₂ = finrank k (LinearMap.range f) + finrank k (LinearMap.range g) := by
  rw [← LinearMap.finrank_range_add_finrank_ker g, LinearMap.exact_iff.1 h, add_comm]

/-- In an exact sequence `V₁ → V₂ → V₃` with `V₁` and `V₃` finite-dimensional, `V₂` is
finite-dimensional. -/
theorem finiteDimensional_of_exact [FiniteDimensional k V₁] [FiniteDimensional k V₃]
    (h : Function.Exact f g) : FiniteDimensional k V₂ := by
  have h' : Function.Exact f g.rangeRestrict := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict]
    exact LinearMap.exact_iff.1 h
  exact Module.Finite.of_exact h' g.surjective_rangeRestrict

/-- Corestricting a linear map does not change the dimension of its range. -/
theorem finrank_range_codRestrict (p : Submodule k V₂) (f : V₁ →ₗ[k] V₂) (h : ∀ x, f x ∈ p) :
    finrank k (LinearMap.range (f.codRestrict p h)) = finrank k (LinearMap.range f) := by
  rw [LinearMap.range_codRestrict]
  exact (Submodule.comapSubtypeEquivOfLe (by rintro _ ⟨x, rfl⟩; exact h x)).finrank_eq

end LinearAlgebra

section ShortComplex

variable (S : ShortComplex (ModuleCat.{u} k))

/-- Rank–nullity in the middle of an exact short complex of vector spaces. -/
theorem finrank_X₂_of_exact (hS : S.Exact) [FiniteDimensional k S.X₂] :
    finrank k S.X₂ = finrank k (LinearMap.range S.f.hom) + finrank k (LinearMap.range S.g.hom) :=
  finrank_eq_add_of_exact (LinearMap.exact_iff.2 hS.moduleCat_range_eq_ker.symm)

/-- The middle term of an exact short complex with finite-dimensional ends is finite-dimensional. -/
theorem finiteDimensional_X₂_of_exact (hS : S.Exact) [FiniteDimensional k S.X₁]
    [FiniteDimensional k S.X₃] : FiniteDimensional k S.X₂ :=
  finiteDimensional_of_exact (f := S.f.hom) (g := S.g.hom)
    (LinearMap.exact_iff.2 hS.moduleCat_range_eq_ker.symm)

/-- The homology of a short complex of vector spaces with finite-dimensional middle term is
finite-dimensional. -/
theorem finiteDimensional_homology [FiniteDimensional k S.X₂] :
    FiniteDimensional k S.homology := by
  have : FiniteDimensional k S.moduleCatLeftHomologyData.H := by
    change FiniteDimensional k (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles)
    infer_instance
  exact Module.Finite.equiv S.moduleCatHomologyIso.toLinearEquiv.symm

/-- `dim H(S) + rk f = dim ker g` for a short complex `S = (f, g)` of vector spaces. -/
theorem finrank_homology_add_finrank_range [FiniteDimensional k S.X₂] :
    finrank k S.homology + finrank k (LinearMap.range S.f.hom) =
      finrank k (LinearMap.ker S.g.hom) := by
  have e₁ : finrank k S.homology =
      finrank k (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) :=
    S.moduleCatHomologyIso.toLinearEquiv.finrank_eq
  have e₂ : finrank k (LinearMap.range S.moduleCatToCycles) =
      finrank k (LinearMap.range S.f.hom) :=
    finrank_range_codRestrict _ _ _
  rw [e₁, ← e₂, Submodule.finrank_quotient_add_finrank]

end ShortComplex

section Complex

variable (C : CochainComplex (ModuleCat.{u} k) ℕ)

/-- The rank of the differential `d^i : C^i → C^{i+1}`. -/
noncomputable def rankD (i : ℕ) : ℕ := finrank k (LinearMap.range (C.d i (i + 1)).hom)

/-- The homology of a complex of finite-dimensional spaces is finite-dimensional. -/
theorem finiteDimensional_homology_of_X [∀ i, FiniteDimensional k (C.X i)] (i : ℕ) :
    FiniteDimensional k (C.homology i) := by
  have : FiniteDimensional k (C.sc i).X₂ := (inferInstance : FiniteDimensional k (C.X i))
  exact finiteDimensional_homology (C.sc i)

/-- `dim H^0(C) + rk d^0 = dim C^0`. -/
theorem finrank_homology_zero_add [∀ i, FiniteDimensional k (C.X i)] :
    finrank k (C.homology 0) + rankD C 0 = finrank k (C.X 0) := by
  have h₂ := LinearMap.finrank_range_add_finrank_ker (C.d 0 1).hom
  have e := (C.homologyIsoSc' 0 0 1 (by simp) (by simp)).toLinearEquiv.finrank_eq
  have : FiniteDimensional k (C.sc' 0 0 1).X₂ := (inferInstance : FiniteDimensional k (C.X 0))
  have h₁ := finrank_homology_add_finrank_range (C.sc' 0 0 1)
  have hf : (C.sc' 0 0 1).f = 0 := C.shape _ _ (by simp)
  rw [hf] at h₁
  change finrank k (C.sc' 0 0 1).homology + finrank k (LinearMap.range (0 : C.X 0 →ₗ[k] C.X 0)) =
    finrank k (LinearMap.ker (C.d 0 1).hom) at h₁
  rw [LinearMap.range_zero, finrank_bot] at h₁
  have hr : rankD C 0 = finrank k (LinearMap.range (C.d 0 1).hom) := rfl
  omega

/-- `dim H^{i+1}(C) + rk d^i + rk d^{i+1} = dim C^{i+1}`. -/
theorem finrank_homology_succ_add [∀ i, FiniteDimensional k (C.X i)] (i : ℕ) :
    finrank k (C.homology (i + 1)) + rankD C i + rankD C (i + 1) = finrank k (C.X (i + 1)) := by
  have h₂ := LinearMap.finrank_range_add_finrank_ker (C.d (i + 1) (i + 1 + 1)).hom
  have e := (C.homologyIsoSc' i (i + 1) (i + 2) (by simp) (by simp)).toLinearEquiv.finrank_eq
  have : FiniteDimensional k (C.sc' i (i + 1) (i + 2)).X₂ :=
    (inferInstance : FiniteDimensional k (C.X (i + 1)))
  have h₁ := finrank_homology_add_finrank_range (C.sc' i (i + 1) (i + 2))
  change finrank k (C.sc' i (i + 1) (i + 2)).homology +
    finrank k (LinearMap.range (C.d i (i + 1)).hom) =
      finrank k (LinearMap.ker (C.d (i + 1) (i + 1 + 1)).hom) at h₁
  rw [rankD, rankD]
  omega

/-- **The Euler characteristic can be computed from the terms**: for a complex of
finite-dimensional spaces with `C^i = 0` for `i ≥ N`,
`∑_{i<N} (-1)^i dim H^i(C) = ∑_{i<N} (-1)^i dim C^i`. -/
theorem sum_finrank_homology_eq_sum_finrank_X [∀ i, FiniteDimensional k (C.X i)] (N : ℕ)
    (hN : ∀ i, N ≤ i → Subsingleton (C.X i)) :
    ∑ i ∈ range N, (-1 : ℤ) ^ i * finrank k (C.homology i) =
      ∑ i ∈ range N, (-1 : ℤ) ^ i * finrank k (C.X i) := by
  have key : ∀ n, ∑ i ∈ range (n + 1), (-1 : ℤ) ^ i *
      ((finrank k (C.X i) : ℤ) - finrank k (C.homology i)) = (-1 : ℤ) ^ n * rankD C n := by
    intro n
    induction n with
    | zero =>
      have := finrank_homology_zero_add C
      simp only [zero_add, range_one, sum_singleton, pow_zero, one_mul]
      omega
    | succ n ih =>
      rw [sum_range_succ, ih]
      have := finrank_homology_succ_add C n
      rw [pow_succ]
      have h' : ((finrank k (C.X (n + 1)) : ℤ) - finrank k (C.homology (n + 1))) =
          rankD C n + rankD C (n + 1) := by omega
      rw [h']
      ring
  rcases N with _ | n
  · simp
  · have hzero : rankD C n = 0 := by
      have : Subsingleton (C.X (n + 1)) := hN (n + 1) le_rfl
      have h0 : finrank k (C.X (n + 1)) = 0 := finrank_zero_of_subsingleton
      have := finrank_homology_succ_add C n
      omega
    have h := key n
    rw [hzero, Nat.cast_zero, mul_zero] at h
    rw [← sub_eq_zero, ← sum_sub_distrib, ← neg_eq_zero, ← sum_neg_distrib, ← h]
    refine sum_congr rfl fun i _ => ?_
    ring

end Complex

section LongExact

variable {S : ShortComplex (CochainComplex (ModuleCat.{u} k) ℕ)} (hS : S.ShortExact)
include hS

/-- `H^0(A) → H^0(B)` is injective for a short exact sequence of `ℕ`-indexed cochain complexes. -/
theorem injective_homologyMap_f_zero :
    Function.Injective (HomologicalComplex.homologyMap S.f 0).hom := by
  have := hS.mono_f
  have : Mono (S.f.f 0) := inferInstance
  have : Mono (HomologicalComplex.homologyMap S.f 0) :=
    HomologicalComplex.mono_homologyMap_of_mono_of_not_rel S.f 0 (by simp)
  exact (ModuleCat.mono_iff_injective _).1 this

/-- In a short exact sequence of complexes, finite-dimensional homology of the outer complexes
gives finite-dimensional homology of the middle one. -/
theorem finiteDimensional_homology_X₂ (i : ℕ) [FiniteDimensional k (S.X₁.homology i)]
    [FiniteDimensional k (S.X₃.homology i)] : FiniteDimensional k (S.X₂.homology i) :=
  finiteDimensional_X₂_of_exact _ (hS.homology_exact₂ i)

/-- **Additivity of the Euler characteristic** in a short exact sequence `0 → A → B → C → 0` of
`ℕ`-indexed cochain complexes of vector spaces with finite-dimensional homology and `H^i(A) = 0`
for `i ≥ N`: `∑_{i<N} (-1)^i dim H^i(B) = ∑_{i<N} (-1)^i dim H^i(A) + ∑_{i<N} (-1)^i dim H^i(C)`.
-/
theorem sum_finrank_homology_of_shortExact [∀ i, FiniteDimensional k (S.X₁.homology i)]
    [∀ i, FiniteDimensional k (S.X₂.homology i)] [∀ i, FiniteDimensional k (S.X₃.homology i)]
    (N : ℕ) (hN : ∀ i, N ≤ i → Subsingleton (S.X₁.homology i)) :
    ∑ i ∈ range N, (-1 : ℤ) ^ i * finrank k (S.X₂.homology i) =
      ∑ i ∈ range N, (-1 : ℤ) ^ i * finrank k (S.X₁.homology i) +
        ∑ i ∈ range N, (-1 : ℤ) ^ i * finrank k (S.X₃.homology i) := by
  set rf : ℕ → ℕ := fun i => finrank k (LinearMap.range (HomologicalComplex.homologyMap S.f i).hom)
  set rg : ℕ → ℕ := fun i => finrank k (LinearMap.range (HomologicalComplex.homologyMap S.g i).hom)
  set rδ : ℕ → ℕ := fun i => finrank k (LinearMap.range (hS.δ i (i + 1) rfl).hom)
  have hb : ∀ i, finrank k (S.X₂.homology i) = rf i + rg i := fun i =>
    finrank_X₂_of_exact _ (hS.homology_exact₂ i)
  have hc : ∀ i, finrank k (S.X₃.homology i) = rg i + rδ i := fun i =>
    finrank_X₂_of_exact _ (hS.homology_exact₃ i (i + 1) rfl)
  have ha : ∀ i, finrank k (S.X₁.homology (i + 1)) = rδ i + rf (i + 1) := fun i =>
    finrank_X₂_of_exact _ (hS.homology_exact₁ i (i + 1) rfl)
  have ha₀ : finrank k (S.X₁.homology 0) = rf 0 :=
    (LinearMap.finrank_range_of_inj (injective_homologyMap_f_zero hS)).symm
  have key : ∀ n, ∑ i ∈ range (n + 1), (-1 : ℤ) ^ i *
      ((finrank k (S.X₁.homology i) : ℤ) - finrank k (S.X₂.homology i) +
        finrank k (S.X₃.homology i)) = (-1 : ℤ) ^ n * rδ n := by
    intro n
    induction n with
    | zero =>
      simp only [zero_add, range_one, sum_singleton, pow_zero, one_mul]
      rw [ha₀, hb, hc]
      push_cast
      ring
    | succ n ih =>
      rw [sum_range_succ, ih, ha, hb, hc, pow_succ]
      push_cast
      ring
  rw [← sub_eq_zero, ← sum_add_distrib, ← sum_sub_distrib]
  rcases N with _ | n
  · simp
  · have hzero : rδ n = 0 := by
      have : Subsingleton (S.X₁.homology (n + 1)) := hN (n + 1) le_rfl
      have h0 : finrank k (S.X₁.homology (n + 1)) = 0 := finrank_zero_of_subsingleton
      have := ha n
      omega
    have h := key n
    rw [hzero, Nat.cast_zero, mul_zero] at h
    rw [← neg_eq_zero, ← sum_neg_distrib, ← h]
    refine sum_congr rfl fun i _ => ?_
    ring

end LongExact

section Mathlib

variable (C : CochainComplex (ModuleCat.{u} k) ℕ)

/-- Mathlib's homological Euler characteristic as a finite sum, when the homology vanishes in
degrees `≥ N`. -/
theorem homologyEulerChar_eq_sum (N : ℕ) (hN : ∀ i, N ≤ i → Subsingleton (C.homology i)) :
    C.homologyEulerChar = ∑ i ∈ range N, (-1 : ℤ) ^ i * finrank k (C.homology i) := by
  rw [HomologicalComplex.homologyEulerChar_eq_sum_finSet_of_finrankSupport_subset C (range N)]
  · simp
  · intro i hi
    by_contra hiN
    simp only [coe_range, Set.mem_Iio, not_lt] at hiN
    have : Subsingleton (C.homology i) := hN i hiN
    exact hi finrank_zero_of_subsingleton

/-- Mathlib's Euler characteristic of the terms as a finite sum, when `C^i = 0` for `i ≥ N`. -/
theorem eulerChar_eq_sum (N : ℕ) (hN : ∀ i, N ≤ i → Subsingleton (C.X i)) :
    C.eulerChar = ∑ i ∈ range N, (-1 : ℤ) ^ i * finrank k (C.X i) := by
  rw [HomologicalComplex.eulerChar_eq_sum_finSet_of_finrankSupport_subset C (range N)]
  · simp
  · intro i hi
    by_contra hiN
    simp only [coe_range, Set.mem_Iio, not_lt] at hiN
    have : Subsingleton (C.X i) := hN i hiN
    exact hi finrank_zero_of_subsingleton

end Mathlib

end DeJongAlterations.StableModification.CurvesField.Genus
