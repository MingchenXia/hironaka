import DeJongAlterations.StableModification.Valuation.Composition
import DeJongAlterations.StableModification.Valuation.Unramified

/-!
# The composition criterion for standard-unramified extensions

This file formalizes the composition criterion, Proposition 2.2.2 (`unramcrit2`) of M. Temkin,
*Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), §2.2
(`semi-stable.tex`, lines 2146–2175), in the **adapted form** of `PLAN-SM-VAL.md` (node V8,
simplification S10).

Setting: `l/k` is a field extension, `A'` a valuation subring of `l` with `A = A' ∩ k`, residue
fields `κ(A) → κ(A')`, and `B'` a valuation subring of `κ(A')` with `B = B' ∩ κ(A)`. The composed
valuation subrings are `C' = A' ∘ B'` of `l` and `C = C' ∩ k = A ∘ B` of `k`
(`comap_compose`).

* `IsStdUnramifiedGenerator.compose`: if `y` is a standard-unramified generator of `l/k` at
  `A'`, the reduction `f̄ ∈ κ(A)[X]` of its minimal polynomial `f` has coefficients in `B`, and
  `f̄'(ȳ)` is a unit of `B'`, then `y` is a standard-unramified generator of `l/k` at `C'`.
* `IsStdUnramifiedGenerator.compose_of_adapted`: the adapted form. If moreover `ȳ` is a unit of
  `B'` that is a standard-unramified generator of `κ(A')/κ(A)` at `B'`, and
  `f̄ = g̃ · X^m` with `g̃` the minimal polynomial of `ȳ` over `κ(A)`, then the hypotheses above
  hold, so `C'/C` is standard-unramified with the same generator `y`.

Temkin proves the general statement ("if `l/k` and `l̃/k̃` are unramified then so is the composed
extension") by checking flatness, `𝔫' = 𝔫C'` and finite presentation, the last via
Raynaud–Gruson [RG, 3.4.7] (flat and of finite type over a valuation ring implies finitely
presented). That theorem is not in Mathlib; the adapted form avoids it because every composition
in the proof of Theorem 2.1.8 is applied to a generator produced by decompletion with prescribed
residue (plan nodes M0–M2), which is adapted in the above sense. The general statement is not
formalized here.
-/

noncomputable section

open IsLocalRing Polynomial

namespace DeJongAlterations.StableModification.Valuation

variable {k l : Type*} [Field k] [Field l] [Algebra k l]
variable (A' : ValuationSubring l) (B' : ValuationSubring (ResidueField A'))

variable {A' B'}

/-- **Composition criterion** (Temkin, Proposition 2.2.2, in the form used for adapted
generators): let `y` be a standard-unramified generator of `l/k` at `A'`, with minimal polynomial
`f` over `A = A' ∩ k` and reduction `f̄ ∈ κ(A)[X]`. If the coefficients of `f̄` lie in
`B = B' ∩ κ(A)` and `f̄'(ȳ)` is a unit of `B'`, then `y` is a standard-unramified generator of
`l/k` at the composed valuation subring `C' = A' ∘ B'`. -/
theorem IsStdUnramifiedGenerator.compose {y : l} (hy : IsStdUnramifiedGenerator k A' y)
    (hcoeff : ∀ i, algebraMap (ResidueField (A'.comap (algebraMap k l))) (ResidueField A')
      (((minpoly (A'.comap (algebraMap k l)) y).map
        (residue (A'.comap (algebraMap k l)))).coeff i) ∈ B')
    (hunit : B'.valuation (aeval (residue A' ⟨y, hy.mem⟩)
      (derivative ((minpoly (A'.comap (algebraMap k l)) y).map
        (residue (A'.comap (algebraMap k l)))))) = 1) :
    IsStdUnramifiedGenerator k (StableModification.Valuation.compose A' B') y := by
  set A := A'.comap (algebraMap k l)
  refine ⟨hy.adjoin_eq_top, ?_, ?_⟩
  · -- the coefficients of `f` lie in `C = C' ∩ k`
    refine isIntegral_comap_of_coeff_mem _ hy.isIntegral_field fun i ↦ ?_
    rw [hy.minpoly_eq, coeff_map]
    set a := (minpoly A y).coeff i
    refine mem_compose.mpr ⟨a.2, ?_⟩
    have h := hcoeff i
    rw [coeff_map, residue_algebraMap_comap] at h
    exact h
  · -- `f'(y)` is a unit of `A'` whose residue is a unit of `B'`
    set a : A' := ⟨aeval y (derivative (minpoly k y)), hy.aeval_derivative_mem⟩
    change (StableModification.Valuation.compose A' B').valuation (a : l) = 1
    rw [valuation_compose_eq_one_iff]
    refine ⟨(A'.valuation_eq_one_iff a).mpr hy.valuation_aeval_derivative, ?_⟩
    have ha : a = aeval (⟨y, hy.mem⟩ : A') (derivative (minpoly A y)) := by
      apply Subtype.ext
      rw [coe_aeval_comap]
      exact hy.aeval_derivative_minpoly_comap.symm
    rw [ha, residue_aeval_comap, ← derivative_map]
    exact hunit

/-- **Composition criterion, adapted form** (plan `PLAN-SM-VAL.md`, node V8). Let `y` be a
standard-unramified generator of `l/k` at `A'` whose residue `ȳ` is a unit of `B'` and a
standard-unramified generator of `κ(A')/κ(A)` at `B'`. If the reduction of the minimal polynomial
of `y` over `A = A' ∩ k` is `g̃ · X^m`, with `g̃` the minimal polynomial of `ȳ` over `κ(A)`, then
`y` is a standard-unramified generator of `l/k` at the composed valuation subring `A' ∘ B'`. -/
theorem IsStdUnramifiedGenerator.compose_of_adapted {y : l} (hy : IsStdUnramifiedGenerator k A' y)
    (hres : IsStdUnramifiedGenerator (ResidueField (A'.comap (algebraMap k l))) B'
      (residue A' ⟨y, hy.mem⟩))
    (hunit : B'.valuation (residue A' ⟨y, hy.mem⟩) = 1)
    (hfac : ∃ m : ℕ, (minpoly (A'.comap (algebraMap k l)) y).map
        (residue (A'.comap (algebraMap k l))) =
      minpoly (ResidueField (A'.comap (algebraMap k l))) (residue A' ⟨y, hy.mem⟩) * X ^ m) :
    IsStdUnramifiedGenerator k (StableModification.Valuation.compose A' B') y := by
  set κ := ResidueField (A'.comap (algebraMap k l))
  set ybar := residue A' ⟨y, hy.mem⟩
  obtain ⟨m, hm⟩ := hfac
  refine hy.compose ?_ ?_
  · intro i
    rw [hm, coeff_mul_X_pow']
    split_ifs
    · rw [hres.minpoly_eq, coeff_map]
      exact ((minpoly (B'.comap (algebraMap κ (ResidueField A'))) ybar).coeff (i - m)).2
    · rw [map_zero]
      exact B'.zero_mem
  · rw [hm, derivative_mul, map_add, map_mul, map_mul, minpoly.aeval, zero_mul, add_zero,
      map_mul, map_pow, hres.valuation_aeval_derivative, aeval_X, map_pow, hunit, one_pow,
      one_mul]

end DeJongAlterations.StableModification.Valuation
