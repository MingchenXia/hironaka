/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DeJongAlterations.StableModification.Valuation.Analytic.Schauder

/-!
# Temkin's Proposition 6.2.4 for type 2 fields in characteristic `p`

Let `k` be an algebraically closed non-archimedean field of characteristic `p` and `L ⊇ k` a
non-archimedean field. Let `U ⊆ L` be such that the `k`-span of
`B = {1} ⊔ U ⊔ U^p ⊔ U^{p²} ⊔ ⋯` is dense in `L` and every element of `span_k U` is orthogonal to
`L^p`. Then every special coset `b + S_{a,s}(L)` contains a minimal element, which lies in
`span_k U` and has absolute value `s` (`exists_isMinimalInCoset_of_dense_span`). By Temkin's
Proposition 6.2.5 (`IsGaussGenerator.exists_frobeniusFamily_isOrthonormalSchauderBasis`) such a
`U` exists for every finite unramified extension `L` of a type 2 field `K = \widehat{k(z)}`
(`IsGaussGenerator.exists_isMinimalInCoset`). This is the type 2 case of Temkin, *Stable
modification of relative curves*, J. Algebraic Geom. 19 (2010), Proposition 6.2.4
(`semi-stable.tex`, lines 3723–3728; proof lines 3951–3964), for special cosets.

The proof follows Temkin: an element of the dense span of `B` in the coset is reduced, monomial by
monomial, to an element of `span_k U` (`exists_smul_frobeniusFamily_sub_mem_range_asMap`: the
monomial `c u^{p^{j+1}}` is congruent to `a c^{1/p} u^{p^j}` modulo `℘_a(L)`, and constants lie in
`℘_a(k)`), and an element of `span_k U` is orthogonal to `L^p`, hence minimal
(`IsSpecialCoset.isMinimalInCoset_of_orthogonal`). Temkin states the proposition for all critical
cosets; his reduction step needs `a ∈ k`, which holds for special cosets (`a ∈ {0, 1}`), the only
ones used later.

## Main results

* `exists_smul_pow_sub_mem_range_asMap`, `exists_smul_frobeniusFamily_sub_mem_range_asMap`,
  `exists_mem_span_sub_eq_asMap`: reduction to `span_k U`.
* `exists_isMinimalInCoset_of_dense_span`: **Temkin, Proposition 6.2.4, type 2**, abstract form.
* `IsGaussGenerator.exists_isMinimalInCoset`: the same for finite unramified extensions of a
  Gauss generator.

## References

Blueprint `sm-val-onedim-type2.tex`: `lem:sm-an-type2-reduction`, `prop:sm-an-type2-critmin`.
-/

noncomputable section

open IsLocalRing Polynomial Module

namespace DeJongAlterations.StableModification.Valuation.Analytic

section Reduction

variable {k L : Type*} [NormedField k] [IsAlgClosed k] [NormedField L] [NormedAlgebra k L]
  {p : ℕ} [hp : Fact p.Prime] [CharP k p]

/-- **Reduction of monomials, `p`-power part**: for `u ∈ U`, `c ∈ k` and `j : ℕ`, the monomial
`c u^{p^j}` is congruent modulo `℘_a(L)` to an element of `span_k U`. -/
theorem exists_smul_pow_sub_mem_range_asMap {U : Set L} (a₀ : k) {u : L} (hu : u ∈ U)
    (j : ℕ) (c : k) :
    ∃ v ∈ Submodule.span k U, ∃ γ : L, c • u ^ p ^ j - v = asMap p (algebraMap k L a₀) γ := by
  have : CharP L p := charP_of_injective_algebraMap (algebraMap k L).injective p
  induction j generalizing c with
  | zero =>
    refine ⟨c • u, Submodule.smul_mem _ _ (Submodule.subset_span hu), 0, ?_⟩
    rw [asMap_zero, pow_zero, pow_one, sub_self]
  | succ j ih =>
    obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq c hp.out.pos
    obtain ⟨v, hv, γ', hγ'⟩ := ih (a₀ * β)
    refine ⟨v, hv, β • u ^ p ^ j + γ', ?_⟩
    have hstep : asMap p (algebraMap k L a₀) (β • u ^ p ^ j) =
        c • u ^ p ^ (j + 1) - (a₀ * β) • u ^ p ^ j := by
      rw [asMap, smul_pow, hβ, pow_succ, pow_mul, mul_smul, Algebra.smul_def a₀]
    rw [asMap_add, hstep, ← hγ']
    abel

/-- **Reduction of monomials**: every monomial `c b`, `b ∈ {1} ⊔ U ⊔ U^p ⊔ ⋯`, is congruent
modulo `℘_a(L)` to an element of `span_k U`. -/
theorem exists_smul_frobeniusFamily_sub_mem_range_asMap (U : Set L) (a₀ : k) (c : k)
    (ι : Option (ℕ × U)) :
    ∃ v ∈ Submodule.span k U, ∃ γ : L,
      c • FunctionField.frobeniusFamily p U ι - v = asMap p (algebraMap k L a₀) γ := by
  rcases ι with _ | ⟨j, u⟩
  · -- constants lie in `℘_a(k)`
    obtain ⟨γ₀, hγ₀⟩ := IsAlgClosed.exists_root (X ^ p - C a₀ * X - C c) (by
      rw [sub_sub, degree_sub_eq_left_of_degree_lt] <;>
        rw [degree_X_pow]
      · exact Nat.cast_ne_zero.mpr hp.out.ne_zero
      · refine (degree_add_le _ _).trans_lt (max_lt ?_ ?_)
        · exact (degree_C_mul_X_le _).trans_lt (by exact_mod_cast hp.out.one_lt)
        · exact (degree_C_le).trans_lt (by exact_mod_cast hp.out.pos))
    have hγ : γ₀ ^ p - a₀ * γ₀ = c := by
      have := hγ₀
      simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_mul, eval_C] at this
      linear_combination this
    refine ⟨0, zero_mem _, algebraMap k L γ₀, ?_⟩
    change c • (1 : L) - 0 = _
    rw [sub_zero, asMap, ← map_pow, ← map_mul, ← map_sub, hγ, Algebra.algebraMap_eq_smul_one]
  · exact exists_smul_pow_sub_mem_range_asMap a₀ u.2 j c

/-- **Reduction to the span of `U`** (Temkin, proof of Proposition 6.2.4, lines 3955–3960): every
element of `span_k ({1} ⊔ U ⊔ U^p ⊔ ⋯)` is congruent modulo `℘_a(L)` to an element of
`span_k U`. -/
theorem exists_mem_span_sub_eq_asMap (U : Set L) (a₀ : k) {x : L}
    (hx : x ∈ Submodule.span k (Set.range (FunctionField.frobeniusFamily p U))) :
    ∃ v ∈ Submodule.span k U, ∃ γ : L, x - v = asMap p (algebraMap k L a₀) γ := by
  have : CharP L p := charP_of_injective_algebraMap (algebraMap k L).injective p
  obtain ⟨l, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
  choose v hv γ hγ using fun ι ↦
    exists_smul_frobeniusFamily_sub_mem_range_asMap (p := p) U a₀ (l ι) ι
  refine ⟨∑ ι ∈ l.support, v ι, Submodule.sum_mem _ fun ι _ ↦ hv ι, ∑ ι ∈ l.support, γ ι, ?_⟩
  rw [Finsupp.sum, ← Finset.sum_sub_distrib]
  rw [show asMap p (algebraMap k L a₀) (∑ ι ∈ l.support, γ ι) =
      ∑ ι ∈ l.support, asMap p (algebraMap k L a₀) (γ ι) from
    map_sum (asMapHom (p := p) (algebraMap k L a₀)) γ l.support]
  exact Finset.sum_congr rfl fun ι _ ↦ hγ ι

/-- **Temkin, Proposition 6.2.4, type 2** (abstract form, special cosets). Let `U ⊆ L` be such that
the `k`-span of `{1} ⊔ U ⊔ U^p ⊔ ⋯` is dense in `L` and every element of `span_k U` is
orthogonal to `L^p`. Then every special coset `b + S_{a,s}(L)` contains a minimal element; it
lies in `span_k U` and has absolute value `s`. -/
theorem exists_isMinimalInCoset_of_dense_span [IsUltrametricDist L] (U : Set L)
    (hdense : Dense (Submodule.span k (Set.range (FunctionField.frobeniusFamily p U)) : Set L))
    (horth : ∀ u ∈ Submodule.span k U, ∀ c : L, ‖u‖ ≤ ‖u + c ^ p‖) {a b : L} {s : ℝ}
    (hsp : IsSpecialCoset p a s b) :
    ∃ v ∈ Submodule.span k U, IsMinimalInCoset p a s b v ∧ ‖v‖ = s := by
  have : CharP L p := charP_of_injective_algebraMap (algebraMap k L).injective p
  obtain ⟨a₀, rfl⟩ : ∃ a₀ : k, algebraMap k L a₀ = a := by
    rcases hsp.2 with rfl | ⟨rfl, -⟩
    · exact ⟨0, map_zero _⟩
    · exact ⟨1, map_one _⟩
  obtain ⟨u, huA, hu⟩ := exists_mem_memCoset_of_dense hdense
    (memCoset_self (a := algebraMap k L a₀) hsp.1.pos b)
  obtain ⟨v, hv, γ, hγ⟩ := exists_mem_span_sub_eq_asMap U a₀ huA
  have hvmem : MemCoset p (algebraMap k L a₀) s b v := by
    have := hu.sub_asMap γ
    rwa [← hγ, sub_sub_cancel] at this
  have hmin := hsp.isMinimalInCoset_of_orthogonal hvmem fun c ↦ horth v hv c
  exact ⟨v, hv, hmin, hsp.1.norm_eq_of_isMinimalInCoset hmin⟩

end Reduction

/-- **Temkin, Proposition 6.2.4, type 2.** Let `k` be algebraically closed of characteristic `p`,
`z` a Gauss generator of `K` over `k`, and `L/K` finite with `L` complete, `[L : K] ≤ [L̃ : K̃]` and
`L̃/K̃` separable. There is `U ⊆ L` as in Temkin's Proposition 6.2.5 (`{1} ⊔ U ⊔ U^p ⊔ ⋯` is an
orthonormal Schauder basis of `L` over `k`, and `span_k U` is orthogonal to `L^p`) such that every
special coset `b + S_{a,s}(L)` contains a minimal element, lying in `span_k U`, of absolute
value `s`. -/
theorem IsGaussGenerator.exists_isMinimalInCoset {k K L : Type*} [NormedField k]
    [IsUltrametricDist k] [IsAlgClosed k] [NormedField K] [IsUltrametricDist K] [NormedAlgebra k K]
    [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra k L]
    [NormedAlgebra K L] [IsScalarTower k K L] (p : ℕ) [Fact p.Prime] [CharP k p] {z : K}
    (hz : IsGaussGenerator k z) [FiniteDimensional K L] (hf : finrank K L ≤ inertiaDegree K L)
    [Algebra.IsSeparable (ResidueField (unitBall K)) (ResidueField (unitBall L))] :
    ∃ U : Set L, IsOrthonormalSchauderBasis k (FunctionField.frobeniusFamily p U) ∧
      (∀ u ∈ Submodule.span k U, ∀ c : L, ‖u‖ ≤ ‖u + c ^ p‖) ∧
      ∀ ⦃a b : L⦄ ⦃s : ℝ⦄, IsSpecialCoset p a s b →
        ∃ v ∈ Submodule.span k U, IsMinimalInCoset p a s b v ∧ ‖v‖ = s := by
  obtain ⟨U, hB, horth⟩ := hz.exists_frobeniusFamily_isOrthonormalSchauderBasis (L := L) p hf
  exact ⟨U, hB, horth, fun _ _ _ hsp ↦
    exists_isMinimalInCoset_of_dense_span U hB.dense_span horth hsp⟩

end DeJongAlterations.StableModification.Valuation.Analytic
