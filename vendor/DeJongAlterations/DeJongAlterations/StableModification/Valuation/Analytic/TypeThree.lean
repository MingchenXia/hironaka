import DeJongAlterations.StableModification.Valuation.Analytic.Annulus

/-!
# Temkin's Proposition 6.2.4 for type 3 fields in characteristic `p`

Let `k` be an algebraically closed non-archimedean field of characteristic `p` and `T` an annulus
generator of a non-archimedean field `K ⊇ k` (`IsAnnulusGenerator`). This file proves the type 3
case of Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010),
Proposition 6.2.4 (`semi-stable.tex`, lines 3723–3728; proof lines 3951–3964), for `K` itself
and for special cosets: every special coset `b + S_{a,s}(K)` contains an element of minimal
absolute value, which lies in the `k`-span of the `T^e` with `p ∤ e`.

The proof follows Temkin: a Laurent polynomial representative of the coset is reduced, monomial
by monomial, to one with exponents prime to `p` (`exists_smul_zpow_sub_mem_range_asMap`; the
monomial `c T^{pj}` is congruent to `a c^{1/p} T^j` modulo `℘_a(K)`, and constants lie in
`℘_a(k)`), and such an element is orthogonal to `K ^ p`
(`IsAnnulusGenerator.norm_le_norm_add_pow_char`), hence minimal
(`IsSpecialCoset.isMinimalInCoset_of_orthogonal`).

## Main results

* `exists_smul_zpow_sub_mem_range_asMap`: reduction of monomials.
* `exists_mem_span_sub_mem_range_asMap`: reduction of Laurent polynomials.
* `IsAnnulusGenerator.exists_isMinimalInCoset`: **Temkin, Proposition 6.2.4, type 3**.

## References

Blueprint `sm-val-onedim-t34.tex`: `lem:sm-an-annulus-reduction`, `prop:sm-an-type3-critmin`.
-/

noncomputable section

open Polynomial

namespace DeJongAlterations.StableModification.Valuation

variable {k K : Type*} [NormedField k] [IsAlgClosed k] [NormedField K] [NormedAlgebra k K]
  {p : ℕ} [Fact p.Prime] [CharP k p]

/-- **Reduction of monomials**: for `a ∈ k`, every monomial `c Tⁱ` is congruent modulo
`℘_a(K)` to a monomial `c' T^{i'}` with `p ∤ i'`. -/
theorem exists_smul_zpow_sub_mem_range_asMap (T : K) (a₀ : k) (c : k) (i : ℤ) :
    ∃ c' : k, ∃ i' : ℤ, ¬ (p : ℤ) ∣ i' ∧
      c • T ^ i - c' • T ^ i' ∈ Set.range (asMap p (algebraMap k K a₀)) := by
  have hp := (Fact.out : p.Prime)
  have : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  have hp1 : ¬ (p : ℤ) ∣ 1 := by
    rw [Int.natCast_dvd_ofNat]
    exact hp.not_dvd_one
  induction hn : i.natAbs using Nat.strong_induction_on generalizing c i with
  | _ n ih =>
    by_cases hpi : (p : ℤ) ∣ i
    · by_cases hi0 : i = 0
      · -- constants lie in `℘_a(k)`
        subst hi0
        obtain ⟨γ₀, hγ₀⟩ := IsAlgClosed.exists_root (X ^ p - C a₀ * X - C c) (by
          rw [sub_sub, degree_sub_eq_left_of_degree_lt] <;>
            rw [degree_X_pow]
          · exact Nat.cast_ne_zero.mpr hp.ne_zero
          · refine (degree_add_le _ _).trans_lt (max_lt ?_ ?_)
            · exact (degree_C_mul_X_le _).trans_lt (by exact_mod_cast hp.one_lt)
            · exact (degree_C_le).trans_lt (by exact_mod_cast hp.pos))
        refine ⟨0, 1, hp1, algebraMap k K γ₀, ?_⟩
        have hγ : γ₀ ^ p - a₀ * γ₀ = c := by
          have := hγ₀
          simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_mul, eval_C] at this
          linear_combination this
        rw [zpow_zero, zero_smul, sub_zero, Algebra.smul_def, mul_one, ← hγ, asMap]
        simp
      · -- `c T^{pj} ≡ a c^{1/p} T^j`
        obtain ⟨j, rfl⟩ := hpi
        have hj0 : j ≠ 0 := by rintro rfl; simp at hi0
        obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq c hp.pos
        have hlt : j.natAbs < n := by
          rw [← hn, Int.natAbs_mul, Int.natAbs_natCast]
          have : 0 < j.natAbs := Int.natAbs_pos.mpr hj0
          nlinarith [hp.two_le]
        obtain ⟨c', i', hi', γ', hγ'⟩ := ih _ hlt (a₀ * β) j rfl
        refine ⟨c', i', hi', β • T ^ j + γ', ?_⟩
        rw [asMap_add, hγ']
        have hstep : asMap p (algebraMap k K a₀) (β • T ^ j) =
            c • T ^ ((p : ℤ) * j) - (a₀ * β) • T ^ j := by
          rw [asMap, _root_.smul_pow, ← zpow_natCast (T ^ j) p, ← zpow_mul, hβ, mul_comm j,
            mul_smul, Algebra.smul_def a₀, ← smul_eq_mul]
        rw [hstep]
        abel
    · exact ⟨c, i, hpi, 0, by simp⟩

/-- **Reduction of Laurent polynomials**: every Laurent polynomial `u` in `T` is congruent
modulo `℘_a(K)` to an element of the `k`-span of the `T^e` with `p ∤ e`. -/
theorem exists_mem_span_sub_mem_range_asMap [IsUltrametricDist K] (T : K) (a₀ : k) {u : K}
    (hu : u ∈ laurentSubring k T) :
    ∃ v ∈ Submodule.span k ((fun i : ℤ => T ^ i) '' {e | ¬ (p : ℤ) ∣ e}),
      ∃ γ : K, u - v = asMap p (algebraMap k K a₀) γ := by
  have : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  obtain ⟨f, rfl⟩ := mem_laurentSubring_iff.mp hu
  choose c' i' hi' γ hγ using fun i => exists_smul_zpow_sub_mem_range_asMap (p := p) T a₀ (f i) i
  refine ⟨∑ i ∈ f.support, c' i • T ^ i' i, ?_, ∑ i ∈ f.support, γ i, ?_⟩
  · exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i' i, hi' i, rfl⟩)
  · rw [laurent_apply, ← Finset.sum_sub_distrib]
    rw [show asMap p (algebraMap k K a₀) (∑ i ∈ f.support, γ i) =
        ∑ i ∈ f.support, asMap p (algebraMap k K a₀) (γ i) from
      map_sum (asMapHom (p := p) (algebraMap k K a₀)) γ f.support]
    exact Finset.sum_congr rfl fun i _ => (hγ i).symm

/-- **Temkin, Proposition 6.2.4, type 3** (characteristic `p`): if `T` is an annulus generator of
`K` over `k`, every special coset `b + S_{a,s}(K)` contains an element of minimal absolute value
(of absolute value `s`, by `IsCriticalCoset.norm_eq_of_isMinimalInCoset`), which lies in the
`k`-span of the `T^e` with `p ∤ e`. -/
theorem IsAnnulusGenerator.exists_isMinimalInCoset [IsUltrametricDist K] {T : K}
    (hT : IsAnnulusGenerator k T) {a b : K} {s : ℝ} (hsp : IsSpecialCoset p a s b) :
    ∃ v ∈ Submodule.span k ((fun i : ℤ => T ^ i) '' {e | ¬ (p : ℤ) ∣ e}),
      IsMinimalInCoset p a s b v := by
  have : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  obtain ⟨a₀, rfl⟩ : ∃ a₀ : k, algebraMap k K a₀ = a := by
    rcases hsp.2 with rfl | ⟨rfl, -⟩
    · exact ⟨0, map_zero _⟩
    · exact ⟨1, map_one _⟩
  obtain ⟨u, huL, hu⟩ :=
    exists_mem_memCoset_of_dense hT.dense_laurent
      (memCoset_self (a := algebraMap k K a₀) hsp.1.pos b)
  obtain ⟨v, hv, γ, hγ⟩ := exists_mem_span_sub_mem_range_asMap (p := p) T a₀ huL
  have hvmem : MemCoset p (algebraMap k K a₀) s b v := by
    have := hu.sub_asMap γ
    rwa [← hγ, sub_sub_cancel] at this
  exact ⟨v, hv, hsp.isMinimalInCoset_of_orthogonal hvmem
    fun c => hT.norm_le_norm_add_pow_char hv c⟩

end DeJongAlterations.StableModification.Valuation
