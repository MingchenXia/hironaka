/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.OrderOfElement

/-!
# Artin–Schreier normal form

Let `M` be a field and `L/M` a Galois extension of prime degree `p`, with `L` of characteristic
`p`. This file proves that `L = M(α)` with `α ^ p - α ∈ M`; more precisely, for every
`σ ≠ 1` in `Gal(L/M)` there is `α` with `σ α = α + 1`. Mathlib has no Artin–Schreier theory; the
proof here uses the linear independence of the characters `σ ^ i` (Dedekind–Artin) to find an
element of trace one, and the classical formula `β = ∑ i σ^i(θ)`.

This is the normal form used for the degree-`p` Galois steps of the towers of `Towers.lean`, in
place of Temkin's disc argument (M. Temkin, *Stable modification of relative curves*,
J. Algebraic Geom. 19 (2010), proof of Proposition 6.1.4, `semi-stable.tex` lines 3569–3636;
plan simplification S6 of `PLAN-SM-VAL.md`).

## Main results

* `orderOf_eq_of_finrank_eq_prime`: in a Galois extension of prime degree `p` every `σ ≠ 1` has
  order `p`.
* `exists_sum_pow_apply_eq_one`: there is `θ` with `∑_{i < p} σ ^ i θ = 1`.
* `exists_apply_eq_add_one`: there is `α` with `σ α = α + 1`.
* `artinSchreier_of_apply_eq_add_one`: every such `α` satisfies `α ∉ M`, `α ^ p - α ∈ M` and
  `L = M(α)`.
* `exists_artinSchreier_generator`: `L = M(α)` with `α ∉ M` and `α ^ p - α ∈ M`.

## References

Blueprint chapter `sm-val-ramification.tex`: `lem:sm-an-artin-schreier`.
-/

open IntermediateField

namespace DeJongAlterations.StableModification.Valuation.Analytic

variable {M L : Type*} [Field M] [Field L] [Algebra M L] [FiniteDimensional M L] [IsGalois M L]

/-- In a Galois extension of prime degree `p`, every nontrivial automorphism has order `p`. -/
theorem orderOf_eq_of_finrank_eq_prime {p : ℕ} (hp : p.Prime) (hdeg : Module.finrank M L = p)
    {σ : L ≃ₐ[M] L} (hσ : σ ≠ 1) : orderOf σ = p := by
  have hcard : Nat.card (L ≃ₐ[M] L) = p := by rw [IsGalois.card_aut_eq_finrank, hdeg]
  have hdvd : orderOf σ ∣ p := hcard ▸ orderOf_dvd_natCard σ
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hσ
  · exact h

omit [FiniteDimensional M L] [IsGalois M L] in
/-- The sum `∑_{i < n} σ ^ i y` is fixed by `σ` if `σ ^ n = 1`. -/
theorem apply_sum_pow_apply_eq (σ : L ≃ₐ[M] L) {n : ℕ} (hn : σ ^ n = 1) (y : L) :
    σ (∑ i ∈ Finset.range n, (σ ^ i) y) = ∑ i ∈ Finset.range n, (σ ^ i) y := by
  have h1 := Finset.sum_range_succ' (fun i => (σ ^ i) y) n
  have h2 := Finset.sum_range_succ (fun i => (σ ^ i) y) n
  rw [map_sum]
  have h3 : ∑ i ∈ Finset.range n, σ ((σ ^ i) y) = ∑ i ∈ Finset.range n, (σ ^ (i + 1)) y :=
    Finset.sum_congr rfl fun i _ => by rw [pow_succ', AlgEquiv.mul_apply]
  rw [h3]
  simp only [hn, pow_zero, AlgEquiv.one_apply] at h1 h2
  exact add_right_cancel (h1.symm.trans h2)

omit [IsGalois M L] in
/-- **An element of trace one**: if `σ` has order `p` there is `θ` with
`∑_{i < p} σ ^ i θ = 1` (Dedekind–Artin independence of characters). -/
theorem exists_sum_pow_apply_eq_one {p : ℕ} {σ : L ≃ₐ[M] L} (hσ : orderOf σ = p) :
    ∃ θ : L, ∑ i ∈ Finset.range p, (σ ^ i) θ = 1 := by
  classical
  have hσp : σ ^ p = 1 := hσ ▸ pow_orderOf_eq_one σ
  -- the characters `σ ^ i`, `i < p`, are distinct
  set f : Fin p → (L →* L) := fun i => ((σ ^ (i : ℕ) : L ≃ₐ[M] L) : L →* L)
  have hfinj : Function.Injective f := by
    intro i j hij
    have h1 : (σ ^ (i : ℕ) : L ≃ₐ[M] L) = σ ^ (j : ℕ) := by
      ext x
      exact DFunLike.congr_fun hij x
    have := pow_injOn_Iio_orderOf (x := σ) (by rw [hσ]; exact i.2) (by rw [hσ]; exact j.2) h1
    exact Fin.ext this
  have hli := (linearIndependent_monoidHom L L).comp f hfinj
  have hne : (∑ i : Fin p, (1 : L) • ((f i : L →* L) : L → L)) ≠ 0 := by
    intro h0
    have := (Fintype.linearIndependent_iff.mp hli) (fun _ => 1) h0
    have hp : 0 < p := hσ ▸ orderOf_pos σ
    exact one_ne_zero (this ⟨0, hp⟩)
  obtain ⟨θ, hθ⟩ := Function.ne_iff.mp hne
  have hsum : ∑ i ∈ Finset.range p, (σ ^ i) θ ≠ 0 := by
    simp only [one_smul, Finset.sum_apply, Pi.zero_apply] at hθ
    rwa [← Fin.sum_univ_eq_sum_range (fun i => (σ ^ i) θ)]
  set t := ∑ i ∈ Finset.range p, (σ ^ i) θ with ht_def
  have hσt : ∀ i : ℕ, (σ ^ i) t = t := by
    intro i
    induction i with
    | zero => simp
    | succ n ih => rw [pow_succ', AlgEquiv.mul_apply, ih, ht_def, apply_sum_pow_apply_eq σ hσp]
  refine ⟨θ / t, ?_⟩
  simp only [map_div₀, hσt]
  rw [← Finset.sum_div, ← ht_def, div_self hsum]

omit [IsGalois M L] in
/-- **Artin–Schreier**: if `σ` has order `p = char L`, there is `α` with `σ α = α + 1`. -/
theorem exists_apply_eq_add_one (p : ℕ) [CharP L p] {σ : L ≃ₐ[M] L} (hσ : orderOf σ = p) :
    ∃ α : L, σ α = α + 1 := by
  obtain ⟨θ, hθ⟩ := exists_sum_pow_apply_eq_one hσ
  have hσp : σ ^ p = 1 := hσ ▸ pow_orderOf_eq_one σ
  have hp : 0 < p := hσ ▸ orderOf_pos σ
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  set β := ∑ i ∈ Finset.range (q + 1), (i : L) * (σ ^ i) θ with hβ_def
  have hq : (q : L) + 1 = 0 := by
    have := CharP.cast_eq_zero L (q + 1)
    push_cast at this
    exact this
  have hσβ : σ β = β - 1 := by
    have h1 : σ β = ∑ i ∈ Finset.range (q + 1), (i : L) * (σ ^ (i + 1)) θ := by
      rw [hβ_def, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_natCast, pow_succ', AlgEquiv.mul_apply]
    have h2 := Finset.sum_range_succ (fun i => (i : L) * (σ ^ (i + 1)) θ) q
    have h3 := Finset.sum_range_succ' (fun i => (i : L) * (σ ^ i) θ) q
    have h4 := Finset.sum_range_succ' (fun i => (σ ^ i) θ) q
    rw [hσp, AlgEquiv.one_apply] at h2
    simp only [pow_zero, AlgEquiv.one_apply, Nat.cast_zero, zero_mul, add_zero] at h3 h4
    rw [h1, h2, hβ_def, h3, ← hθ, h4]
    push_cast
    simp only [add_mul, one_mul, Finset.sum_add_distrib]
    linear_combination θ * hq
  exact ⟨-β, by rw [map_neg, hσβ]; ring⟩

/-- **Artin–Schreier generators**: in a Galois extension of prime degree `p = char L`, if
`σ α = α + 1` for some `σ`, then `α ∉ M`, `α ^ p - α ∈ M` and `L = M(α)`. -/
theorem artinSchreier_of_apply_eq_add_one (p : ℕ) [hp : Fact p.Prime] [CharP L p]
    (hdeg : Module.finrank M L = p) {σ : L ≃ₐ[M] L} {α : L} (hα : σ α = α + 1) :
    α ∉ (algebraMap M L).range ∧ α ^ p - α ∈ (algebraMap M L).range ∧ M⟮α⟯ = ⊤ := by
  have hcard : Nat.card (L ≃ₐ[M] L) = p := by rw [IsGalois.card_aut_eq_finrank, hdeg]
  have hσ : σ ≠ 1 := by
    rintro rfl
    rw [AlgEquiv.one_apply] at hα
    have : (1 : L) = 0 := by linear_combination -hα
    exact one_ne_zero this
  have hord := orderOf_eq_of_finrank_eq_prime hp.out hdeg hσ
  have hαM : α ∉ (algebraMap M L).range := by
    rintro ⟨c, rfl⟩
    rw [AlgEquiv.commutes] at hα
    have : (1 : L) = 0 := by linear_combination -hα
    exact one_ne_zero this
  refine ⟨hαM, ?_, ?_⟩
  · -- `α ^ p - α` is fixed by `σ`, hence by the whole Galois group
    have hfix : σ (α ^ p - α) = α ^ p - α := by
      rw [map_sub, map_pow, hα, add_pow_char]
      ring
    have hzp : Subgroup.zpowers σ = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [Nat.card_zpowers, hord, hcard]
    have hstab : Subgroup.zpowers σ ≤ MulAction.stabilizer (L ≃ₐ[M] L) (α ^ p - α) := by
      rw [Subgroup.zpowers_le]
      exact hfix
    have hall : ∀ τ : L ≃ₐ[M] L, τ (α ^ p - α) = α ^ p - α := fun τ =>
      hstab (hzp ▸ Subgroup.mem_top τ)
    obtain ⟨c, hc⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (α ^ p - α)).mpr hall
    exact ⟨c, hc⟩
  · -- `[M(α) : M]` divides `p` and is not `1`
    have hdvd : Module.finrank M M⟮α⟯ ∣ p := by
      rw [← hdeg]
      exact ⟨_, (Module.finrank_mul_finrank M M⟮α⟯ L).symm⟩
    have hne1 : Module.finrank M M⟮α⟯ ≠ 1 := by
      rw [Ne, IntermediateField.finrank_eq_one_iff, adjoin_simple_eq_bot_iff, mem_bot]
      exact fun ⟨c, hc⟩ => hαM ⟨c, hc⟩
    rcases hp.out.eq_one_or_self_of_dvd _ hdvd with h | h
    · exact absurd h hne1
    · exact eq_of_le_of_finrank_eq le_top (by rw [finrank_top', h, hdeg])

/-- **Artin–Schreier normal form**: a Galois extension `L/M` of prime degree `p = char L` is
generated by an element `α ∉ M` with `α ^ p - α ∈ M`. -/
theorem exists_artinSchreier_generator (p : ℕ) [hp : Fact p.Prime] [CharP L p]
    (hdeg : Module.finrank M L = p) :
    ∃ α : L, α ∉ (algebraMap M L).range ∧ α ^ p - α ∈ (algebraMap M L).range ∧ M⟮α⟯ = ⊤ := by
  have hcard : Nat.card (L ≃ₐ[M] L) = p := by rw [IsGalois.card_aut_eq_finrank, hdeg]
  have : Nontrivial (L ≃ₐ[M] L) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    exact hp.out.one_lt
  obtain ⟨σ, hσ⟩ := exists_ne (1 : L ≃ₐ[M] L)
  obtain ⟨α, hα⟩ := exists_apply_eq_add_one p (orderOf_eq_of_finrank_eq_prime hp.out hdeg hσ)
  exact ⟨α, artinSchreier_of_apply_eq_add_one p hdeg hα⟩

end DeJongAlterations.StableModification.Valuation.Analytic
