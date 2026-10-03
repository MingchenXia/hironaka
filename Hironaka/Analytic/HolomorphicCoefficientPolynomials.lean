/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
set_option autoImplicit false

/-!
# Polynomials with holomorphic coefficients

Tools for the local proper projection theorem for analytic sets (Gunning--Rossi, III.B;
Chirka, §3.7), where a Weierstrass polynomial `t^d + ∑_{k<d} a_k(z) t^k` and the
remainders of Weierstrass division are treated as polynomials in `t` whose coefficients
depend holomorphically on `z`.

* `norm_lt_of_weierstrass_root`: the roots of `t^d + ∑_{k<d} a_k t^k` lie in the disc of
  radius `ε ≤ 1` once every `‖a_k‖ < ε^d / d`.
-/

open Polynomial

namespace Hironaka.HolomorphicCoefficientPolynomials

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Root bound for Weierstrass-type polynomials.**  If `0 < ε ≤ 1` and every coefficient
satisfies `‖a_k‖ * d < ε ^ d`, every root `t` of `t^d + ∑_{k<d} a_k t^k` has `‖t‖ < ε`. -/
theorem norm_lt_of_weierstrass_root {d : ℕ} {a : ℕ → ℂ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ha : ∀ k < d, ‖a k‖ * d < ε ^ d) {t : ℂ}
    (ht : t ^ d + ∑ k ∈ Finset.range d, a k * t ^ k = 0) : ‖t‖ < ε := by
  by_contra hlt
  push Not at hlt
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp at ht
  have ht0 : 0 < ‖t‖ := hε.trans_le hlt
  -- `ε^(d-1) ‖t‖^k ≤ ‖t‖^(d-1)` for `k < d`
  have hpow : ∀ k < d, ε ^ (d - 1) * ‖t‖ ^ k ≤ ‖t‖ ^ (d - 1) := by
    intro k hkd
    calc ε ^ (d - 1) * ‖t‖ ^ k ≤ ε ^ (d - 1 - k) * ‖t‖ ^ k := by
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_of_le_one hε.le hε1 (Nat.sub_le _ _)) (by positivity)
      _ ≤ ‖t‖ ^ (d - 1 - k) * ‖t‖ ^ k := by gcongr
      _ = ‖t‖ ^ (d - 1) := by rw [← pow_add]; congr 1; omega
  have hsum : ‖t‖ ^ d = ‖∑ k ∈ Finset.range d, a k * t ^ k‖ := by
    rw [← norm_pow, eq_neg_of_add_eq_zero_left ht, norm_neg]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have key : ε ^ (d - 1) * ‖t‖ ^ d < ε ^ d * ‖t‖ ^ (d - 1) := by
    rw [hsum]
    calc ε ^ (d - 1) * ‖∑ k ∈ Finset.range d, a k * t ^ k‖
        ≤ ∑ k ∈ Finset.range d, ‖a k‖ * (ε ^ (d - 1) * ‖t‖ ^ k) := by
          refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans ?_
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun k _ => ?_
          rw [norm_mul, norm_pow]
          nlinarith [norm_nonneg (a k), pow_nonneg (norm_nonneg t) k,
            pow_nonneg hε.le (d - 1)]
      _ ≤ ∑ k ∈ Finset.range d, ‖a k‖ * ‖t‖ ^ (d - 1) :=
          Finset.sum_le_sum fun k hk =>
            mul_le_mul_of_nonneg_left (hpow k (Finset.mem_range.mp hk)) (norm_nonneg _)
      _ < ∑ k ∈ Finset.range d, ε ^ d / d * ‖t‖ ^ (d - 1) := by
          refine Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.mpr hd⟩ fun k hk => ?_
          have := ha k (Finset.mem_range.mp hk)
          have hlt' : ‖a k‖ < ε ^ d / d := by rw [lt_div_iff₀ hdR]; exact this
          exact mul_lt_mul_of_pos_right hlt' (pow_pos ht0 _)
      _ = ε ^ d * ‖t‖ ^ (d - 1) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          field_simp
  have hd1 : d = d - 1 + 1 := by omega
  have : ε ^ d * ‖t‖ ^ (d - 1) ≤ ε ^ (d - 1) * ‖t‖ ^ d := by
    rw [hd1, pow_succ, pow_succ, Nat.add_sub_cancel]
    have := mul_le_mul_of_nonneg_left hlt (mul_nonneg (pow_nonneg hε.le (d - 1))
      (pow_nonneg ht0.le (d - 1)))
    linarith
  linarith

end

end Hironaka.HolomorphicCoefficientPolynomials
