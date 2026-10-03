/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.HolomorphicGermWeierstrassPreparation
import Hironaka.Analytic.HolomorphicCoefficientPolynomials
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
set_option autoImplicit false

/-!
# Local proper projection along a Weierstrass direction

Source: Gunning--Rossi, *Analytic functions of several complex variables*, III.B
(Theorem 1, the elimination step); Chirka, *Complex analytic sets*, §3.7.  A step of the
local parametrization of analytic sets, the missing input behind
`AnalyticIrreducibleComponents.eq_dim_of_regularAtDim`.

Let `A = {g_1 = … = g_s = 0}` near `0 ∈ E × ℂ` and let `G` vanish on `A` near `0`, with
`G (0, t) = t^d u(t)`, `u(0) ≠ 0`.  Then there are `δ, ε > 0` such that over the ball
`‖z‖ < δ` the part of `A` in `‖t‖ < ε` stays in `‖t‖ < ε/2` (the projection is proper),
and its projection `{z | ∃ t, ‖t‖ < ε, (z, t) ∈ A}` is the common zero set of finitely
many functions holomorphic on the ball.

## Proof

Weierstrass preparation turns `G` into `W = t^d + ∑_{k<d} a_k(z) t^k` (up to a unit), and Weierstrass division by
`W` writes `g_j = Q_j W + ρ_j` with `ρ_j` a polynomial in `t` of degree `< d` with holomorphic coefficients. For
small `z` all roots of `W(z, ·)` are small (`norm_lt_of_weierstrass_root`), so `(z, t) ∈ A` with `‖t‖ < ε` iff `t`
is a common root of `W(z, ·)` and all `ρ_j(z, ·)`. Such a common root exists iff the resultants `Res_{d,d}(W(z, ·),
∑_j l^j ρ_j(z, ·))` vanish for `l = 0, …, d s`, and these are holomorphic in `z` (`differentiableOn_resultant_map`).
-/

open Filter Topology Polynomial Metric

namespace Hironaka.AnalyticProjectionWeierstrass

open HolomorphicCoefficientPolynomials

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The Weierstrass polynomial `t^d + ∑_{k<d} a_k(z) t^k` as a function on `E × ℂ`. -/
def weierstrassFun (d : ℕ) (a : ℕ → E → ℂ) (x : E × ℂ) : ℂ :=
  x.2 ^ d + ∑ k ∈ Finset.range d, a k x.1 * x.2 ^ k

/-- `∑_{k<d} c_k X^k` has degree `< d`. -/
theorem degree_sum_range_lt {R : Type*} [Semiring R] (d : ℕ) (c : ℕ → R) :
    (∑ k ∈ Finset.range d, C (c k) * X ^ k).degree < (d : WithBot ℕ) := by
  rw [Finset.sum_range (fun k => C (c k) * X ^ k)]
  exact degree_sum_fin_lt (fun i : Fin d => c i)

/-- `X^d + ∑_{k<d} c_k X^k` is monic of degree `d`. -/
theorem monic_X_pow_add_sum {R : Type*} [Semiring R] [Nontrivial R] (d : ℕ) (c : ℕ → R) :
    (X ^ d + ∑ k ∈ Finset.range d, C (c k) * X ^ k).Monic ∧
      (X ^ d + ∑ k ∈ Finset.range d, C (c k) * X ^ k).natDegree = d := by
  refine ⟨monic_X_pow_add (degree_sum_range_lt d c), ?_⟩
  rw [natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]
  exact degree_sum_range_lt d c

end

end Hironaka.AnalyticProjectionWeierstrass
