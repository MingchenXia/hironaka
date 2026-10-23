import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.CharP.Algebra
import DeJongAlterations.StableModification.Valuation.Analytic.TypeFour.Basic

/-!
# Hasse derivatives and the Hasse–Cauchy bound

Let `k` be an algebraically closed field with a non-archimedean absolute value and `K` a
non-archimedean valued field containing `k` isometrically. This file proves the
**Hasse–Cauchy bound** (a new ingredient replacing Temkin's completed tensor products
`K ⊗̂_k l ≅ l{r⁻¹w}` in the proofs of Lemmas 6.2.8 and 6.2.9 of Temkin, *Stable modification of
relative curves*, J. Algebraic Geom. 19 (2010), `semi-stable.tex`, lines 3843–3949): if
`0 ≤ r ≤ ‖z - a‖` for all `a ∈ k`, then for every `g ∈ k[X]` and `i : ℕ`,
`‖(D⁽ⁱ⁾ g)(z)‖ * r ^ i ≤ ‖g(z)‖`, where `D⁽ⁱ⁾ = Polynomial.hasseDeriv i`.

In characteristic `p` it also studies the additive operators
`Λ_N(f) = ∑_{n ≤ N} (D^{(pⁿ)} f) ^ (p ^ (N - n))` (`hasseLambda`), the substitute (without
`p`-th roots) for Temkin's element `b̄ = b̄₁ + b̄_p^{1/p} + ⋯` (line 3919), and proves Temkin's
**Lemma 6.2.8** in characteristic `p`: a type 4 generator has no `p`-th root in `K`.

## Main results

* `hasseDeriv_X_sub_C_mul`: Leibniz rule for a linear factor.
* `norm_aeval_hasseDeriv_mul_pow_le`: the Hasse–Cauchy bound.
* `hasseDeriv_mul_pow_char`, `hasseDeriv_pow_char_of_not_dvd`: Hasse derivatives of `p`-th
  powers in characteristic `p`.
* `hasseLambda_add`, `hasseLambda_sub`, `hasseLambda_pow_char_sub` (`Λ_N(c ^ p - c) =
  -D^{(p^N)} c`), `hasseLambda_eq_pow`, `norm_aeval_hasseLambda_mul_le`: properties of `Λ_N`.
* `natDegree_hasseLambda_log`, `leadingCoeff_hasseLambda_log`: leading term of `Λ_{N₀}(g)` for
  `N₀ = ⌊log_p deg g⌋`, `p ∤ deg g`.
* `IsTypeFourGenerator.pow_char_ne`: **Temkin, Lemma 6.2.8** (characteristic `p`).

## References

Blueprint `sm-val-onedim-t34.tex`: `lem:sm-an-hasse-cauchy`, `lem:sm-an-hasse-frobenius`,
`def:sm-an-hasse-lambda`, `lem:sm-an-hasse-lambda`, `lem:sm-an-hasse-lambda-degree`,
`lem:sm-an-no-pth-root`.
-/

noncomputable section

open Polynomial

namespace DeJongAlterations.StableModification.Valuation

/-! ### The Hasse–Cauchy bound -/

section Cauchy

variable {k : Type*} [Field k]

/-- Leibniz rule for a linear factor:
`D⁽ʲ⁺¹⁾((X - a) h) = (X - a) D⁽ʲ⁺¹⁾ h + D⁽ʲ⁾ h`. -/
theorem hasseDeriv_X_sub_C_mul (a : k) (h : k[X]) (j : ℕ) :
    hasseDeriv (j + 1) ((X - C a) * h) = (X - C a) * hasseDeriv (j + 1) h + hasseDeriv j h := by
  rw [hasseDeriv_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ',
    Finset.sum_range_succ']
  have h2 : ∀ m, hasseDeriv (m + 1 + 1) (X - C a) = 0 := fun m => by
    rw [map_sub, hasseDeriv_X (m + 1 + 1) (by omega), hasseDeriv_C (m + 1 + 1) a (by omega),
      sub_zero]
  simp only [h2, zero_mul, Finset.sum_const_zero, zero_add, hasseDeriv_zero', hasseDeriv_one',
    derivative_sub, derivative_X, derivative_C, sub_zero, one_mul, Nat.sub_zero,
    Nat.add_sub_cancel]
  ring

end Cauchy

section CauchyBound

variable {k K : Type*} [NormedField k] [IsAlgClosed k] [NormedField K] [IsUltrametricDist K]
  [NormedAlgebra k K]

/-- **Hasse–Cauchy bound.** If `0 ≤ r ≤ ‖z - a‖` for every `a ∈ k`, then
`‖(D⁽ⁱ⁾ g)(z)‖ * r ^ i ≤ ‖g(z)‖` for all `g ∈ k[X]` and `i : ℕ`. -/
theorem norm_aeval_hasseDeriv_mul_pow_le {z : K} {r : ℝ} (hr0 : 0 ≤ r)
    (hr : ∀ a : k, r ≤ ‖z - algebraMap k K a‖) (g : k[X]) (i : ℕ) :
    ‖aeval z (hasseDeriv i g)‖ * r ^ i ≤ ‖aeval z g‖ := by
  induction g using induction_on_X_sub_C_mul generalizing i with
  | hC c =>
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp
    · rw [hasseDeriv_C i c hi]
      simp
  | hmul a g ih =>
    rcases i with _ | j
    · simp
    have e : aeval z ((X - C a) * hasseDeriv (j + 1) g + hasseDeriv j g) =
        (z - algebraMap k K a) * aeval z (hasseDeriv (j + 1) g) + aeval z (hasseDeriv j g) := by
      simp
    have e' : ‖aeval z ((X - C a) * g)‖ = ‖z - algebraMap k K a‖ * ‖aeval z g‖ := by
      simp [norm_mul]
    rw [hasseDeriv_X_sub_C_mul, e, e']
    have hrp : 0 ≤ r ^ (j + 1) := pow_nonneg hr0 _
    calc ‖(z - algebraMap k K a) * aeval z (hasseDeriv (j + 1) g) + aeval z (hasseDeriv j g)‖ *
          r ^ (j + 1)
        ≤ max (‖z - algebraMap k K a‖ * ‖aeval z (hasseDeriv (j + 1) g)‖)
            ‖aeval z (hasseDeriv j g)‖ * r ^ (j + 1) := by
          refine mul_le_mul_of_nonneg_right ?_ hrp
          rw [← norm_mul]
          exact IsUltrametricDist.norm_add_le_max _ _
      _ = max (‖z - algebraMap k K a‖ * (‖aeval z (hasseDeriv (j + 1) g)‖ * r ^ (j + 1)))
            (‖aeval z (hasseDeriv j g)‖ * r ^ j * r) := by
          rw [max_mul_of_nonneg _ _ hrp, pow_succ]
          ring_nf
      _ ≤ max (‖z - algebraMap k K a‖ * ‖aeval z g‖) (‖aeval z g‖ * r) :=
          max_le_max (mul_le_mul_of_nonneg_left (ih (j + 1)) (norm_nonneg _))
            (mul_le_mul_of_nonneg_right (ih j) hr0)
      _ ≤ ‖z - algebraMap k K a‖ * ‖aeval z g‖ := by
          refine max_le le_rfl ?_
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right (hr a) (norm_nonneg _)

end CauchyBound

/-! ### Hasse derivatives of `p`-th powers -/

section Frobenius

variable {k : Type*} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p]

theorem eval_hasseDeriv_pow_char (c : k[X]) (j : ℕ) (x : k) :
    (hasseDeriv j (c ^ p)).eval x =
      if p ∣ j then ((hasseDeriv (j / p) c).eval x) ^ p else 0 := by
  rw [← taylor_coeff, taylor_pow, ← map_frobenius_expand, coeff_map,
    coeff_expand (Fact.out : p.Prime).pos]
  split_ifs
  · rw [taylor_coeff, frobenius_def]
  · exact map_zero _

variable [Infinite k]

/-- In characteristic `p`, `D^{(p j)}(c ^ p) = (D^{(j)} c) ^ p`. -/
theorem hasseDeriv_mul_pow_char (c : k[X]) (j : ℕ) :
    hasseDeriv (p * j) (c ^ p) = (hasseDeriv j c) ^ p := by
  apply Polynomial.funext
  intro x
  rw [eval_hasseDeriv_pow_char, if_pos (dvd_mul_right p j),
    Nat.mul_div_cancel_left j (Fact.out : p.Prime).pos, eval_pow]

/-- In characteristic `p`, `D^{(j)}(c ^ p) = 0` if `p ∤ j`. -/
theorem hasseDeriv_pow_char_of_not_dvd (c : k[X]) {j : ℕ} (hj : ¬ p ∣ j) :
    hasseDeriv j (c ^ p) = 0 := by
  apply Polynomial.funext
  intro x
  rw [eval_hasseDeriv_pow_char, if_neg hj, eval_zero]

end Frobenius

/-! ### The operators `Λ_N` -/

section Lambda

variable {k : Type*} [Field k] (p : ℕ)

/-- `Λ_N(f) = ∑_{n ≤ N} (D^{(pⁿ)} f) ^ (p ^ (N - n))`. -/
def hasseLambda (N : ℕ) (f : k[X]) : k[X] :=
  ∑ n ∈ Finset.range (N + 1), (hasseDeriv (p ^ n) f) ^ (p ^ (N - n))

variable {p} [Fact p.Prime] [CharP k p]

theorem hasseLambda_add (N : ℕ) (f g : k[X]) :
    hasseLambda p N (f + g) = hasseLambda p N f + hasseLambda p N g := by
  simp only [hasseLambda, map_add, add_pow_char_pow, Finset.sum_add_distrib]

theorem hasseLambda_sub (N : ℕ) (f g : k[X]) :
    hasseLambda p N (f - g) = hasseLambda p N f - hasseLambda p N g := by
  simp only [hasseLambda, map_sub, sub_pow_char_pow, Finset.sum_sub_distrib]

/-- `Λ_N(c ^ p) = Λ_N(c) - D^{(p^N)} c`. -/
theorem hasseLambda_pow_char [Infinite k] (N : ℕ) (c : k[X]) :
    hasseLambda p N (c ^ p) = hasseLambda p N c - hasseDeriv (p ^ N) c := by
  have hp := (Fact.out : p.Prime)
  have hsum : ∑ n ∈ Finset.range N, (hasseDeriv (p ^ (n + 1)) (c ^ p)) ^ (p ^ (N - (n + 1))) =
      ∑ n ∈ Finset.range N, (hasseDeriv (p ^ n) c) ^ (p ^ (N - n)) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn : n < N := Finset.mem_range.mp hn
    rw [pow_succ', hasseDeriv_mul_pow_char, ← pow_mul, ← pow_succ']
    congr 2
    omega
  rw [hasseLambda, Finset.sum_range_succ', hsum, pow_zero,
    hasseDeriv_pow_char_of_not_dvd c hp.not_dvd_one,
    zero_pow (pow_ne_zero _ hp.ne_zero), add_zero, hasseLambda, Finset.sum_range_succ,
    Nat.sub_self, pow_zero, pow_one, add_sub_cancel_right]

/-- `Λ_N(c ^ p - c) = -D^{(p^N)} c`. -/
theorem hasseLambda_pow_char_sub [Infinite k] (N : ℕ) (c : k[X]) :
    hasseLambda p N (c ^ p - c) = -hasseDeriv (p ^ N) c := by
  rw [hasseLambda_sub, hasseLambda_pow_char]
  ring

/-- If `deg f < p ^ (N₀ + 1)` and `N₀ ≤ N`, then `Λ_N(f) = Λ_{N₀}(f) ^ (p ^ (N - N₀))`. -/
theorem hasseLambda_eq_pow {f : k[X]} {N₀ N : ℕ} (hf : f.natDegree < p ^ (N₀ + 1))
    (hN : N₀ ≤ N) : hasseLambda p N f = hasseLambda p N₀ f ^ (p ^ (N - N₀)) := by
  have hp := (Fact.out : p.Prime)
  rw [hasseLambda, hasseLambda, sum_pow_char_pow]
  symm
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr (by omega : N₀ + 1 ≤ N + 1))]
  · refine Finset.sum_congr rfl fun n hn => ?_
    have hn : n ≤ N₀ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    rw [← pow_mul, ← pow_add]
    congr 2
    omega
  · intro n _ hn
    have hn : N₀ + 1 ≤ n := by simpa using hn
    have hlt : f.natDegree < p ^ n :=
      hf.trans_le (Nat.pow_le_pow_right hp.pos hn)
    rw [hasseDeriv_eq_zero_of_lt_natDegree f _ hlt,
      zero_pow (pow_ne_zero _ hp.ne_zero)]

/-- For `x ≥ 0` and `1 ≤ q ≤ Q`, `x ^ q ≤ max x (x ^ Q)`. -/
theorem pow_le_max_pow {x : ℝ} (hx : 0 ≤ x) {q Q : ℕ} (hq : 1 ≤ q) (hqQ : q ≤ Q) :
    x ^ q ≤ max x (x ^ Q) := by
  rcases le_total x 1 with h1 | h1
  · have h : x ^ q ≤ x ^ 1 := pow_le_pow_of_le_one hx h1 hq
    rw [pow_one] at h
    exact h.trans (le_max_left _ _)
  · exact (pow_le_pow_right₀ h1 hqQ).trans (le_max_right _ _)

/-! ### The leading term of `Λ_{N₀}(g)` -/

omit [Fact p.Prime] in
theorem natDegree_derivative_eq_and_leadingCoeff {g : k[X]} (hm : ¬ p ∣ g.natDegree) :
    (derivative g).natDegree = g.natDegree - 1 ∧
      (derivative g).leadingCoeff = g.leadingCoeff * g.natDegree := by
  have hm0 : g.natDegree ≠ 0 := fun h => hm (h ▸ dvd_zero p)
  have hcoeff : (derivative g).coeff (g.natDegree - 1) = g.leadingCoeff * g.natDegree := by
    rw [coeff_derivative, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm0)]
    norm_cast
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm0)]
    rfl
  have hne : g.leadingCoeff * g.natDegree ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · rw [leadingCoeff_ne_zero]
      rintro rfl
      simp at hm0
    · rwa [Ne, CharP.cast_eq_zero_iff k p]
  have hdeg : (derivative g).natDegree = g.natDegree - 1 :=
    natDegree_eq_of_le_of_coeff_ne_zero (natDegree_derivative_le g) (hcoeff ▸ hne)
  exact ⟨hdeg, by rw [leadingCoeff, hdeg, hcoeff]⟩

omit [Fact p.Prime] in
/-- Degree bound for the terms `n ≥ 1` of `Λ_{N₀}(g)`. -/
private theorem natDegree_lt_aux {m N₀ n : ℕ} (hp : 2 ≤ p) (hm : p ^ N₀ ≤ m) (hn : n < N₀) :
    p ^ (N₀ - (n + 1)) * (m - p ^ (n + 1)) < p ^ N₀ * (m - 1) := by
  set e := N₀ - (n + 1) with he_def
  set q := p ^ (n + 1) with hq_def
  have hN : p ^ N₀ = p ^ e * q := by
    rw [hq_def, ← pow_add]
    congr 1
    omega
  have hq : 2 ≤ q := le_trans hp (Nat.le_self_pow (by omega) p)
  have he : 0 < p ^ e := pow_pos (by omega) e
  rw [hN] at hm ⊢
  have hqm : q ≤ m := le_trans (Nat.le_mul_of_pos_left _ he) hm
  obtain ⟨t, rfl⟩ : ∃ t, m = q + t := ⟨m - q, by omega⟩
  rw [Nat.add_sub_cancel_left, mul_assoc]
  refine (Nat.mul_lt_mul_left he).mpr ?_
  have h1 : t + 1 ≤ q + t - 1 := by omega
  calc t < 2 * (t + 1) := by omega
    _ ≤ q * (q + t - 1) := Nat.mul_le_mul hq h1

theorem natDegree_and_leadingCoeff_hasseLambda_log {g : k[X]} (hm : ¬ p ∣ g.natDegree) :
    (hasseLambda p (Nat.log p g.natDegree) g).natDegree =
        p ^ Nat.log p g.natDegree * (g.natDegree - 1) ∧
      (hasseLambda p (Nat.log p g.natDegree) g).leadingCoeff =
        (g.leadingCoeff * g.natDegree) ^ (p ^ Nat.log p g.natDegree) := by
  have hp := (Fact.out : p.Prime)
  set m := g.natDegree with hmdef
  set N₀ := Nat.log p m
  have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero p)
  have hpN : p ^ N₀ ≤ m := Nat.pow_log_le_self p hm0
  obtain ⟨hdd, hdl⟩ := natDegree_derivative_eq_and_leadingCoeff hm
  set T₀ := (derivative g) ^ (p ^ N₀) with hT₀
  have hdne : derivative g ≠ 0 := by
    intro h
    rw [h, leadingCoeff_zero] at hdl
    exact (mul_ne_zero (leadingCoeff_ne_zero.mpr (by rintro rfl; simp [hmdef] at hm0))
      (by rwa [Ne, CharP.cast_eq_zero_iff k p])) hdl.symm
  have hT₀ne : T₀ ≠ 0 := pow_ne_zero _ hdne
  have hT₀deg : T₀.natDegree = p ^ N₀ * (m - 1) := by rw [hT₀, natDegree_pow, hdd]
  have hT₀lc : T₀.leadingCoeff = (g.leadingCoeff * m) ^ (p ^ N₀) := by
    rw [hT₀, leadingCoeff_pow, hdl]
  set R := ∑ n ∈ Finset.range N₀, (hasseDeriv (p ^ (n + 1)) g) ^ (p ^ (N₀ - (n + 1))) with hR
  have hsplit : hasseLambda p N₀ g = R + T₀ := by
    rw [hasseLambda, Finset.sum_range_succ', pow_zero, hasseDeriv_one', Nat.sub_zero]
  have hRdeg : R.degree < T₀.degree := by
    rw [degree_eq_natDegree hT₀ne, hT₀deg]
    refine (degree_sum_le _ _).trans_lt ?_
    rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
    intro n hn
    have hn : n < N₀ := Finset.mem_range.mp hn
    refine degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr ?_)
    calc (hasseDeriv (p ^ (n + 1)) g ^ p ^ (N₀ - (n + 1))).natDegree
        ≤ p ^ (N₀ - (n + 1)) * (hasseDeriv (p ^ (n + 1)) g).natDegree := natDegree_pow_le
      _ ≤ p ^ (N₀ - (n + 1)) * (m - p ^ (n + 1)) :=
          Nat.mul_le_mul_left _ (natDegree_hasseDeriv_le g _)
      _ < p ^ N₀ * (m - 1) := natDegree_lt_aux hp.two_le hpN hn
  rw [hsplit]
  exact ⟨by rw [natDegree_add_eq_right_of_degree_lt hRdeg, hT₀deg],
    by rw [leadingCoeff_add_of_degree_lt hRdeg, hT₀lc]⟩

/-- For `p ∤ deg g` and `N₀ = ⌊log_p deg g⌋`, `deg Λ_{N₀}(g) = p ^ N₀ (deg g - 1)`. -/
theorem natDegree_hasseLambda_log {g : k[X]} (hm : ¬ p ∣ g.natDegree) :
    (hasseLambda p (Nat.log p g.natDegree) g).natDegree =
      p ^ Nat.log p g.natDegree * (g.natDegree - 1) :=
  (natDegree_and_leadingCoeff_hasseLambda_log hm).1

/-- For `p ∤ deg g` and `N₀ = ⌊log_p deg g⌋`, the leading coefficient of `Λ_{N₀}(g)` is
`(lc g * deg g) ^ (p ^ N₀)`. -/
theorem leadingCoeff_hasseLambda_log {g : k[X]} (hm : ¬ p ∣ g.natDegree) :
    (hasseLambda p (Nat.log p g.natDegree) g).leadingCoeff =
      (g.leadingCoeff * g.natDegree) ^ (p ^ Nat.log p g.natDegree) :=
  (natDegree_and_leadingCoeff_hasseLambda_log hm).2

end Lambda

section LambdaNorm

variable {k K : Type*} [NormedField k] [IsAlgClosed k] [NormedField K] [IsUltrametricDist K]
  [NormedAlgebra k K] {p : ℕ} [Fact p.Prime]

/-- Cauchy bound for `Λ_N`: `‖Λ_N(f)(z)‖ * r ^ (p ^ N) ≤ max ‖f(z)‖ (‖f(z)‖ ^ (p ^ N))`. -/
theorem norm_aeval_hasseLambda_mul_le {z : K} {r : ℝ} (hr0 : 0 ≤ r)
    (hr : ∀ a : k, r ≤ ‖z - algebraMap k K a‖) (f : k[X]) (N : ℕ) :
    ‖aeval z (hasseLambda p N f)‖ * r ^ (p ^ N) ≤
      max ‖aeval z f‖ (‖aeval z f‖ ^ (p ^ N)) := by
  have hp := (Fact.out : p.Prime)
  set M := max ‖aeval z f‖ (‖aeval z f‖ ^ (p ^ N))
  have hM : 0 ≤ M := (norm_nonneg _).trans (le_max_left _ _)
  have hterm : ∀ n ∈ Finset.range (N + 1),
      ‖aeval z (hasseDeriv (p ^ n) f) ^ (p ^ (N - n))‖ * r ^ (p ^ N) ≤ M := by
    intro n hn
    have hn : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    have hpow : r ^ (p ^ N) = (r ^ (p ^ n)) ^ (p ^ (N - n)) := by
      rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hn]
    rw [norm_pow, hpow, ← mul_pow]
    calc (‖aeval z (hasseDeriv (p ^ n) f)‖ * r ^ (p ^ n)) ^ (p ^ (N - n))
        ≤ ‖aeval z f‖ ^ (p ^ (N - n)) :=
          pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (pow_nonneg hr0 _))
            (norm_aeval_hasseDeriv_mul_pow_le hr0 hr f _) _
      _ ≤ M := pow_le_max_pow (norm_nonneg _) (Nat.one_le_pow _ _ hp.pos)
            (Nat.pow_le_pow_right hp.pos (Nat.sub_le N n))
  rcases eq_or_lt_of_le (pow_nonneg hr0 (p ^ N)) with h0 | hpos
  · rw [← h0, mul_zero]
    exact hM
  · rw [← le_div_iff₀ hpos]
    simp only [hasseLambda, map_sum, map_pow]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (div_nonneg hM hpos.le)
      fun n hn => ?_
    rw [le_div_iff₀ hpos]
    simpa using hterm n hn

end LambdaNorm

/-! ### Temkin, Lemma 6.2.8 in characteristic `p` -/

section NoRoot

variable {k K : Type*} [NormedField k] [IsAlgClosed k] [NormedField K] [IsUltrametricDist K]
  [NormedAlgebra k K] {p : ℕ} [Fact p.Prime] [CharP k p]

/-- **Temkin, Lemma 6.2.8** (characteristic `p`): a type 4 generator `z` of `K` has no `p`-th
root in `K`. -/
theorem IsTypeFourGenerator.pow_char_ne {z : K} (hz : IsTypeFourGenerator k z) (y : K) :
    y ^ p ≠ z := by
  have hp := (Fact.out : p.Prime)
  have : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  intro hyz
  set r := radius k z
  have hr : 0 < r := hz.radius_pos
  set δ := min r 1 with hδ
  have hδpos : 0 < δ := lt_min hr one_pos
  obtain ⟨_, ⟨g, rfl⟩, hyg⟩ := hz.dense_aeval.exists_dist_lt y hδpos
  rw [dist_eq_norm] at hyg
  have hnorm : ‖aeval z (X - g ^ p)‖ < r := by
    have : aeval z (X - g ^ p) = (y - aeval z g) ^ p := by
      rw [sub_pow_char, hyz]; simp
    rw [this, norm_pow]
    calc ‖y - aeval z g‖ ^ p < δ ^ p := pow_lt_pow_left₀ hyg (norm_nonneg _) hp.ne_zero
      _ ≤ δ := pow_le_of_le_one hδpos.le (min_le_right _ _) hp.ne_zero
      _ ≤ r := min_le_left _ _
  have hD : hasseDeriv 1 (X - g ^ p : k[X]) = 1 := by
    rw [hasseDeriv_one', derivative_sub, derivative_X, derivative_pow,
      CharP.cast_eq_zero, map_zero, zero_mul, zero_mul, sub_zero]
  have hC := norm_aeval_hasseDeriv_mul_pow_le hr.le (radius_le z) (X - g ^ p) 1
  rw [hD, map_one, norm_one, one_mul, pow_one] at hC
  exact lt_irrefl _ (hC.trans_lt hnorm)

end NoRoot

end DeJongAlterations.StableModification.Valuation
