import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.Finite.Basic
import DeJongAlterations.StableModification.Valuation.Analytic.TypeFour.Taylor

/-!
# Temkin's Lemma 6.2.9 in characteristic `p`

Let `k` be an algebraically closed non-archimedean field of characteristic `p`, and `z` a type 4
generator of a non-archimedean field `K ⊇ k` (`IsTypeFourGenerator`), with radius
`r = inf_{a ∈ k} ‖z - a‖`. This file proves Temkin's "unpleasant" Lemma 6.2.9
(*Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), `semi-stable.tex`,
lines 3871–3949) in characteristic `p`: if `g = ∑_{i ≤ m} bᵢ Xⁱ ∈ k[X]` has degree `m` with
`p ∤ m` and the coset `g(z) + S_{a,s}(K)` is special, then `‖b_m‖ r ^ m ≤ s`, strictly if
`m > 1`.

Temkin's proof uses the completed tensor product `K ⊗̂_k l ≅ l{r⁻¹ w}` over an auxiliary
algebraically closed field `l`. It is replaced here by the Hasse–Cauchy bound
(`norm_aeval_hasseDeriv_mul_pow_le`) and the density of `k[z]` in `K`: for `a = 0` the first
Hasse derivative kills `p`-th powers, and for `a = 1` the operators `Λ_N` of
`DeJongAlterations.StableModification.Valuation.hasseLambda` satisfy `Λ_N(c ^ p - c) =
-D^{(p^N)} c`, whose size is controlled by `‖c(z)‖` independently of `N`.

## Main results

* `norm_natCast_eq_one_of_not_dvd`: `‖(m : k)‖ = 1` for `p ∤ m`.
* `IsTypeFourGenerator.exists_poly_approx`: elements of a critical coset of `g(z)` approximated
  by polynomial expressions `(g + c ^ p - a c + d)(z)`.
* `IsTypeFourGenerator.radius_mul_norm_derivative_le` (case `a = 0`) and
  `IsTypeFourGenerator.norm_aeval_hasseLambda_mul_le_one` (case `a = 1`, `s = 1`).
* `IsTypeFourGenerator.norm_leadingCoeff_mul_radius_pow_le`,
  `IsTypeFourGenerator.norm_leadingCoeff_mul_radius_pow_lt`: **Temkin, Lemma 6.2.9**.

## References

Blueprint `sm-val-onedim-t34.tex`: `lem:sm-an-dirty-charp`.
-/

noncomputable section

open Polynomial

namespace DeJongAlterations.StableModification.Valuation

variable {k K : Type*} [NormedField k] [IsAlgClosed k] [NormedField K] [IsUltrametricDist K]
  [NormedAlgebra k K] {p : ℕ} [Fact p.Prime] [CharP k p]

omit [IsAlgClosed k] in
/-- In characteristic `p`, an integer prime to `p` has absolute value `1`. -/
theorem norm_natCast_eq_one_of_not_dvd {m : ℕ} (hm : ¬ p ∣ m) : ‖(m : k)‖ = 1 := by
  have hp := (Fact.out : p.Prime)
  have hm0 : (m : k) ≠ 0 := by rwa [Ne, CharP.cast_eq_zero_iff k p]
  have hfrob : (m : k) ^ p = m := by
    rw [← map_natCast (ZMod.castHom (dvd_refl p) k), ← map_pow, ZMod.pow_card]
  have h1 : (m : k) ^ (p - 1) = 1 := by
    have : (m : k) ^ (p - 1) * m = 1 * m := by
      rw [← pow_succ, Nat.sub_add_cancel hp.one_lt.le, hfrob, one_mul]
    exact mul_right_cancel₀ hm0 this
  have h2 : ‖(m : k)‖ ^ (p - 1) = 1 := by rw [← norm_pow, h1, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by have := hp.two_le; omega)).mp h2

omit [IsAlgClosed k] [Fact p.Prime] [CharP k p] in
/-- Elements of a critical coset `g(z) + S_{a,s}(K)` with `a ∈ k` are approximated by
`(g + c ^ p - a c + d)(z)` with polynomials `c, d` and `‖d(z)‖ < s`. -/
theorem IsTypeFourGenerator.exists_poly_approx [IsAlgClosed k] {z : K}
    (hz : IsTypeFourGenerator k z) {a₀ : k} {s : ℝ} {g : k[X]}
    (hcrit : IsCriticalCoset p (algebraMap k K a₀) s (aeval z g)) {t : ℝ} (ht : s < t) :
    ∃ c d : k[X], ‖aeval z d‖ < s ∧ ‖aeval z (g + c ^ p - C a₀ * c + d)‖ < t := by
  obtain ⟨_, ⟨c, rfl⟩, _, ⟨d, rfl⟩, hd, hlt⟩ := hcrit.exists_mem_dense hz.dense_aeval ht
  refine ⟨c, d, hd, ?_⟩
  convert hlt using 2
  simp only [map_add, map_sub, map_mul, map_pow, aeval_C, asMap]
  ring

/-- **Lemma 6.2.9, case `a = 0`**: `r ‖g'(z)‖ ≤ s` when `g(z) + S_{0,s}(K)` is critical. -/
theorem IsTypeFourGenerator.radius_mul_norm_derivative_le {z : K}
    (hz : IsTypeFourGenerator k z) {s : ℝ} {g : k[X]}
    (hcrit : IsCriticalCoset p 0 s (aeval z g)) :
    radius k z * ‖aeval z (derivative g)‖ ≤ s := by
  have hp := (Fact.out : p.Prime)
  set r := radius k z
  have hr0 : 0 ≤ r := radius_nonneg z
  have hcrit' : IsCriticalCoset p (algebraMap k K 0) s (aeval z g) := by rwa [map_zero]
  refine le_of_forall_gt fun t ht => ?_
  obtain ⟨c, d, hd, hf⟩ := hz.exists_poly_approx hcrit' ht
  set f := g + c ^ p - C 0 * c + d with hfdef
  have hderiv : derivative g = derivative f - derivative d := by
    have h0 : derivative (c ^ p) = 0 := by
      rw [derivative_pow, CharP.cast_eq_zero, map_zero, zero_mul, zero_mul]
    rw [hfdef]
    simp [h0]
  have hCf := norm_aeval_hasseDeriv_mul_pow_le hr0 (radius_le z) f 1
  have hCd := norm_aeval_hasseDeriv_mul_pow_le hr0 (radius_le z) d 1
  rw [hasseDeriv_one', pow_one] at hCf hCd
  rw [hderiv, map_sub]
  calc r * ‖aeval z (derivative f) - aeval z (derivative d)‖
      ≤ r * max ‖aeval z (derivative f)‖ ‖aeval z (derivative d)‖ :=
        mul_le_mul_of_nonneg_left (norm_sub_le_max_norm _ _) hr0
    _ = max (‖aeval z (derivative f)‖ * r) (‖aeval z (derivative d)‖ * r) := by
        rw [mul_max_of_nonneg _ _ hr0, mul_comm r, mul_comm r]
    _ < t := max_lt (hCf.trans_lt hf) (hCd.trans_lt (hd.trans ht))

/-- **Lemma 6.2.9, case `a = 1`, `s = 1`**: with `N₀ = ⌊log_p deg g⌋`,
`‖Λ_{N₀}(g)(z)‖ r ^ (p ^ N₀) ≤ 1` when `g(z) + S_{1,1}(K)` is critical. -/
theorem IsTypeFourGenerator.norm_aeval_hasseLambda_mul_le_one {z : K}
    (hz : IsTypeFourGenerator k z) {g : k[X]} (hcrit : IsCriticalCoset p 1 1 (aeval z g)) :
    ‖aeval z (hasseLambda p (Nat.log p g.natDegree) g)‖ *
      radius k z ^ (p ^ Nat.log p g.natDegree) ≤ 1 := by
  have hp := (Fact.out : p.Prime)
  set r := radius k z
  have hr0 : 0 ≤ r := radius_nonneg z
  set N₀ := Nat.log p g.natDegree
  set q := p ^ N₀ with hq
  have hq0 : q ≠ 0 := pow_ne_zero _ hp.ne_zero
  set A := ‖aeval z (hasseLambda p N₀ g)‖ * r ^ q with hAdef
  by_contra hA
  rw [not_le] at hA
  -- choose `t > 1` with `t ^ q < A`
  set t : ℝ := A ^ (1 / (2 * (q : ℝ))) with htdef
  have hqpos : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq0
  have ht1 : 1 < t := Real.one_lt_rpow hA (by positivity)
  have htq : t ^ q < A := by
    rw [htdef, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    have : 1 / (2 * (q : ℝ)) * q = 1 / 2 := by field_simp
    rw [this]
    calc A ^ (1 / 2 : ℝ) < A ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt hA (by norm_num)
      _ = A := Real.rpow_one A
  have hcrit' : IsCriticalCoset p (algebraMap k K 1) 1 (aeval z g) := by rwa [map_one]
  obtain ⟨c, d, hd, hf⟩ := hz.exists_poly_approx hcrit' ht1
  set f := g + c ^ p - C 1 * c + d with hfdef
  -- the key inequality for every `N ≥ N₀`
  have hkey : ∀ j : ℕ, A ^ (p ^ j) ≤ max (max ((t ^ q) ^ (p ^ j)) ‖aeval z c‖) 1 := by
    intro j
    set N := N₀ + j with hN
    have hdeg : g.natDegree < p ^ (N₀ + 1) := Nat.lt_pow_succ_log_self hp.one_lt _
    have hpowN : p ^ N = q * p ^ j := by rw [hN, pow_add]
    have hLg : hasseLambda p N g = hasseLambda p N₀ g ^ (p ^ j) := by
      rw [hasseLambda_eq_pow hdeg (by omega), show N - N₀ = j by omega]
    have hdecomp : hasseLambda p N g =
        hasseLambda p N f + hasseDeriv (p ^ N) c - hasseLambda p N d := by
      have h1 := hasseLambda_add (p := p) N (g + (c ^ p - c)) d
      have h2 := hasseLambda_add (p := p) N g (c ^ p - c)
      have h3 := hasseLambda_pow_char_sub (p := p) N c
      have hf' : f = g + (c ^ p - c) + d := by rw [hfdef, C_1, one_mul]; ring
      rw [hf', h1, h2, h3]
      ring
    have hlhs : ‖aeval z (hasseLambda p N g)‖ * r ^ (p ^ N) = A ^ (p ^ j) := by
      rw [hLg, map_pow, norm_pow, hpowN, pow_mul, ← mul_pow]
    rw [← hlhs, hdecomp, map_sub, map_add]
    have hR : 0 ≤ r ^ (p ^ N) := pow_nonneg hr0 _
    have hfN : ‖aeval z (hasseLambda p N f)‖ * r ^ (p ^ N) ≤ (t ^ q) ^ (p ^ j) := by
      refine (norm_aeval_hasseLambda_mul_le hr0 (radius_le z) f N).trans (max_le ?_ ?_)
      · rw [← pow_mul, ← hpowN]
        exact hf.le.trans (le_self_pow₀ ht1.le (pow_ne_zero _ hp.ne_zero))
      · rw [← pow_mul, ← hpowN]
        exact pow_le_pow_left₀ (norm_nonneg _) hf.le _
    have hcN : ‖aeval z (hasseDeriv (p ^ N) c)‖ * r ^ (p ^ N) ≤ ‖aeval z c‖ :=
      norm_aeval_hasseDeriv_mul_pow_le hr0 (radius_le z) c _
    have hdN : ‖aeval z (hasseLambda p N d)‖ * r ^ (p ^ N) ≤ 1 :=
      (norm_aeval_hasseLambda_mul_le hr0 (radius_le z) d N).trans
        (max_le hd.le (pow_le_one₀ (norm_nonneg _) hd.le))
    calc ‖aeval z (hasseLambda p N f) + aeval z (hasseDeriv (p ^ N) c) -
          aeval z (hasseLambda p N d)‖ * r ^ (p ^ N)
        ≤ max (max ‖aeval z (hasseLambda p N f)‖ ‖aeval z (hasseDeriv (p ^ N) c)‖)
            ‖aeval z (hasseLambda p N d)‖ * r ^ (p ^ N) :=
          mul_le_mul_of_nonneg_right ((norm_sub_le_max_norm _ _).trans
            (max_le_max (IsUltrametricDist.norm_add_le_max _ _) le_rfl)) hR
      _ = max (max (‖aeval z (hasseLambda p N f)‖ * r ^ (p ^ N))
            (‖aeval z (hasseDeriv (p ^ N) c)‖ * r ^ (p ^ N)))
            (‖aeval z (hasseLambda p N d)‖ * r ^ (p ^ N)) := by
          rw [max_mul_of_nonneg _ _ hR, max_mul_of_nonneg _ _ hR]
      _ ≤ max (max ((t ^ q) ^ (p ^ j)) ‖aeval z c‖) 1 :=
          max_le_max (max_le_max hfN hcN) hdN
  -- contradiction for large `j`
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt ‖aeval z c‖ hA
  have hjp : A ^ j ≤ A ^ (p ^ j) := pow_le_pow_right₀ hA.le (Nat.lt_pow_self hp.one_lt).le
  have hpj : p ^ j ≠ 0 := pow_ne_zero _ hp.ne_zero
  have h1 : (t ^ q) ^ (p ^ j) < A ^ (p ^ j) :=
    pow_lt_pow_left₀ htq (pow_nonneg (by linarith) _) hpj
  have h2 : 1 < A ^ (p ^ j) := one_lt_pow₀ hA hpj
  exact absurd (hkey j) (not_le.mpr (max_lt (max_lt h1 (hj.trans_le hjp)) h2))

/-- **Temkin, Lemma 6.2.9** (characteristic `p`), both inequalities. -/
theorem IsTypeFourGenerator.norm_leadingCoeff_mul_radius_pow_le_and_lt {z : K}
    (hz : IsTypeFourGenerator k z) {g : k[X]} (hm : ¬ p ∣ g.natDegree) {a : K} {s : ℝ}
    (hsp : IsSpecialCoset p a s (aeval z g)) :
    ‖g.leadingCoeff‖ * radius k z ^ g.natDegree ≤ s ∧
      (1 < g.natDegree → ‖g.leadingCoeff‖ * radius k z ^ g.natDegree < s) := by
  have hp := (Fact.out : p.Prime)
  set r := radius k z
  have hr : 0 < r := hz.radius_pos
  set m := g.natDegree with hmdef
  have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero p)
  have hg0 : g ≠ 0 := by rintro rfl; simp [hmdef] at hm0
  have hnot := hz.exists_norm_sub_lt_norm_sub
  obtain ⟨hdd, hdl⟩ := natDegree_derivative_eq_and_leadingCoeff hm
  have hlcm : ‖g.leadingCoeff * (m : k)‖ = ‖g.leadingCoeff‖ := by
    rw [norm_mul, norm_natCast_eq_one_of_not_dvd hm, mul_one]
  have hrm : r ^ m = r * r ^ (m - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm0)]
  rcases hsp.2 with rfl | ⟨rfl, rfl⟩
  · -- case `a = 0`
    have hD := hz.radius_mul_norm_derivative_le hsp.1
    have hlow : ‖g.leadingCoeff‖ * r ^ (m - 1) ≤ ‖aeval z (derivative g)‖ := by
      have := norm_leadingCoeff_mul_pow_le_norm_aeval hr.le (radius_le z) (derivative g)
      rwa [hdd, hdl, hlcm] at this
    refine ⟨?_, fun h1 => ?_⟩
    · rw [hrm]
      calc ‖g.leadingCoeff‖ * (r * r ^ (m - 1)) = r * (‖g.leadingCoeff‖ * r ^ (m - 1)) := by ring
        _ ≤ r * ‖aeval z (derivative g)‖ := mul_le_mul_of_nonneg_left hlow hr.le
        _ ≤ s := hD
    · have hstrict : ‖g.leadingCoeff‖ * r ^ (m - 1) < ‖aeval z (derivative g)‖ := by
        have := norm_leadingCoeff_mul_radius_pow_lt_norm_aeval hnot
          (g := derivative g) (by rw [hdd]; omega)
        rwa [hdd, hdl, hlcm] at this
      rw [hrm]
      calc ‖g.leadingCoeff‖ * (r * r ^ (m - 1)) = r * (‖g.leadingCoeff‖ * r ^ (m - 1)) := by ring
        _ < r * ‖aeval z (derivative g)‖ := mul_lt_mul_of_pos_left hstrict hr
        _ ≤ s := hD
  · -- case `a = 1`, `s = 1`
    have hA := hz.norm_aeval_hasseLambda_mul_le_one hsp.1
    set N₀ := Nat.log p m
    set q := p ^ N₀
    have hq0 : q ≠ 0 := pow_ne_zero _ hp.ne_zero
    have hGdeg := natDegree_hasseLambda_log hm
    have hGlc := leadingCoeff_hasseLambda_log hm
    have hpow : ‖g.leadingCoeff‖ ^ q * r ^ (q * (m - 1)) * r ^ q =
        (‖g.leadingCoeff‖ * r ^ m) ^ q := by
      rw [mul_pow, mul_assoc, ← pow_add, ← pow_mul, mul_comm m q]
      congr 2
      rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm0)]
    have hlow : ‖g.leadingCoeff‖ ^ q * r ^ (q * (m - 1)) ≤
        ‖aeval z (hasseLambda p N₀ g)‖ := by
      have := norm_leadingCoeff_mul_pow_le_norm_aeval hr.le (radius_le z) (hasseLambda p N₀ g)
      rwa [hGdeg, hGlc, norm_pow, hlcm] at this
    refine ⟨?_, fun h1 => ?_⟩
    · have : (‖g.leadingCoeff‖ * r ^ m) ^ q ≤ 1 := by
        rw [← hpow]
        exact (mul_le_mul_of_nonneg_right hlow (pow_nonneg hr.le _)).trans hA
      exact (pow_le_one_iff_of_nonneg (by positivity) hq0).mp this
    · have hstrict : ‖g.leadingCoeff‖ ^ q * r ^ (q * (m - 1)) <
          ‖aeval z (hasseLambda p N₀ g)‖ := by
        have := norm_leadingCoeff_mul_radius_pow_lt_norm_aeval hnot
          (g := hasseLambda p N₀ g)
          (by rw [hGdeg]; exact Nat.mul_pos (Nat.pos_of_ne_zero hq0) (by omega))
        rwa [hGdeg, hGlc, norm_pow, hlcm] at this
      have : (‖g.leadingCoeff‖ * r ^ m) ^ q < 1 := by
        rw [← hpow]
        exact (mul_lt_mul_of_pos_right hstrict (pow_pos hr _)).trans_le hA
      exact (pow_lt_one_iff_of_nonneg (by positivity) hq0).mp this

/-- **Temkin, Lemma 6.2.9** (characteristic `p`): if `g ∈ k[X]` has degree `m` with `p ∤ m`
and `g(z) + S_{a,s}(K)` is special, then `‖lc g‖ r ^ m ≤ s`. -/
theorem IsTypeFourGenerator.norm_leadingCoeff_mul_radius_pow_le {z : K}
    (hz : IsTypeFourGenerator k z) {g : k[X]} (hm : ¬ p ∣ g.natDegree) {a : K} {s : ℝ}
    (hsp : IsSpecialCoset p a s (aeval z g)) :
    ‖g.leadingCoeff‖ * radius k z ^ g.natDegree ≤ s :=
  (hz.norm_leadingCoeff_mul_radius_pow_le_and_lt hm hsp).1

/-- **Temkin, Lemma 6.2.9** (characteristic `p`), strict form for `m > 1`. -/
theorem IsTypeFourGenerator.norm_leadingCoeff_mul_radius_pow_lt {z : K}
    (hz : IsTypeFourGenerator k z) {g : k[X]} (hm : ¬ p ∣ g.natDegree) (h1 : 1 < g.natDegree)
    {a : K} {s : ℝ} (hsp : IsSpecialCoset p a s (aeval z g)) :
    ‖g.leadingCoeff‖ * radius k z ^ g.natDegree < s :=
  (hz.norm_leadingCoeff_mul_radius_pow_le_and_lt hm hsp).2 h1

end DeJongAlterations.StableModification.Valuation
