/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.Tuning

/-!
# The tuning parameter

[Kol07, Aside 99.10] remarks that `(m − 1) · lcm(2, …, m) ≤ m!` for `m ≥ 6`, that (99.6) can be
checked by hand for `t ≥ m!` when `m = 1, …, 5`, and hence that `W_{m!}(I)` is D-balanced, "the
traditional choice of the coefficient ideal". This module proves the first remark and fixes the
parameter `s(m)` of the tuning ideal `W_{s(m)}(I)` used throughout the library.

* `(m − 1) L_m ≤ m!` for `m ≥ 6` (`sub_one_mul_Lcm_le_factorial`), with `L_m = lcm(2, …, m)`. The
  proof is the library's own: `L_{n+1} = lcm(L_n, n + 1)` (`Lcm_succ`), so
  `d · L_{n+1} ≤ L_n (n + 1)` for every common divisor `d` of `L_n` and `n + 1` (`mul_Lcm_succ_le`);
  if `n + 2` is composite, its least prime factor is such a common divisor of `L_{n+1}` and `n + 2`,
  and if `n + 2` is an odd prime, then `n + 1` is even and `2` is a common divisor of `L_n` and
  `n + 1`. The invariant `m L_m ≤ m!` for `m ≥ 6` follows by a two-step induction from the cases
  `m = 6, 7` (`mul_Lcm_le_factorial`).
* For `m ∈ {1, 2}` and `m ≥ 6`, `m! = r L_m` with `r ≥ m − 1` (`exists_factorial_eq_mul_Lcm`), so
  [Kol07, Proposition 99 (6)–(8)] apply with `s = m!`: `W_{m!}(I)` is D-balanced
  (`isDBalanced_W_factorial`).
* The **tuning parameter** of the library is `tuningParam m = max (m − 1) 1 · L_m`, the smallest
  multiple `r L_m` with `r ≥ m − 1` and `r ≥ 1`; it is admissible for [Kol07, Proposition 99
  (6)–(8)] for every `m ≥ 1` without any hand check. `W_{s(m)}(I)` is D-balanced
  (`isDBalanced_W_tuningParam`), MC-invariant (`isMCInvariant_W_tuningParam`) and of order `s(m)`
  when `ord I = m` (`ord_W_tuningParam`). The factorial `m!` is not used as the parameter anywhere
  in the library.

Used for the tuned triple of the order-reduction theorems
(`Hironaka/Resolution/Algebraic/OrderReduction/Tuned.lean`,
`Hironaka/Resolution/Algebraic/Tuning/Parameter.lean`,
`Hironaka/Resolution/Algebraic/Stage/Amalgam.lean`) and on manifolds
(`Hironaka/Manifold/IdealSheaf/Tuning.lean`).
-/

@[expose] public section

namespace IsLocalRing

open IsLocalRing Nat

/-! ### Number theory of `L_m` -/

theorem Lcm_dvd_Lcm_succ (n : ℕ) : Lcm n ∣ Lcm (n + 1) :=
  Finset.lcm_dvd fun k hk => by
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hk
    change k ∣ Lcm (n + 1)
    exact dvd_Lcm (by omega) (by omega)

theorem succ_dvd_Lcm_succ (n : ℕ) (hn : 1 ≤ n) : n + 1 ∣ Lcm (n + 1) :=
  dvd_Lcm (by omega) le_rfl

theorem Lcm_dvd_factorial (m : ℕ) : Lcm m ∣ m ! :=
  Finset.lcm_dvd fun k hk => by
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hk
    change k ∣ Nat.factorial m
    exact Nat.dvd_factorial (by omega) h2

/-- `L_{n+1} = lcm(L_n, n + 1)`. -/
theorem Lcm_succ (n : ℕ) (hn : 1 ≤ n) : Lcm (n + 1) = Nat.lcm (Lcm n) (n + 1) :=
  Nat.dvd_antisymm
    (Finset.lcm_dvd fun k hk => by
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hk
      change k ∣ Nat.lcm (Lcm n) (n + 1)
      rcases Nat.lt_or_ge k (n + 1) with h | h
      · exact (dvd_Lcm (by omega) (by omega)).trans (Nat.dvd_lcm_left _ _)
      · have : k = n + 1 := le_antisymm h2 h
        rw [this]
        exact Nat.dvd_lcm_right _ _)
    (Nat.lcm_dvd (Lcm_dvd_Lcm_succ n) (succ_dvd_Lcm_succ n hn))

/-- A common divisor `d` of `L_n` and `n + 1` gives `d · L_{n+1} ≤ L_n (n + 1)`. -/
theorem mul_Lcm_succ_le {n d : ℕ} (hn : 1 ≤ n) (hd : d ∣ Lcm n) (hd' : d ∣ n + 1) :
    d * Lcm (n + 1) ≤ Lcm n * (n + 1) := by
  rw [Lcm_succ n hn, ← Nat.gcd_mul_lcm (Lcm n) (n + 1)]
  exact Nat.mul_le_mul_right _
    (Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (Lcm_pos n)) (Nat.dvd_gcd hd hd'))

theorem Lcm_succ_le (n : ℕ) (hn : 1 ≤ n) : Lcm (n + 1) ≤ Lcm n * (n + 1) := by
  have := mul_Lcm_succ_le hn (one_dvd (Lcm n)) (one_dvd (n + 1))
  simpa using this

/-- The induction step for `m L_m ≤ m!`: from the cases `n` and `n + 1` to `n + 2` (`n ≥ 6`), by
the least prime factor of `n + 2` when it is composite and by `2 ∣ n + 1` when it is an odd
prime. -/
theorem mul_Lcm_le_factorial_step {n : ℕ} (hn : 6 ≤ n) (h1 : n * Lcm n ≤ n !)
    (h2 : (n + 1) * Lcm (n + 1) ≤ (n + 1)!) : (n + 2) * Lcm (n + 2) ≤ (n + 2)! := by
  rw [Nat.factorial_succ (n + 1)]
  refine Nat.mul_le_mul_left _ ?_
  have hB : Lcm (n + 2) ≤ Lcm (n + 1) * (n + 2) := Lcm_succ_le (n + 1) (by omega)
  by_cases hp : Nat.Prime (n + 2)
  · have hodd : Odd (n + 2) := hp.odd_of_ne_two (by omega)
    have h2n : 2 ∣ n + 1 := by
      obtain ⟨k, hk⟩ := hodd
      exact ⟨k, by omega⟩
    have hA : 2 * Lcm (n + 1) ≤ Lcm n * (n + 1) :=
      mul_Lcm_succ_le (by omega) (dvd_Lcm (by omega) (by omega)) h2n
    have hfac : (n + 1)! = (n + 1) * n ! := Nat.factorial_succ n
    have hchain : 2 * n * Lcm (n + 2) ≤ n ! * (n + 1) * (n + 2) := by
      calc 2 * n * Lcm (n + 2) ≤ 2 * n * (Lcm (n + 1) * (n + 2)) := Nat.mul_le_mul_left _ hB
        _ = n * (2 * Lcm (n + 1)) * (n + 2) := by ring
        _ ≤ n * (Lcm n * (n + 1)) * (n + 2) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hA)
        _ = n * Lcm n * (n + 1) * (n + 2) := by ring
        _ ≤ n ! * (n + 1) * (n + 2) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h1)
    have : 2 * n * Lcm (n + 2) ≤ 2 * n * (n + 1)! := by
      calc 2 * n * Lcm (n + 2) ≤ n ! * (n + 1) * (n + 2) := hchain
        _ ≤ n ! * (n + 1) * (2 * n) := Nat.mul_le_mul_left _ (by omega)
        _ = 2 * n * (n + 1)! := by rw [hfac]; ring
    exact Nat.le_of_mul_le_mul_left this (by omega)
  · have hne1 : n + 2 ≠ 1 := by omega
    have hmin := Nat.minFac_dvd (n + 2)
    have hmin2 : 2 ≤ Nat.minFac (n + 2) := (Nat.minFac_prime hne1).two_le
    have hminlt : Nat.minFac (n + 2) < n + 2 := (Nat.not_prime_iff_minFac_lt (by omega)).mp hp
    have hA : Nat.minFac (n + 2) * Lcm (n + 2) ≤ Lcm (n + 1) * (n + 2) :=
      mul_Lcm_succ_le (by omega) (dvd_Lcm (by omega) (by omega)) hmin
    have hA2 : 2 * Lcm (n + 2) ≤ Lcm (n + 1) * (n + 2) :=
      (Nat.mul_le_mul_right _ hmin2).trans hA
    have hchain : 2 * (n + 1) * Lcm (n + 2) ≤ (n + 1)! * (n + 2) := by
      calc 2 * (n + 1) * Lcm (n + 2) = (n + 1) * (2 * Lcm (n + 2)) := by ring
        _ ≤ (n + 1) * (Lcm (n + 1) * (n + 2)) := Nat.mul_le_mul_left _ hA2
        _ = (n + 1) * Lcm (n + 1) * (n + 2) := by ring
        _ ≤ (n + 1)! * (n + 2) := Nat.mul_le_mul_right _ h2
    have : 2 * (n + 1) * Lcm (n + 2) ≤ 2 * (n + 1) * (n + 1)! := by
      calc 2 * (n + 1) * Lcm (n + 2) ≤ (n + 1)! * (n + 2) := hchain
        _ ≤ (n + 1)! * (2 * (n + 1)) := Nat.mul_le_mul_left _ (by omega)
        _ = 2 * (n + 1) * (n + 1)! := by ring
    exact Nat.le_of_mul_le_mul_left this (by omega)

/-- `m L_m ≤ m!` for `m ≥ 6`. -/
theorem mul_Lcm_le_factorial {m : ℕ} (hm : 6 ≤ m) : m * Lcm m ≤ m ! := by
  have key : ∀ k, (k + 6) * Lcm (k + 6) ≤ (k + 6)! ∧ (k + 7) * Lcm (k + 7) ≤ (k + 7)! := by
    intro k
    induction k with
    | zero => exact ⟨by decide, by decide⟩
    | succ k ih => exact ⟨ih.2, mul_Lcm_le_factorial_step (by omega) ih.1 ih.2⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 6 := ⟨m - 6, by omega⟩
  exact (key k).1

/-- [Kol07, Aside 99.10]: `(m − 1) · lcm(2, …, m) ≤ m!` for `m ≥ 6`, which Kollár says "is easy to
see". -/
theorem sub_one_mul_Lcm_le_factorial {m : ℕ} (hm : 6 ≤ m) : (m - 1) * Lcm m ≤ m ! :=
  (Nat.mul_le_mul_right _ (Nat.sub_le m 1)).trans (mul_Lcm_le_factorial hm)

/-- For `m ∈ {1, 2}` and `m ≥ 6`, `m! = r L_m` with `r ≥ m − 1`, so [Kol07, Proposition 99
(6)–(8)] apply with `s = m!`. -/
theorem exists_factorial_eq_mul_Lcm {m : ℕ} (hm : m = 1 ∨ m = 2 ∨ 6 ≤ m) :
    ∃ r : ℕ, m ! = r * Lcm m ∧ m - 1 ≤ r := by
  refine ⟨m ! / Lcm m, (Nat.div_mul_cancel (Lcm_dvd_factorial m)).symm, ?_⟩
  rw [Nat.le_div_iff_mul_le (Lcm_pos m)]
  rcases hm with rfl | rfl | hm
  · decide
  · decide
  · exact sub_one_mul_Lcm_le_factorial hm

/-! ### The tuning parameter -/

/-- The **tuning parameter** `s(m) = max (m − 1) 1 · L_m` of the library: the smallest multiple
`r L_m` of `L_m` with `r ≥ m − 1` and `r ≥ 1`, for which [Kol07, Proposition 99 (6)–(8)] apply. -/
def tuningParam (m : ℕ) : ℕ := max (m - 1) 1 * Lcm m

theorem one_le_tuningParam (m : ℕ) : 1 ≤ tuningParam m := by
  change 1 * 1 ≤ max (m - 1) 1 * Lcm m
  exact Nat.mul_le_mul (le_max_right _ _) (Lcm_pos m)

namespace RegularCoords

variable {R : Type*} [CommRing R] [IsRegularLocalRing R] [Algebra ℚ R] {n : ℕ}
  (c : RegularCoords R n)

/-- [Kol07, Aside 99.10] ("Thus we conclude that `W_{m!}(I)` is D-balanced") for `m ∈ {1, 2}` and
`m ≥ 6`: `W_{m!}(I)` is D-balanced with respect to `m!`. -/
theorem isDBalanced_W_factorial {m : ℕ} (hm : m = 1 ∨ m = 2 ∨ 6 ≤ m) {I : Ideal R}
    (hI : ord I ≤ m) : c.IsDBalanced (c.W m (m !) I) (m !) := by
  obtain ⟨r, hr, hr'⟩ := exists_factorial_eq_mul_Lcm hm
  rw [hr]
  exact c.isDBalanced_W (by omega) hI hr'

/-- `W_{s(m)}(I)` is D-balanced with respect to `s(m)` ([Kol07, (99.8)]). -/
theorem isDBalanced_W_tuningParam {m : ℕ} (hm : 1 ≤ m) {I : Ideal R} (hI : ord I ≤ m) :
    c.IsDBalanced (c.W m (tuningParam m) I) (tuningParam m) :=
  c.isDBalanced_W hm hI (le_max_left _ _)

/-- `W_{s(m)}(I)` is MC-invariant with respect to `s(m)` ([Kol07, (99.5)]). -/
theorem isMCInvariant_W_tuningParam {m : ℕ} (hm : 1 ≤ m) {I : Ideal R} (hI : ord I ≤ m) :
    c.IsMCInvariant (c.W m (tuningParam m) I) (tuningParam m) :=
  c.isMCInvariant_W hm hI (one_le_tuningParam m)

/-- `ord W_{s(m)}(I) = s(m)` when `ord I = m ≥ 1` (`ord_W`). -/
theorem ord_W_tuningParam {m : ℕ} (hm : 1 ≤ m) {I : Ideal R} (hI : ord I = m) :
    ord (c.W m (tuningParam m) I) = tuningParam m :=
  c.ord_W hm hI _

end RegularCoords

end IsLocalRing
