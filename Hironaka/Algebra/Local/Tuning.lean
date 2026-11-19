/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.Balanced
public import Hironaka.Algebra.Local.MaximalContact

/-!
# Maximal coefficient ideals

[Kol07, Definition 98]: for an ideal `I` with `m = max-ord I`, the *maximal coefficient ideal of
order `s`* is `W_s(I) = ∑ { ∏ⱼ (Dʲ I)^{cⱼ} : ∑ⱼ (m − j) cⱼ ≥ s }`, the sum over all exponent
vectors `c : {0, …, m} → ℕ` of weight at least `s`. Here `R` is a regular local ring containing `ℚ`
with coordinates (`RegularCoords`), `Dʲ` its iterated derivative ideals
(`Hironaka/Algebra/Local/Derivative.lean`), and the parameter `m` is explicit: `c.W m s I`, with the
weight `wt m c`. The module proves the local forms of [Kol07, Proposition 99] and of its Claim 99.9:

* `W_0(I) = R`; `Iᵏ ≤ W_s(I)` for `m k ≥ s` (`pow_le_W`); `MC_m(I)ˢ ≤ W_s(I)` (`MC_pow_le_W`);
  `W_1(I) = MC_m(I)` for `m ≥ 1` (`W_one`); `W_s(I) = R` when `ord I < m` (`W_eq_top_of_ord_lt`);
* (99.1) `W_{s+1}(I) ≤ W_s(I)` and (99.2) `W_s(I) · W_t(I) ≤ W_{s+t}(I)` (`W_succ_le`, `W_mul_le`);
* (99.3) `D(W_{s+1}(I)) = W_s(I)` for `ord I ≤ m`, `m ≥ 1` (`D_W_succ`: the inclusion `≤` by the
  product rule; the reverse by Kollár's argument with an element `x₁ ∈ MC_m(I)` of order `1` and a
  derivation `∂` with `∂ x₁ = 1`, showing `x₁^{s−t} W_t(I) ≤ D(W_{s+1}(I))` by induction on `t`),
  and its iterate `Dⁱ(W_s(I)) = W_{s−i}(I)` (`Dpow_W`);
* the order: `ord W_s(I) = s` when `ord I = m ≥ 1` (`ord_W`; for `s = m!` this is
  [Kol07, Theorem 54.2 (i)]), and `s ≤ ord W_s(I) ↔ m ≤ ord I` for `s ≥ 1` (`le_ord_W_iff`: the
  cosupports of `(W_s(I), s)` and `(I, m)` agree);
* (99.4) `MC_s(W_s(I)) = W_1(I) = MC_m(I)` (`MC_W`) and (99.5) `W_s(I)` is MC-invariant
  (`isMCInvariant_W`);
* Claim 99.9 in the weight language (`exists_le_wt_eq`: every exponent vector of weight
  `≥ (r + m − 1) L_m`, with `L_m = lcm(2, …, m)`, has a sub-vector of weight exactly `r L_m`) and
  its consequences (99.6) `W_s(I) · W_t(I) = W_{s+t}(I)` for `s = r L_m` and `t ≥ (m − 1) L_m`
  (`W_mul_W_eq`), (99.7) `W_s(I)ʲ = W_{js}(I)` for `s = r L_m`, `r ≥ m − 1` (`W_pow`), and (99.8)
  `W_s(I)` is D-balanced for such `s` (`isDBalanced_W`).

Conventions: indices are zero-based; `MC_m(I) = D^{m−1}(I)` is the maximal-contact ideal of
`Hironaka/Algebra/Local/MaximalContact.lean`; D-balanced and MC-invariant are `IsDBalanced`
(`Hironaka/Algebra/Local/Balanced.lean`) and `IsMCInvariant`
(`Hironaka/Algebra/Local/MaximalContact.lean`).

Used for the maximal coefficient ideal sheaf and Theorem 100
(`Hironaka/Resolution/Algebraic/Tuning/Sheaf.lean`,
`Hironaka/Resolution/Algebraic/Tuning/Cosupport.lean`,
`Hironaka/Resolution/Algebraic/Tuning/MCTuned.lean`,
`Hironaka/Resolution/Algebraic/Tuning/Corollary101.lean`,
`Hironaka/Resolution/Algebraic/Tuning/Parameter.lean`), for the tuning parameter
(`Hironaka/Algebra/Local/TuningParam.lean`) and on manifolds
(`Hironaka/Manifold/IdealSheaf/TuningLemmas.lean`).
-/

@[expose] public section

namespace IsLocalRing

open IsLocalRing

/-- The **weight** `∑ⱼ (m − j) cⱼ` of an exponent vector `c : {0, …, m} → ℕ`
([Kol07, Definition 98]). -/
def wt (m : ℕ) (e : Fin (m + 1) → ℕ) : ℕ := ∑ j : Fin (m + 1), (m - (j : ℕ)) * e j

theorem wt_add (m : ℕ) (e e' : Fin (m + 1) → ℕ) : wt m (e + e') = wt m e + wt m e' := by
  simp [wt, mul_add, Finset.sum_add_distrib]

theorem wt_single (m : ℕ) (j : Fin (m + 1)) (k : ℕ) : wt m (Pi.single j k) = (m - (j : ℕ)) * k := by
  unfold wt
  rw [Finset.sum_eq_single j (fun j' _ hj' => by simp [hj']) (by simp)]
  simp

/-! ### Claim 99.9 -/

/-- `L_m = lcm(2, …, m)`, with `L_1 = 1` ([Kol07, Claim 99.9]). -/
def Lcm (m : ℕ) : ℕ := (Finset.Icc 2 m).lcm id

theorem Lcm_pos (m : ℕ) : 0 < Lcm m := by
  rw [Nat.pos_iff_ne_zero, Lcm, Ne, Finset.lcm_eq_zero_iff]
  rintro ⟨x, hx, hx0⟩
  rw [Finset.mem_Icc] at hx
  simp only [id] at hx0
  omega

/-- Every `w` with `1 ≤ w ≤ m` divides `L_m`. -/
theorem dvd_Lcm {m w : ℕ} (h1 : 1 ≤ w) (h2 : w ≤ m) : w ∣ Lcm m := by
  rcases Nat.eq_or_lt_of_le h1 with rfl | h1'
  · exact one_dvd _
  · exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨h1', h2⟩)

/-- A vector bounded by `b` with a prescribed sum `r ≤ ∑ b` (Kollár's "choose `0 ≤ dᵢ ≤ bᵢ` such
that `∑ dᵢ = r`" in the proof of Claim 99.9). -/
theorem exists_le_sum_eq {ι : Type*} [Fintype ι] (b : ι → ℕ) (r : ℕ)
    (hr : r ≤ ∑ i, b i) : ∃ d : ι → ℕ, d ≤ b ∧ ∑ i, d i = r := by
  classical
  induction r with
  | zero => exact ⟨0, fun _ => Nat.zero_le _, by simp⟩
  | succ r ih =>
    obtain ⟨d, hdb, hd⟩ := ih (Nat.le_of_succ_le hr)
    have hex : ∃ i, d i < b i := by
      by_contra hcon
      push Not at hcon
      have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hcon i
      omega
    obtain ⟨i, hi⟩ := hex
    refine ⟨d + Pi.single i 1, fun j => ?_, ?_⟩
    · by_cases hj : j = i
      · subst hj
        simp only [Pi.add_apply, Pi.single_eq_same]
        omega
      · simp only [Pi.add_apply, Pi.single_eq_of_ne hj, add_zero]
        exact hdb j
    · simp only [Pi.add_apply]
      rw [Finset.sum_add_distrib, hd, Finset.sum_pi_single']
      simp

/-- [Kol07, Claim 99.9] in the weight language of Definition 98 (Kollár's variable `uᵢ` of degree
`i` is `D^{m−i} I`, `dᵢ = c_{m−i}`, `deg d = wt_m c`; the index `m`, of weight `0`, is ignored):
every exponent vector `e` with `wt e ≥ (r + m − 1) L_m` has a sub-vector `e' ≤ e` with
`wt e' = r L_m`.  Proof as Kollár's: write `eⱼ = bⱼ (L_m/wⱼ) + fⱼ` with `wⱼ fⱼ < L_m`
(`wⱼ = m − j`); if `∑ bⱼ ≥ r` pick `d ≤ b` with `∑ d = r` and `e'ⱼ = dⱼ L_m/wⱼ`; otherwise
`wt e < (r − 1) L_m + m L_m`, a contradiction. -/
theorem exists_le_wt_eq {m : ℕ} (hm : 1 ≤ m) (r : ℕ) {e : Fin (m + 1) → ℕ}
    (he : (r + m - 1) * Lcm m ≤ wt m e) :
    ∃ e' : Fin (m + 1) → ℕ, e' ≤ e ∧ wt m e' = r * Lcm m := by
  classical
  have hL0 : 0 < Lcm m := Lcm_pos m
  obtain ⟨q, hq⟩ : ∃ q : Fin (m + 1) → ℕ, q = fun j : Fin (m + 1) => Lcm m / (m - (j : ℕ)) :=
    ⟨_, rfl⟩
  obtain ⟨bq, hbq⟩ : ∃ bq : Fin (m + 1) → ℕ, bq = fun j => e j / q j := ⟨_, rfl⟩
  obtain ⟨rem, hrem⟩ : ∃ rem : Fin (m + 1) → ℕ, rem = fun j => e j % q j := ⟨_, rfl⟩
  have hwq : ∀ j : Fin (m + 1), (j : ℕ) < m → (m - (j : ℕ)) * q j = Lcm m := fun j hj => by
    rw [hq]
    exact Nat.mul_div_cancel' (dvd_Lcm (by omega) (Nat.sub_le m j))
  have hb0 : ∀ j : Fin (m + 1), m ≤ (j : ℕ) → bq j = 0 := fun j hj => by
    rw [hbq, hq]
    simp [Nat.sub_eq_zero_of_le hj]
  have hkey : ∀ j : Fin (m + 1), (m - (j : ℕ)) * e j = bq j * Lcm m + (m - (j : ℕ)) * rem j := by
    intro j
    rcases Nat.lt_or_ge (j : ℕ) m with hj | hj
    · have hdm := Nat.div_add_mod (e j) (q j)
      rw [hbq, hrem]
      simp only
      calc (m - (j : ℕ)) * e j = (m - (j : ℕ)) * (q j * (e j / q j) + e j % q j) := by rw [hdm]
        _ = e j / q j * ((m - (j : ℕ)) * q j) + (m - (j : ℕ)) * (e j % q j) := by ring
        _ = _ := by rw [hwq j hj]
    · rw [hb0 j hj, Nat.sub_eq_zero_of_le hj]
      simp
  have hbound : ∀ j : Fin (m + 1), (j : ℕ) < m → (m - (j : ℕ)) * rem j < Lcm m := by
    intro j hj
    have hqpos : 0 < q j := by
      rcases Nat.eq_zero_or_pos (q j) with h0 | h0
      · have := hwq j hj
        rw [h0, mul_zero] at this
        omega
      · exact h0
    calc (m - (j : ℕ)) * rem j < (m - (j : ℕ)) * q j := by
          rw [hrem]
          exact Nat.mul_lt_mul_of_pos_left (Nat.mod_lt _ hqpos) (by omega)
      _ = Lcm m := hwq j hj
  have hwt : wt m e = (∑ j, bq j) * Lcm m + ∑ j : Fin (m + 1), (m - (j : ℕ)) * rem j := by
    unfold wt
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => hkey j
  rcases Nat.lt_or_ge (∑ j, bq j) r with hr | hr
  swap
  · obtain ⟨d, hdb, hd⟩ := exists_le_sum_eq bq r hr
    refine ⟨fun j => d j * q j, fun j => ?_, ?_⟩
    · calc d j * q j ≤ bq j * q j := Nat.mul_le_mul_right _ (hdb j)
        _ ≤ e j := by rw [hbq]; exact Nat.div_mul_le_self _ _
    · unfold wt
      calc ∑ j : Fin (m + 1), (m - (j : ℕ)) * (d j * q j) = ∑ j : Fin (m + 1), d j * Lcm m := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rcases Nat.lt_or_ge (j : ℕ) m with hj | hj
            · rw [← hwq j hj]
              ring
            · have hd0 : d j = 0 := by
                have := Pi.le_def.mp hdb j
                rw [hb0 j hj] at this
                omega
              rw [hd0, Nat.sub_eq_zero_of_le hj]
              simp
        _ = r * Lcm m := by rw [← Finset.sum_mul, hd]
  · exfalso
    have hsum : ∑ j : Fin (m + 1), (m - (j : ℕ)) * rem j < m * Lcm m := by
      rw [Fin.sum_univ_castSucc]
      have hlast : (m - ((Fin.last m : Fin (m + 1)) : ℕ)) * rem (Fin.last m) = 0 := by simp
      rw [hlast, add_zero]
      calc ∑ i : Fin m, (m - ((Fin.castSucc i : Fin (m + 1)) : ℕ)) * rem (Fin.castSucc i)
          ≤ ∑ _i : Fin m, (Lcm m - 1) := Finset.sum_le_sum fun i _ => by
            have := hbound (Fin.castSucc i) (by simp)
            omega
        _ = m * (Lcm m - 1) := by simp
        _ < m * Lcm m := Nat.mul_lt_mul_of_pos_left (Nat.sub_lt hL0 Nat.one_pos) hm
    have h1 : (∑ j, bq j) * Lcm m ≤ (r - 1) * Lcm m := Nat.mul_le_mul_right _ (by omega)
    have h2 : (r - 1) * Lcm m + m * Lcm m = (r + m - 1) * Lcm m := by
      rw [← Nat.add_mul]
      congr 1
      omega
    omega

namespace RegularCoords

variable {R : Type*} [CommRing R] [IsRegularLocalRing R] [Algebra ℚ R] {n : ℕ}
  (c : RegularCoords R n)

/-- The **maximal coefficient ideal** of order `s` ([Kol07, Definition 98]),
`W_s(I) = ∑_{wt c ≥ s} ∏ⱼ (Dʲ I)^{cⱼ}`, with the parameter `m` (Kollár's `max-ord I`) explicit. -/
def W (m s : ℕ) (I : Ideal R) : Ideal R :=
  ⨆ (e : Fin (m + 1) → ℕ) (_ : s ≤ wt m e), ∏ j : Fin (m + 1), c.Dpow j I ^ e j

theorem prod_le_W {m s : ℕ} {e : Fin (m + 1) → ℕ} (he : s ≤ wt m e) (I : Ideal R) :
    ∏ j : Fin (m + 1), c.Dpow j I ^ e j ≤ c.W m s I :=
  le_iSup₂_of_le e he le_rfl

theorem W_le_iff {m s : ℕ} {I J : Ideal R} :
    c.W m s I ≤ J ↔ ∀ e : Fin (m + 1) → ℕ, s ≤ wt m e → ∏ j : Fin (m + 1), c.Dpow j I ^ e j ≤ J :=
  iSup₂_le_iff

/-- `W_0(I) = R`. -/
@[simp]
theorem W_zero (m : ℕ) (I : Ideal R) : c.W m 0 I = ⊤ := by
  refine top_le_iff.mp ?_
  have := c.prod_le_W (e := (0 : Fin (m + 1) → ℕ)) (Nat.zero_le _) I
  simpa [Ideal.top_pow] using this

/-- `Iᵏ ≤ W_s(I)` whenever `m k ≥ s`. -/
theorem pow_le_W {m s k : ℕ} (h : s ≤ m * k) (I : Ideal R) : I ^ k ≤ c.W m s I := by
  have hw : s ≤ wt m (Pi.single (0 : Fin (m + 1)) k) := by
    rw [wt_single]
    simpa using h
  refine le_trans ?_ (c.prod_le_W hw I)
  rw [Finset.prod_eq_single (0 : Fin (m + 1)) (fun j _ hj => by simp [hj])
    (by simp)]
  simp

/-- `I^⌈s/m⌉ ≤ W_s(I)` for `m ≥ 1`. -/
theorem pow_ceil_le_W {m s : ℕ} (hm : 1 ≤ m) (I : Ideal R) :
    I ^ ((s + m - 1) / m) ≤ c.W m s I := by
  refine c.pow_le_W ?_ I
  have h1 := Nat.lt_mul_div_succ (s + m - 1) hm
  rw [Nat.mul_succ] at h1
  generalize m * ((s + m - 1) / m) = t at h1 ⊢
  omega

/-- `MC_m(I)ˢ ≤ W_s(I)`: the exponent vector `c_{m−1} = s` has weight `s` (Kollár's
`x₁^{s+1} ∈ W_{s+1}(I)` in the proof of [Kol07, Proposition 99]). -/
theorem MC_pow_le_W {m : ℕ} (hm : 1 ≤ m) (s : ℕ) (I : Ideal R) : c.MC I m ^ s ≤ c.W m s I := by
  have hw : s ≤ wt m (Pi.single (⟨m - 1, by omega⟩ : Fin (m + 1)) s) := by
    rw [wt_single]
    simp only
    rw [Nat.sub_sub_self hm, one_mul]
  refine le_trans ?_ (c.prod_le_W hw I)
  rw [Finset.prod_eq_single (⟨m - 1, by omega⟩ : Fin (m + 1))
    (fun j _ hj => by simp [hj]) (by simp)]
  simp [MC]

/-- `hˢ ∈ W_s(I)` for `h ∈ MC_m(I)`. -/
theorem pow_mem_W {m : ℕ} (hm : 1 ≤ m) {s : ℕ} {I : Ideal R} {h : R} (hh : h ∈ c.MC I m) :
    h ^ s ∈ c.W m s I :=
  c.MC_pow_le_W hm s I (Ideal.pow_mem_pow hh s)

/-- `W_1(I) = D^{m−1} I = MC_m(I)` for `m ≥ 1` (the proof of (99.4) in
[Kol07, Proposition 99]). -/
theorem W_one {m : ℕ} (hm : 1 ≤ m) (I : Ideal R) : c.W m 1 I = c.MC I m := by
  refine le_antisymm (c.W_le_iff.mpr fun e he => ?_) (by simpa using c.MC_pow_le_W hm 1 I)
  obtain ⟨j, hj⟩ : ∃ j : Fin (m + 1), 1 ≤ (m - (j : ℕ)) * e j := by
    by_contra hcon
    push Not at hcon
    have : wt m e = 0 := Finset.sum_eq_zero fun j _ => by have := hcon j; omega
    omega
  have hjm : (j : ℕ) < m := by
    by_contra h'
    push Not at h'
    rw [Nat.sub_eq_zero_of_le h', zero_mul] at hj
    omega
  have hej : e j ≠ 0 := by
    rintro h0
    rw [h0, mul_zero] at hj
    omega
  calc ∏ j' : Fin (m + 1), c.Dpow j' I ^ e j'
      ≤ c.Dpow j I ^ e j := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
        exact Ideal.mul_le_left
    _ ≤ c.Dpow j I := Ideal.pow_le_self hej
    _ ≤ c.Dpow (m - 1) I := c.Dpow_mono_left (by omega) I

/-- If `ord I < m` then `W_s(I) = R` for every `s`, since `MC_m(I) = R` ([Kol07, Lemma 74 (3)]
locally). -/
theorem W_eq_top_of_ord_lt {m : ℕ} (hm : 1 ≤ m) {I : Ideal R} (h : ord I < m) (s : ℕ) :
    c.W m s I = ⊤ := by
  have := c.MC_pow_le_W hm s I
  rw [c.MC_eq_top_of_ord_lt hm h, Ideal.top_pow] at this
  exact top_le_iff.mp this

/-! ### Proposition 99 (1)–(3) -/

section Prop99

theorem W_anti {m s t : ℕ} (h : s ≤ t) (I : Ideal R) : c.W m t I ≤ c.W m s I :=
  c.W_le_iff.mpr fun _ he => c.prod_le_W (h.trans he) I

/-- [Kol07, (99.1)]: `W_{s+1}(I) ≤ W_s(I)`. -/
theorem W_succ_le (m s : ℕ) (I : Ideal R) : c.W m (s + 1) I ≤ c.W m s I :=
  c.W_anti (Nat.le_succ s) I

/-- [Kol07, (99.2)]: `W_s(I) · W_t(I) ≤ W_{s+t}(I)`. -/
theorem W_mul_le (m s t : ℕ) (I : Ideal R) : c.W m s I * c.W m t I ≤ c.W m (s + t) I := by
  unfold W
  rw [Ideal.iSup_mul]
  refine iSup_le fun e => ?_
  rw [Ideal.iSup_mul]
  refine iSup_le fun he => ?_
  rw [Ideal.mul_iSup]
  refine iSup_le fun e' => ?_
  rw [Ideal.mul_iSup]
  refine iSup_le fun he' => ?_
  rw [← Finset.prod_mul_distrib]
  refine le_iSup₂_of_le (e + e') (by rw [wt_add]; omega) (le_of_eq ?_)
  exact Finset.prod_congr rfl fun j _ => by rw [Pi.add_apply, pow_add]

/-- A single generator: `(Dʲ I)^k ≤ W_{(m-j)k}(I)`. -/
theorem Dpow_pow_le_W (m : ℕ) (j : Fin (m + 1)) (k : ℕ) (I : Ideal R) :
    c.Dpow j I ^ k ≤ c.W m ((m - (j : ℕ)) * k) I := by
  refine le_trans (le_of_eq ?_) (c.prod_le_W (e := Pi.single j k) (by rw [wt_single]) I)
  rw [Finset.prod_eq_single j (fun j' _ hj' => by simp [hj']) (by simp)]
  simp

theorem Dpow_le_W_of_le {m j : ℕ} (hj : j ≤ m) (I : Ideal R) : c.Dpow j I ≤ c.W m (m - j) I := by
  have := c.Dpow_pow_le_W m ⟨j, by omega⟩ 1 I
  simpa using this

theorem D_Dpow_le_W (m : ℕ) (j : Fin (m + 1)) (I : Ideal R) :
    c.D (c.Dpow j I) ≤ c.W m (m - (j : ℕ) - 1) I := by
  rw [← Dpow_succ]
  rcases Nat.lt_or_ge (j : ℕ) m with hj | hj
  · exact c.Dpow_le_W_of_le hj I
  · have hjm : (j : ℕ) = m := le_antisymm (Nat.lt_succ_iff.mp j.isLt) hj
    rw [hjm, Nat.sub_self, Nat.zero_sub, W_zero]
    exact le_top

/-- The product rule for one generator: `D((Dʲ I)^k) ≤ W_{(m-j)k - 1}(I)`. -/
theorem D_Dpow_pow_le_W (m : ℕ) (j : Fin (m + 1)) (k : ℕ) (I : Ideal R) :
    c.D (c.Dpow j I ^ k) ≤ c.W m ((m - (j : ℕ)) * k - 1) I := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [D_top]
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    refine (c.D_pow_le _ hk).trans ?_
    rw [Nat.add_sub_cancel]
    refine ((Ideal.mul_mono (c.D_Dpow_le_W m j I) (c.Dpow_pow_le_W m j k' I)).trans
      (c.W_mul_le _ _ _ I)).trans (c.W_anti ?_ I)
    generalize m - (j : ℕ) = a
    rw [Nat.mul_add, Nat.mul_one]
    generalize a * k' = t
    omega

/-- A product of generators lies in `W` of its weight. -/
theorem prod_le_W_sum (m : ℕ) (s : Finset (Fin (m + 1))) (e : Fin (m + 1) → ℕ) (I : Ideal R) :
    ∏ l ∈ s, c.Dpow l I ^ e l ≤ c.W m (∑ l ∈ s, (m - (l : ℕ)) * e l) I := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (Ideal.mul_mono (c.Dpow_pow_le_W m a (e a) I) ih).trans (c.W_mul_le _ _ _ I)

/-- The product rule for a product of generators (Kollár's "follows from the product rule" in the
proof of [Kol07, Proposition 99]): `D(∏ (Dˡ I)^{eₗ}) ≤ W_{wt(e) − 1}(I)`. -/
theorem D_prod_le_W (m : ℕ) (s : Finset (Fin (m + 1))) (e : Fin (m + 1) → ℕ) (I : Ideal R) :
    c.D (∏ l ∈ s, c.Dpow l I ^ e l) ≤ c.W m ((∑ l ∈ s, (m - (l : ℕ)) * e l) - 1) I := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [D_top]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    refine (c.D_mul_le _ _).trans (sup_le ?_ ?_)
    · refine ((Ideal.mul_mono (c.D_Dpow_pow_le_W m a (e a) I) (c.prod_le_W_sum m s e I)).trans
        (c.W_mul_le _ _ _ I)).trans (c.W_anti ?_ I)
      generalize (m - (a : ℕ)) * e a = A
      generalize (∑ l ∈ s, (m - (l : ℕ)) * e l) = S
      omega
    · refine ((Ideal.mul_mono (c.Dpow_pow_le_W m a (e a) I) ih).trans
        (c.W_mul_le _ _ _ I)).trans (c.W_anti ?_ I)
      generalize (m - (a : ℕ)) * e a = A
      generalize (∑ l ∈ s, (m - (l : ℕ)) * e l) = S
      omega

/-- The inclusion `⊆` of [Kol07, (99.3)], by the product rule: `D(W_{s+1}(I)) ≤ W_s(I)`. -/
theorem D_W_succ_le (m s : ℕ) (I : Ideal R) : c.D (c.W m (s + 1) I) ≤ c.W m s I := by
  unfold W
  rw [D_iSup]
  refine iSup_le fun e => ?_
  rw [D_iSup]
  refine iSup_le fun he => ?_
  refine (c.D_prod_le_W m Finset.univ e I).trans (c.W_anti ?_ I)
  unfold wt at he
  omega

/-- An element of `𝔪 ∖ 𝔪²` has a coordinate partial that is a unit (the contrapositive of
`mem_maximalIdeal_sq_of_pderiv_mem`, `Hironaka/Algebra/Local/Coords.lean`): Kollár's `∂/∂x₁` in the
proof of [Kol07, Proposition 99] is `u⁻¹ ∂ᵢ` for such an `i`, with `∂ᵢ x₁ = u`. -/
theorem exists_isUnit_pderiv {h : R} (hh : h ∈ maximalIdeal R) (hh' : h ∉ maximalIdeal R ^ 2) :
    ∃ i, IsUnit (c.pderiv i h) := by
  by_contra hcon
  push Not at hcon
  refine hh' (c.mem_maximalIdeal_sq_of_pderiv_mem hh fun i => ?_)
  by_contra hx
  exact hcon i (IsLocalRing.notMem_maximalIdeal.mp hx)

/-- Kollár's "Pick `x₁ ∈ MC(I)` that has order 1" (the proof of [Kol07, Proposition 99]): for
`ord I = m ≥ 1` there are `x₁ ∈ MC_m(I)` of order `1` and a derivation `∂` with `∂ x₁ = 1` mapping
every ideal `J` into `D J`, namely `∂ = u⁻¹ ∂ᵢ` for an `i` with `∂ᵢ x₁ = u` a unit. No hypothesis
that the `∂ᵢ` span the derivations is needed. -/
theorem exists_maximalContact_deriv {I : Ideal R} {m : ℕ} (hm : 1 ≤ m) (hI : ord I = m) :
    ∃ h ∈ c.MC I m, ordElem h = 1 ∧
      ∃ δ : Derivation ℚ R R, δ h = 1 ∧ ∀ (J : Ideal R) (f : R), f ∈ J → δ f ∈ c.D J := by
  obtain ⟨h, hmem, hh⟩ := c.exists_mem_MC_ordElem_eq_one hm hI
  obtain ⟨hh1, hh2⟩ := ordElem_eq_one_iff.mp hh
  obtain ⟨i, hu⟩ := c.exists_isUnit_pderiv hh1 hh2
  refine ⟨h, hmem, hh, (↑hu.unit⁻¹ : R) • c.pderiv i, ?_, fun J f hf => ?_⟩
  · rw [Derivation.smul_apply, smul_eq_mul, IsUnit.val_inv_mul]
  · rw [Derivation.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_left _ _ (c.pderiv_mem_D hf i)

/-- (The proof of [Kol07, Proposition 99].) `x₁ˢ = (s+1)⁻¹ ∂(x₁^{s+1}) ∈ D(W_{s+1}(I))`. -/
theorem pow_mem_D_W_succ {m : ℕ} (hm : 1 ≤ m) {I : Ideal R} {h : R} (hh : h ∈ c.MC I m)
    {δ : Derivation ℚ R R} (h1 : δ h = 1) (hD : ∀ (J : Ideal R) (f : R), f ∈ J → δ f ∈ c.D J)
    (s : ℕ) : h ^ s ∈ c.D (c.W m (s + 1) I) := by
  have hmem := hD _ _ (c.pow_mem_W hm hh (s := s + 1))
  rw [Derivation.leibniz_pow, h1, smul_eq_mul, mul_one, Nat.add_sub_cancel, nsmul_eq_mul] at hmem
  have hu : IsUnit ((s + 1 : ℕ) : R) := isUnit_natCast R (Nat.succ_ne_zero s)
  have := Ideal.mul_mem_left _ (↑hu.unit⁻¹ : R) hmem
  rwa [← mul_assoc, IsUnit.val_inv_mul, one_mul] at this

/-- (The proof of [Kol07, Proposition 99].) `x₁^{s−t} W_t(I) ≤ D(W_{s+1}(I))` for `t ≤ s`, by
induction on `t`. -/
theorem pow_mul_mem_D_W_succ {m : ℕ} (hm : 1 ≤ m) {I : Ideal R} {h : R} (hh : h ∈ c.MC I m)
    {δ : Derivation ℚ R R} (h1 : δ h = 1) (hD : ∀ (J : Ideal R) (f : R), f ∈ J → δ f ∈ c.D J)
    (s : ℕ) : ∀ t ≤ s, ∀ f ∈ c.W m t I, h ^ (s - t) * f ∈ c.D (c.W m (s + 1) I) := by
  intro t
  induction t with
  | zero =>
    intro _ f _
    exact Ideal.mul_mem_right _ _ (c.pow_mem_D_W_succ hm hh h1 hD s)
  | succ t ih =>
    intro ht f hf
    have hmul : h ^ (s - t) * f ∈ c.W m (s + 1) I := by
      have := Ideal.mul_mem_mul (c.pow_mem_W hm hh (s := s - t)) hf
      exact ((c.W_mul_le m (s - t) (t + 1) I).trans (c.W_anti (by omega) I)) this
    have hder := hD _ _ hmul
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, Derivation.leibniz_pow, h1, smul_eq_mul,
      mul_one, nsmul_eq_mul] at hder
    have h2 : h ^ (s - t) * δ f ∈ c.D (c.W m (s + 1) I) :=
      ih (by omega) (δ f) (c.D_W_succ_le m t I (hD _ _ hf))
    have h3 := Ideal.sub_mem _ hder h2
    rw [add_sub_cancel_left] at h3
    have hu : IsUnit ((s - t : ℕ) : R) := isUnit_natCast R (by omega)
    have h4 := Ideal.mul_mem_left _ (↑hu.unit⁻¹ : R) h3
    have heq : (↑hu.unit⁻¹ : R) * (f * (((s - t : ℕ) : R) * h ^ (s - t - 1))) =
        h ^ (s - (t + 1)) * f := by
      rw [← Nat.sub_sub]
      calc _ = (↑hu.unit⁻¹ * ((s - t : ℕ) : R)) * (h ^ (s - t - 1) * f) := by ring
        _ = _ := by rw [IsUnit.val_inv_mul, one_mul]
    rwa [heq] at h4

/-- [Kol07, (99.3)]: `D(W_{s+1}(I)) = W_s(I)` for `ord I ≤ m`, `m ≥ 1`. -/
theorem D_W_succ {m : ℕ} (hm : 1 ≤ m) {I : Ideal R} (hI : ord I ≤ m) (s : ℕ) :
    c.D (c.W m (s + 1) I) = c.W m s I := by
  refine le_antisymm (c.D_W_succ_le m s I) ?_
  rcases hI.lt_or_eq with hlt | heq
  · rw [c.W_eq_top_of_ord_lt hm hlt, c.W_eq_top_of_ord_lt hm hlt, D_top]
  · obtain ⟨h, hh, -, δ, h1, hD⟩ := c.exists_maximalContact_deriv hm heq
    intro f hf
    have := c.pow_mul_mem_D_W_succ hm hh h1 hD s s le_rfl f hf
    rwa [Nat.sub_self, pow_zero, one_mul] at this

/-- (99.3) iterated, Kollár's "applying (3) repeatedly": `Dⁱ(W_s(I)) = W_{s−i}(I)` for `i ≤ s`. -/
theorem Dpow_W {m : ℕ} (hm : 1 ≤ m) {I : Ideal R} (hI : ord I ≤ m) {i s : ℕ} (hi : i ≤ s) :
    c.Dpow i (c.W m s I) = c.W m (s - i) I := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Dpow_succ, ih (by omega)]
    obtain ⟨k, hk⟩ : ∃ k, s - i = k + 1 := ⟨s - i - 1, by omega⟩
    rw [hk, c.D_W_succ hm hI k, show s - (i + 1) = k by omega]

end Prop99

/-! ### The order of `W_s(I)` -/

section OrderW

/-- Every generator of `W_s(I)` lies in `𝔪^{wt(e)}` when `I ≤ 𝔪ᵐ`, since `Dʲ I ≤ 𝔪^{m−j}` (the
estimate in the proof of [Kol07, Theorem 100]). -/
theorem prod_le_maximalIdeal_pow {m : ℕ} {I : Ideal R} (hI : I ≤ maximalIdeal R ^ m)
    (e : Fin (m + 1) → ℕ) : ∏ j : Fin (m + 1), c.Dpow j I ^ e j ≤ maximalIdeal R ^ wt m e := by
  classical
  unfold wt
  rw [← Finset.prod_pow_eq_pow_sum]
  induction (Finset.univ : Finset (Fin (m + 1))) using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    refine Ideal.mul_mono ?_ ih
    rw [pow_mul]
    exact Ideal.pow_right_mono ((c.Dpow_mono _ hI).trans
      (c.Dpow_maximalIdeal_pow (Nat.lt_succ_iff.mp a.isLt))) _

theorem W_le_maximalIdeal_pow {m s : ℕ} {I : Ideal R} (hI : I ≤ maximalIdeal R ^ m) :
    c.W m s I ≤ maximalIdeal R ^ s :=
  c.W_le_iff.mpr fun e he => (c.prod_le_maximalIdeal_pow hI e).trans (Ideal.pow_le_pow_right he)

/-- If `m ≤ ord I` then `s ≤ ord (W_s(I))` (the estimate in the proof of
[Kol07, Theorem 100]). -/
theorem le_ord_W {m : ℕ} {I : Ideal R} (hm : (m : ℕ∞) ≤ ord I) (s : ℕ) :
    (s : ℕ∞) ≤ ord (c.W m s I) :=
  le_ord_iff.mpr (c.W_le_maximalIdeal_pow (le_ord_iff.mp hm))

/-- If `ord I = m ≥ 1` then `ord (W_s(I)) ≤ s`, since `Dˢ(W_s(I)) = W_0(I) = R` ((99.3)
iterated) and an ideal whose `s`-th derivative ideal is the unit ideal has order `≤ s`
([Kol07, Lemma 74 (3)] locally). -/
theorem ord_W_le {m : ℕ} (hm : 1 ≤ m) {I : Ideal R} (hI : ord I = m) (s : ℕ) :
    ord (c.W m s I) ≤ s := by
  by_contra hlt
  push Not at hlt
  have h1 : ((s + 1 : ℕ) : ℕ∞) ≤ ord (c.W m s I) := by
    push_cast
    exact (ENat.add_one_le_iff (ENat.natCast_ne_top s)).mpr hlt
  have h2 := (c.le_ord_iff_le_ord_Dpow (c.W m s I) (show s < s + 1 by omega)).mp h1
  rw [c.Dpow_W hm hI.le le_rfl, Nat.sub_self, W_zero, ord_top, Nat.add_sub_cancel_left] at h2
  exact absurd h2 (by simp)

/-- If `ord I = m ≥ 1` then `ord (W_s(I)) = s`; for `s = m!` this is [Kol07, Theorem 54.2 (i)],
locally. -/
theorem ord_W {m : ℕ} (hm : 1 ≤ m) {I : Ideal R} (hI : ord I = m) (s : ℕ) :
    ord (c.W m s I) = s :=
  le_antisymm (c.ord_W_le hm hI s) (c.le_ord_W hI.ge s)

/-- For `s ≥ 1`, `cosupp (W_s(I), s) = cosupp (I, m)`, locally: `s ≤ ord (W_s(I)) ↔ m ≤ ord I`;
no hypothesis `ord I ≤ m` is needed. -/
theorem le_ord_W_iff {m : ℕ} (hm : 1 ≤ m) {I : Ideal R} {s : ℕ} (hs1 : 1 ≤ s) :
    (s : ℕ∞) ≤ ord (c.W m s I) ↔ (m : ℕ∞) ≤ ord I := by
  refine ⟨fun h => ?_, fun h => c.le_ord_W h s⟩
  by_contra hlt
  push Not at hlt
  rw [c.W_eq_top_of_ord_lt hm hlt, ord_top] at h
  have : s ≤ 0 := by exact_mod_cast h
  omega

end OrderW

/-! ### Proposition 99 (4)–(5) -/

section Prop99b

/-- [Kol07, (99.4)]: `MC_s(W_s(I)) = W_1(I) = MC_m(I)` for `s ≥ 1`, `ord I ≤ m`, `m ≥ 1` (the
mark of `W_s(I)` is `s`, its order by `ord_W`). -/
theorem MC_W {m : ℕ} (hm : 1 ≤ m) {I : Ideal R} (hI : ord I ≤ m) {s : ℕ} (hs1 : 1 ≤ s) :
    c.MC (c.W m s I) s = c.MC I m := by
  rw [MC, c.Dpow_W hm hI (Nat.sub_le s 1), Nat.sub_sub_self hs1, c.W_one hm]

/-- [Kol07, (99.5)] (Kollár: "Together with (2) and (3), this implies (5)"): `W_s(I)` is
MC-invariant with respect to `s`: `MC_s(W_s) · D(W_s) = W_1 · W_{s−1} ≤ W_s`. -/
theorem isMCInvariant_W {m : ℕ} (hm : 1 ≤ m) {I : Ideal R} (hI : ord I ≤ m) {s : ℕ}
    (hs1 : 1 ≤ s) : c.IsMCInvariant (c.W m s I) s := by
  unfold IsMCInvariant
  rw [c.MC_W hm hI hs1, ← c.W_one hm]
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  rw [c.D_W_succ hm hI k]
  exact (c.W_mul_le m 1 k I).trans (c.W_anti (by omega) I)

end Prop99b

/-! ### Proposition 99 (6)–(8) -/

section Prop99c

/-- [Kol07, (99.6)] (Kollár: "(6) is implied by (99.9)"): `W_s(I) · W_t(I) = W_{s+t}(I)` for
`s = r L_m` and `t ≥ (m − 1) L_m`. -/
theorem W_mul_W_eq {m : ℕ} (hm : 1 ≤ m) (r t : ℕ) (ht : (m - 1) * Lcm m ≤ t) (I : Ideal R) :
    c.W m (r * Lcm m) I * c.W m t I = c.W m (r * Lcm m + t) I := by
  refine le_antisymm (c.W_mul_le _ _ _ I) (c.W_le_iff.mpr fun e he => ?_)
  have hsplit : (r + m - 1) * Lcm m = r * Lcm m + (m - 1) * Lcm m := by
    rw [← Nat.add_mul]
    congr 1
    omega
  obtain ⟨e', he'e, hwt'⟩ := exists_le_wt_eq hm r (e := e) (by omega)
  have hsub : e = e' + (e - e') := by
    ext j
    have := Pi.le_def.mp he'e j
    simp only [Pi.add_apply, Pi.sub_apply]
    omega
  have hwt2 : t ≤ wt m (e - e') := by
    have : wt m e = wt m e' + wt m (e - e') := by rw [← wt_add, ← hsub]
    omega
  calc ∏ j : Fin (m + 1), c.Dpow j I ^ e j
      = (∏ j : Fin (m + 1), c.Dpow j I ^ e' j) * ∏ j : Fin (m + 1), c.Dpow j I ^ (e - e') j := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [← pow_add]
        congr 1
        have := Pi.le_def.mp he'e j
        simp only [Pi.sub_apply]
        omega
    _ ≤ c.W m (r * Lcm m) I * c.W m t I :=
        Ideal.mul_mono (c.prod_le_W hwt'.ge I) (c.prod_le_W hwt2 I)

/-- `W_a(I)^k ≤ W_{ka}(I)` (99.2 iterated). -/
theorem W_pow_le (m a k : ℕ) (I : Ideal R) : c.W m a I ^ k ≤ c.W m (k * a) I := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.add_mul, Nat.one_mul]
    exact (Ideal.mul_mono ih le_rfl).trans (c.W_mul_le _ _ _ I)

/-- [Kol07, (99.7)]: `W_s(I)ʲ = W_{js}(I)` for `s = r L_m`, `r ≥ m − 1`. -/
theorem W_pow {m : ℕ} (hm : 1 ≤ m) {r : ℕ} (hr : m - 1 ≤ r) (j : ℕ) (I : Ideal R) :
    c.W m (r * Lcm m) I ^ j = c.W m (j * (r * Lcm m)) I := by
  induction j with
  | zero => simp
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · rw [pow_succ, ih, mul_comm (c.W m (j * (r * Lcm m)) I) (c.W m (r * Lcm m) I),
        c.W_mul_W_eq hm r _ ?_ I]
      · congr 1
        ring
      · calc (m - 1) * Lcm m ≤ r * Lcm m := Nat.mul_le_mul_right _ hr
          _ ≤ j * (r * Lcm m) := Nat.le_mul_of_pos_left _ hj

/-- (The proof of (99.8) in [Kol07, Proposition 99].) For `s = r L_m`, `r ≥ m − 1`, `ord I ≤ m`
and `i < s`: `(Dⁱ W_s(I))ˢ = W_{s−i}(I)ˢ ≤ W_{s(s−i)}(I) = W_s(I)^{s−i}`. -/
theorem Dpow_W_pow_le {m : ℕ} (hm : 1 ≤ m) {I : Ideal R} (hI : ord I ≤ m) {r : ℕ}
    (hr : m - 1 ≤ r) {i : ℕ} (hi : i < r * Lcm m) :
    c.Dpow i (c.W m (r * Lcm m) I) ^ (r * Lcm m) ≤ c.W m (r * Lcm m) I ^ (r * Lcm m - i) := by
  rw [c.Dpow_W hm hI hi.le, c.W_pow hm hr]
  exact (c.W_pow_le _ _ _ I).trans
    (le_of_eq (by rw [Nat.mul_comm (r * Lcm m) (r * Lcm m - i)]))

/-- [Kol07, (99.8)]: `W_s(I)` is D-balanced with respect to `s` for `s = r L_m`, `r ≥ m − 1`,
`ord I ≤ m` (the mark `s` is the order of `W_s(I)` by `ord_W` when `s ≥ 1`, that is, `r ≥ 1`). -/
theorem isDBalanced_W {m : ℕ} (hm : 1 ≤ m) {I : Ideal R} (hI : ord I ≤ m) {r : ℕ}
    (hr : m - 1 ≤ r) : c.IsDBalanced (c.W m (r * Lcm m) I) (r * Lcm m) :=
  fun _ hi => c.Dpow_W_pow_le hm hI hr hi

end Prop99c

end RegularCoords

end IsLocalRing
