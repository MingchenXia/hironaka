import Hironaka.Resolution.HironakaG10ChowCompactBranch

/-!
# Tracked rounds give frequent decrease (Hironaka 1975, Lemma 4.6.1 and its iteration)

Module M3 of lane G10H's plan (`work/hironaka-resume-20261111/G10H/HIRONAKA75-GLOBAL-STEP.md` §4;
statement and proof drafted by lane G10H in `G10H/drafts/G10HStatementCheckTN.lean`, landed by G10C).
Hironaka's bookkeeping (pp. 544–546) abstracted to sets: if every round `[r_k, r_{k+1})` starts with all
non-flat points tracked (H1), ends with no non-flat point tracked (H4), and a non-flat point that leaves
the tracked set in a step has a strict fibre decrease at that step (H2), then every branch of non-flat
points decreases infinitely often — the hypothesis `hfreq` of
`HironakaG10ChowSequenceFibreChain.exists_flattening_of_frequentDecrease`.
-/

set_option autoImplicit false

namespace Hironaka.HironakaG10ChowTrackedRounds

open Hironaka.HironakaG10ChowCompactBranch

/-- **Tracked rounds give frequent decrease.** -/
theorem frequently_of_trackedRounds {S : ℕ → Type*} (π : ∀ n, S (n + 1) → S n)
    (Z : ∀ n, Set (S n)) (dec : ∀ n, S (n + 1) → Prop) (r : ℕ → ℕ) (hr : ∀ k, r k < r (k + 1))
    (Tr : ℕ → ∀ n, Set (S n))
    (hstart : ∀ k, Z (r k) ⊆ Tr k (r k))
    (hleave : ∀ k n, r k ≤ n → n < r (k + 1) → ∀ x' ∈ Z (n + 1), π n x' ∈ Tr k n →
      x' ∉ Tr k (n + 1) → dec n x')
    (hend : ∀ k, Z (r (k + 1)) ∩ Tr k (r (k + 1)) = ∅)
    (z : ∀ n, S n) (hz : IsBranch π Z z) :
    ∀ N, ∃ m, N ≤ m ∧ dec m (z (m + 1)) := by
  have hrk : ∀ k, k ≤ r k := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hr k))
  intro N
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  -- inside round `N`, the branch never leaves the tracked set
  have key : ∀ n, r N ≤ n → n ≤ r (N + 1) → z n ∈ Tr N n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => intro _; exact hstart N (hz.1 _)
    | succ n hn ih =>
      intro hle
      have hlt : n < r (N + 1) := hle
      by_contra hout
      have hd := hleave N n hn hlt (z (n + 1)) (hz.1 _) (by rw [hz.2 n]; exact ih hlt.le) hout
      exact hcon n (le_trans (hrk N) hn) hd
  have h1 := key (r (N + 1)) (hr N).le le_rfl
  have h2 : z (r (N + 1)) ∈ Z (r (N + 1)) ∩ Tr N (r (N + 1)) := ⟨hz.1 _, h1⟩
  rw [hend N] at h2
  exact h2

end Hironaka.HironakaG10ChowTrackedRounds
