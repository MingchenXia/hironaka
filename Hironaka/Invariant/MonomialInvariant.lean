/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Combinatorics.Colex
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.WithBot
import Hironaka.Invariant.ResolutionInvariantOrder
set_option autoImplicit false

/-!
# The invariant of a monomial marked ideal: combinatorics of Step 2b

Sources: Włodarczyk 2005 (Step 2b of the proof of the resolution theorem: blowing up the intersection of a minimal
set of divisor members whose exponents add up to the mark), Bierstone--Milman 2003 and Bierstone--Milman 2008 (the
invariant of a monomial marked ideal, whose maximum locus is the next centre).

At a point `x` of the cosupport of a monomial marked ideal `𝔞|_N = ∏_{H ∋ x} 𝓘_H^{a_H}` with mark `d`, the members of
the divisor through `x` are recorded by a finite set `S ⊆ ℕ` of their indices in the divisor sequence, and the exponents by
`a : ℕ → ℕ`.  A subset `K ⊆ S` is *feasible* if `d ≤ ∑_K a`.  The invariant is the largest *key*
`(n - |K|, ∑_K a, K)` of a feasible subset, ordered lexicographically, the subsets themselves colexicographically (`n` is a
bound for the number of members through a point, the dimension).  So the invariant prefers small subsets, then large
sums, then colex-large subsets; the maximizing subset `I` is unique, and its members cut out the centre.

## Main results

* `inv_eq_bot_iff`: the invariant is `⊥` exactly off the cosupport (`∑_S a < d`);
* `exists_top`: on the cosupport the invariant is the key of a feasible `I` that dominates every feasible subset;
* `card_le_of_top`, `sum_erase_lt_of_top`: the top subset has minimal cardinality, so dropping one of its members gives a
  sum `< d`;
* `inv_mono`: fewer members through a point (a nearby point) give a smaller invariant (upper semicontinuity);
* `inv_eq_iff_subset`: a nearby point has the same invariant iff it lies on all members of the top subset (the maximum
  locus is the intersection of those members);
* `inv_lt_of_blowup`: **the drop** -- after blowing up the intersection of the members of the top subset `I`, at a point
  over the centre in the chart of `j₀ ∈ I` the members are among `S \ {j₀}` and the new exceptional index `m`, with the old
  exponents and `a'_m = ∑_I a - d`; the invariant there is strictly smaller;
* `wellFoundedLT_val`: the values are well-founded (colex on `Finset ℕ` is order-isomorphic to `ℕ`), so iterating
  the blowup of the maximum locus terminates.
-/

open Finset

namespace Hironaka.MonomialInvariant

/-- The values of the invariant: lexicographic triples `(n - |K|, ∑_K a, K)`, the last entry ordered colexicographically. -/
abbrev Val := Lex (ℕ × Lex (ℕ × Colex (Finset ℕ)))

/-- The key of a set `K` of members with exponents `a`, for the bound `n` on the number of members through a point. -/
def key (n : ℕ) (a : ℕ → ℕ) (K : Finset ℕ) : Val :=
  toLex (n - #K, toLex (∑ i ∈ K, a i, toColex K))

/-- The feasible sets of members: subsets of `S` whose exponents add up to at least the mark `d`. -/
def feasible (S : Finset ℕ) (a : ℕ → ℕ) (d : ℕ) : Finset (Finset ℕ) :=
  S.powerset.filter fun K => d ≤ ∑ i ∈ K, a i

/-- **The invariant of a monomial marked ideal** at a point with members `S` and exponents `a`: the largest key of a
feasible set (`⊥` if there is none, i.e. off the cosupport). -/
def inv (n : ℕ) (S : Finset ℕ) (a : ℕ → ℕ) (d : ℕ) : WithBot Val :=
  ((feasible S a d).image (key n a)).max

variable {n d : ℕ} {S S' K I : Finset ℕ} {a a' : ℕ → ℕ}

theorem mem_feasible : K ∈ feasible S a d ↔ K ⊆ S ∧ d ≤ ∑ i ∈ K, a i := by
  simp [feasible]

/-- The key determines the set. -/
theorem key_injective : Function.Injective (key n a) := by
  intro K L h
  simpa [key] using congrArg (fun v => ofColex (ofLex (ofLex v).2).2) h

theorem key_lt_key_iff : key n a K < key n a' I ↔
    n - #K < n - #I ∨ n - #K = n - #I ∧ (∑ i ∈ K, a i < ∑ i ∈ I, a' i ∨
      ∑ i ∈ K, a i = ∑ i ∈ I, a' i ∧ toColex K < toColex I) := by
  simp only [key, Prod.Lex.toLex_lt_toLex]

theorem feasible_nonempty_iff : (feasible S a d).Nonempty ↔ d ≤ ∑ i ∈ S, a i := by
  constructor
  · rintro ⟨K, hK⟩
    obtain ⟨hKS, hd⟩ := mem_feasible.mp hK
    exact hd.trans (sum_le_sum_of_subset hKS)
  · intro h
    exact ⟨S, mem_feasible.mpr ⟨subset_rfl, h⟩⟩

/-- The invariant is `⊥` exactly off the cosupport. -/
theorem inv_eq_bot_iff : inv n S a d = ⊥ ↔ ∑ i ∈ S, a i < d := by
  rw [inv, Finset.max_eq_bot, image_eq_empty, ← not_nonempty_iff_eq_empty, feasible_nonempty_iff, not_le]

/-- **The top set**: on the cosupport the invariant is the key of a feasible set dominating every feasible set. -/
theorem exists_top (h : d ≤ ∑ i ∈ S, a i) :
    ∃ I ∈ feasible S a d, inv n S a d = key n a I ∧ ∀ K ∈ feasible S a d, key n a K ≤ key n a I := by
  obtain ⟨I, hI, hmax⟩ := exists_max_image (feasible S a d) (key n a) (feasible_nonempty_iff.mpr h)
  refine ⟨I, hI, le_antisymm (Finset.max_le fun v hv => ?_) (Finset.le_max (mem_image_of_mem _ hI)), hmax⟩
  obtain ⟨K, hK, rfl⟩ := mem_image.mp hv
  exact WithBot.coe_le_coe.mpr (hmax K hK)

/-- A set whose key is the invariant is the top set. -/
theorem eq_of_inv_eq_key (hI : I ∈ feasible S a d) (htop : ∀ K ∈ feasible S a d, key n a K ≤ key n a I)
    {L : Finset ℕ} (hL : inv n S a d = key n a L) : L = I := by
  obtain ⟨K, hK, hKL⟩ := mem_image.mp (Finset.mem_of_max hL)
  have hI' : (key n a I : WithBot Val) ≤ inv n S a d := Finset.le_max (mem_image_of_mem _ hI)
  rw [hL] at hI'
  exact key_injective (le_antisymm (hKL ▸ htop K hK) (WithBot.coe_le_coe.mp hI'))

/-- **The top set has minimal cardinality** among the feasible sets (when at most `n` members pass through the
point). -/
theorem card_le_of_top (hn : #S ≤ n) (hI : I ∈ feasible S a d)
    (htop : ∀ K ∈ feasible S a d, key n a K ≤ key n a I) (hK : K ∈ feasible S a d) : #I ≤ #K := by
  by_contra! hlt
  have hIn : #I ≤ n := (card_le_card (mem_feasible.mp hI).1).trans hn
  have : key n a I < key n a K := key_lt_key_iff.mpr (Or.inl (by omega))
  exact absurd (htop K hK) (not_le.mpr this)

/-- Dropping one member of the top set gives a sum below the mark. -/
theorem sum_erase_lt_of_top (hn : #S ≤ n) (hI : I ∈ feasible S a d)
    (htop : ∀ K ∈ feasible S a d, key n a K ≤ key n a I) {j : ℕ} (hj : j ∈ I) :
    ∑ i ∈ I.erase j, a i < d := by
  by_contra! hle
  have hK : I.erase j ∈ feasible S a d :=
    mem_feasible.mpr ⟨(erase_subset j I).trans (mem_feasible.mp hI).1, hle⟩
  have := card_le_of_top hn hI htop hK
  rw [card_erase_of_mem hj] at this
  have : 0 < #I := card_pos.mpr ⟨j, hj⟩
  omega

/-- **Upper semicontinuity**: fewer members (a nearby point lies on a subset of the members through the point) give a
smaller invariant. -/
theorem inv_mono (hS : S' ⊆ S) : inv n S' a d ≤ inv n S a d := by
  refine Finset.max_mono (image_subset_image fun K hK => ?_)
  obtain ⟨hKS, hd⟩ := mem_feasible.mp hK
  exact mem_feasible.mpr ⟨hKS.trans hS, hd⟩

/-- **The maximum locus**: a nearby point (members `S' ⊆ S`) has the same invariant iff it lies on every member of the
top set. -/
theorem inv_eq_iff_subset (hS : S' ⊆ S) (hI : I ∈ feasible S a d)
    (htop : ∀ K ∈ feasible S a d, key n a K ≤ key n a I) : inv n S' a d = inv n S a d ↔ I ⊆ S' := by
  have hinv : inv n S a d = key n a I := by
    obtain ⟨I', hI', h', htop'⟩ := exists_top (n := n) (feasible_nonempty_iff.mp ⟨I, hI⟩)
    rw [h', eq_of_inv_eq_key hI htop h']
  constructor
  · intro h
    rw [hinv] at h
    obtain ⟨K, hK, hKI⟩ := mem_image.mp (Finset.mem_of_max h)
    exact key_injective hKI ▸ (mem_feasible.mp hK).1
  · intro h
    refine le_antisymm (inv_mono hS) ?_
    rw [hinv]
    exact Finset.le_max (mem_image_of_mem _ (mem_feasible.mpr ⟨h, (mem_feasible.mp hI).2⟩))

/-- **The drop, for one feasible set after the blowup.** -/
theorem key_lt_of_blowup (hn : #S ≤ n) (hI : I ∈ feasible S a d)
    (htop : ∀ K ∈ feasible S a d, key n a K ≤ key n a I) {j₀ m : ℕ} (hj₀ : j₀ ∈ I)
    (hS' : S' ⊆ insert m (S.erase j₀)) (ha' : ∀ i ∈ S, a' i = a i) (hD : a' m + d = ∑ i ∈ I, a i)
    {K' : Finset ℕ} (hK' : K' ∈ feasible S' a' d) : key n a' K' < key n a I := by
  obtain ⟨hK'S', hK'd⟩ := mem_feasible.mp hK'
  have hIS : I ⊆ S := (mem_feasible.mp hI).1
  have hsub : ∀ i ∈ K', i ≠ m → i ∈ S.erase j₀ := fun i hi him => by
    have := hS' (hK'S' hi)
    rcases mem_insert.mp this with h | h
    · exact absurd h him
    · exact h
  by_cases hmK : m ∈ K'
  · -- replace the exceptional member by `j₀`
    set L := K'.erase m with hL
    have hLS : ∀ i ∈ L, i ∈ S.erase j₀ := fun i hi =>
      hsub i (mem_of_mem_erase hi) (ne_of_mem_erase hi)
    have hj₀L : j₀ ∉ L := fun h => (ne_of_mem_erase (hLS j₀ h)) rfl
    set K := insert j₀ L with hK
    have hKS : K ⊆ S := insert_subset (hIS hj₀) fun i hi => mem_of_mem_erase (hLS i hi)
    have hcard : #K = #K' := by
      rw [hK, card_insert_of_notMem hj₀L, hL, card_erase_of_mem hmK]
      have : 0 < #K' := card_pos.mpr ⟨m, hmK⟩
      omega
    have hsumL : ∑ i ∈ L, a' i = ∑ i ∈ L, a i :=
      sum_congr rfl fun i hi => ha' i (mem_of_mem_erase (hLS i hi))
    have hsumK' : ∑ i ∈ K', a' i = a' m + ∑ i ∈ L, a' i := (add_sum_erase K' a' hmK).symm
    have hsumK : ∑ i ∈ K, a i = a j₀ + ∑ i ∈ L, a i := sum_insert hj₀L
    have hlt0 : a' m < a j₀ := by
      have h1 := sum_erase_lt_of_top hn hI htop hj₀
      have h2 : ∑ i ∈ I, a i = a j₀ + ∑ i ∈ I.erase j₀, a i := (add_sum_erase I a hj₀).symm
      omega
    have hlt : ∑ i ∈ K', a' i < ∑ i ∈ K, a i := by omega
    have hKf : K ∈ feasible S a d := mem_feasible.mpr ⟨hKS, by omega⟩
    refine lt_of_lt_of_le (key_lt_key_iff.mpr (Or.inr ⟨by rw [hcard], Or.inl hlt⟩)) (htop K hKf)
  · -- an old feasible set, different from the top set
    have hK'S : K' ⊆ S := fun i hi => mem_of_mem_erase (hsub i hi fun h => hmK (h ▸ hi))
    have hsum : ∑ i ∈ K', a' i = ∑ i ∈ K', a i := sum_congr rfl fun i hi => ha' i (hK'S hi)
    have hKf : K' ∈ feasible S a d := mem_feasible.mpr ⟨hK'S, hsum ▸ hK'd⟩
    have hkey : key n a' K' = key n a K' := by simp only [key, hsum]
    rw [hkey]
    refine lt_of_le_of_ne (htop K' hKf) fun h => ?_
    have hj : j₀ ∉ K' := fun h' => (ne_of_mem_erase (hsub j₀ h' fun h'' => hmK (h'' ▸ h'))) rfl
    exact hj (key_injective h ▸ hj₀)

/-- **The invariant drops under the blowup of the maximum locus** (`hir:monomial-case` (2)): let `I` be the top set at a
point with members `S`, `j₀ ∈ I`, and let a point over the centre (the intersection of the members of `I`) lie in the chart
of `j₀`; its members are among `S \ {j₀}` and the new exceptional index `m`, with the old exponents and the exceptional
exponent `∑_I a - d`.  Then its invariant is strictly smaller. -/
theorem inv_lt_of_blowup (hn : #S ≤ n) (hI : I ∈ feasible S a d)
    (htop : ∀ K ∈ feasible S a d, key n a K ≤ key n a I) {j₀ m : ℕ} (hj₀ : j₀ ∈ I)
    (hS' : S' ⊆ insert m (S.erase j₀)) (ha' : ∀ i ∈ S, a' i = a i) (hD : a' m + d = ∑ i ∈ I, a i) :
    inv n S' a' d < inv n S a d := by
  have hinv : inv n S a d = key n a I := by
    obtain ⟨I', hI', h', htop'⟩ := exists_top (n := n) (feasible_nonempty_iff.mp ⟨I, hI⟩)
    rw [h', eq_of_inv_eq_key hI htop h']
  rw [hinv]
  by_cases h' : d ≤ ∑ i ∈ S', a' i
  · obtain ⟨K', hK', hinv', -⟩ := exists_top (n := n) h'
    rw [hinv']
    exact WithBot.coe_lt_coe.mpr (key_lt_of_blowup hn hI htop hj₀ hS' ha' hD hK')
  · rw [(inv_eq_bot_iff (n := n)).mpr (not_le.mp h')]
    exact WithBot.bot_lt_coe _

/-- **The values are well-founded**: colex on `Finset ℕ` is order-isomorphic to `ℕ` (binary expansion), and
lexicographic products and `WithBot` of well-founded orders are well-founded. Hence the maxima of the invariant,
which strictly decrease under the blowup of the maximum locus, reach `⊥` (empty cosupport) after finitely many
steps. -/
theorem wellFoundedLT_val : WellFoundedLT (WithBot Val) := by
  have : WellFoundedLT (Colex (Finset ℕ)) := (orderIsoColex).symm.strictMono.wellFoundedLT
  infer_instance

end Hironaka.MonomialInvariant
