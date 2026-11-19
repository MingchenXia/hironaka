import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Constructions
import Mathlib.Order.WellFounded
import Mathlib.Order.OrderIsoNat

/-!
# Compatible branches through inverse sequences of compact spaces

The termination step of the global flattening algorithm (Rydh, *Functorial flatification of
proper morphisms*, proof of Theorem 1.1; McQuillan, *Flattening and algebrisation*, Fact 4.2,
"compactness of the Zariski–Riemann surface, or just Tychonoff for the product of the
sequence"): if the closed non-flat loci `Z n` of the successive strict transforms over a
sequence of compact Hausdorff bases `S n` are all nonempty and compatible
(`π n (Z (n+1)) ⊆ Z n`), there is a compatible sequence of points `s n ∈ Z n`, i.e. an infinite
branch.  Contrapositively, if no infinite branch exists (because along a branch some invariant
would decrease forever), then some `Z n` is empty: the algorithm terminates.

This is pure topology (Tychonoff + Cantor's intersection theorem); no complex geometry.

Main declarations:

* `IsBranch π Z s` — `s` is a compatible sequence of points of the `Z n`;
* `exists_isBranch` — nonempty closed compatible subsets of compact Hausdorff spaces carry a
  branch;
* `exists_eq_empty_of_forall_not_isBranch` — termination when no branch exists;
* `exists_eq_empty_of_strictAnti` — termination when a well-founded invariant strictly drops
  along every step inside the `Z n`.
-/

set_option autoImplicit false

open Set

namespace Hironaka.HironakaG10ChowCompactBranch

universe u

variable {S : ℕ → Type u} (π : ∀ n, S (n + 1) → S n)

/-- `s` is a branch through the sets `Z n`: `s n ∈ Z n` and `π n (s (n+1)) = s n` for all `n`. -/
def IsBranch (Z : ∀ n, Set (S n)) (s : ∀ n, S n) : Prop :=
  (∀ n, s n ∈ Z n) ∧ ∀ n, π n (s (n + 1)) = s n

/-- The finite-stage approximations of the set of branches: sequences whose first `N + 1` terms
lie in the `Z n` and are compatible. -/
def stage (Z : ∀ n, Set (S n)) (N : ℕ) : Set (∀ n, S n) :=
  {s | ∀ n, n ≤ N → s n ∈ Z n ∧ (n < N → π n (s (n + 1)) = s n)}

theorem stage_succ_subset (Z : ∀ n, Set (S n)) (N : ℕ) :
    stage π Z (N + 1) ⊆ stage π Z N := by
  intro s hs n hn
  refine ⟨(hs n (Nat.le_succ_of_le hn)).1, fun hlt => ?_⟩
  exact (hs n (Nat.le_succ_of_le hn)).2 (Nat.lt_succ_of_lt hlt)

theorem isClosed_stage [∀ n, TopologicalSpace (S n)] [∀ n, T2Space (S n)]
    (hπ : ∀ n, Continuous (π n)) (Z : ∀ n, Set (S n)) (hZ : ∀ n, IsClosed (Z n)) (N : ℕ) :
    IsClosed (stage π Z N) := by
  have h : stage π Z N = ⋂ n, ⋂ (_ : n ≤ N),
      ((fun s : ∀ k, S k => s n) ⁻¹' Z n ∩
        ⋂ (_ : n < N), {s : ∀ k, S k | π n (s (n + 1)) = s n}) := by
    ext s
    simp only [stage, mem_ofPred_eq, mem_iInter, mem_inter_iff, mem_preimage]
  rw [h]
  refine isClosed_iInter fun n => isClosed_iInter fun _ => ?_
  refine IsClosed.inter ((hZ n).preimage (continuous_apply n)) ?_
  refine isClosed_iInter fun _ => ?_
  exact isClosed_eq ((hπ n).comp (continuous_apply (n + 1))) (continuous_apply n)

/-- Every point of `Z N` is the `N`-th term of an element of the `N`-th stage. -/
theorem exists_mem_stage (Z : ∀ n, Set (S n)) (hZn : ∀ n, (Z n).Nonempty)
    (hZπ : ∀ n, MapsTo (π n) (Z (n + 1)) (Z n)) :
    ∀ (N : ℕ) (z : S N), z ∈ Z N → ∃ s ∈ stage π Z N, s N = z := by
  classical
  intro N
  induction N with
  | zero =>
    intro z hz
    refine ⟨Function.update (fun n => (hZn n).some) 0 z, ?_, Function.update_self _ _ _⟩
    intro n hn
    have hn0 : n = 0 := Nat.le_zero.mp hn
    subst hn0
    refine ⟨?_, fun h => absurd h (Nat.lt_irrefl 0)⟩
    rw [Function.update_self]
    exact hz
  | succ N ih =>
    intro z hz
    obtain ⟨s, hs, hsN⟩ := ih (π N z) (hZπ N hz)
    refine ⟨Function.update s (N + 1) z, ?_, Function.update_self _ _ _⟩
    intro n hn
    rcases Nat.lt_or_ge n (N + 1) with hlt | hge
    · have hnN : n ≤ N := Nat.lt_succ_iff.mp hlt
      have hne : n ≠ N + 1 := Nat.ne_of_lt hlt
      refine ⟨?_, fun _ => ?_⟩
      · rw [Function.update_of_ne hne]
        exact (hs n hnN).1
      · rw [Function.update_of_ne hne]
        rcases Nat.lt_or_ge n N with hlt' | hge'
        · have hne' : n + 1 ≠ N + 1 := fun h => Nat.lt_irrefl N (by omega)
          rw [Function.update_of_ne hne']
          exact (hs n hnN).2 hlt'
        · have hnN' : n = N := le_antisymm hnN hge'
          subst hnN'
          rw [Function.update_self]
          exact hsN.symm
    · have hnN : n = N + 1 := le_antisymm hn hge
      subst hnN
      refine ⟨?_, fun h => absurd h (Nat.lt_irrefl _)⟩
      rw [Function.update_self]
      exact hz

/-- **Compatible branches exist** (König's lemma for compact Hausdorff spaces): nonempty closed
subsets `Z n` of compact Hausdorff spaces `S n`, compatible under continuous maps
`π n : S (n+1) → S n`, carry a branch `s` with `s n ∈ Z n` and `π n (s (n+1)) = s n`. -/
theorem exists_isBranch [∀ n, TopologicalSpace (S n)] [∀ n, CompactSpace (S n)]
    [∀ n, T2Space (S n)] (hπ : ∀ n, Continuous (π n)) (Z : ∀ n, Set (S n))
    (hZ : ∀ n, IsClosed (Z n)) (hZn : ∀ n, (Z n).Nonempty)
    (hZπ : ∀ n, MapsTo (π n) (Z (n + 1)) (Z n)) :
    ∃ s, IsBranch π Z s := by
  have hne : ∀ N, (stage π Z N).Nonempty := fun N => by
    obtain ⟨z, hz⟩ := hZn N
    obtain ⟨s, hs, -⟩ := exists_mem_stage π Z hZn hZπ N z hz
    exact ⟨s, hs⟩
  obtain ⟨s, hs⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (stage π Z) (stage_succ_subset π Z) hne
    (isClosed_stage π hπ Z hZ 0).isCompact (isClosed_stage π hπ Z hZ)
  rw [mem_iInter] at hs
  exact ⟨s, fun n => (hs n n le_rfl).1, fun n => (hs (n + 1) n (Nat.le_succ n)).2 (Nat.lt_succ_self n)⟩

/-- **Termination over compact bases.**  If closed subsets `Z n` of compact Hausdorff spaces are
compatible (`π n (Z (n+1)) ⊆ Z n`) and admit no branch, then some `Z n` is empty. -/
theorem exists_eq_empty_of_forall_not_isBranch [∀ n, TopologicalSpace (S n)]
    [∀ n, CompactSpace (S n)] [∀ n, T2Space (S n)] (hπ : ∀ n, Continuous (π n))
    (Z : ∀ n, Set (S n)) (hZ : ∀ n, IsClosed (Z n))
    (hZπ : ∀ n, MapsTo (π n) (Z (n + 1)) (Z n)) (hno : ∀ s, ¬ IsBranch π Z s) :
    ∃ n, Z n = ∅ := by
  by_contra h
  push Not at h
  obtain ⟨s, hs⟩ := exists_isBranch π hπ Z hZ h hZπ
  exact hno s hs

/-- A strictly decreasing well-founded invariant along the steps inside the `Z n` rules out
branches. -/
theorem not_isBranch_of_strictAnti {α : Type*} [Preorder α] [WellFoundedLT α]
    (Z : ∀ n, Set (S n)) (ν : ∀ n, S n → α)
    (hν : ∀ n (t : S (n + 1)), t ∈ Z (n + 1) → π n t ∈ Z n → ν (n + 1) t < ν n (π n t))
    (s : ∀ n, S n) : ¬ IsBranch π Z s := by
  rintro ⟨hsZ, hsπ⟩
  have hdec : ∀ n, ν (n + 1) (s (n + 1)) < ν n (s n) := fun n => by
    have h := hν n (s (n + 1)) (hsZ (n + 1)) (by rw [hsπ n]; exact hsZ n)
    rwa [hsπ n] at h
  obtain ⟨n, hn⟩ := WellFounded.not_rel_apply_succ (r := (· < ·)) (fun n => ν n (s n))
  exact hn (hdec n)

/-- **Termination by a well-founded invariant over compact bases.** -/
theorem exists_eq_empty_of_strictAnti [∀ n, TopologicalSpace (S n)] [∀ n, CompactSpace (S n)]
    [∀ n, T2Space (S n)] (hπ : ∀ n, Continuous (π n)) {α : Type*} [Preorder α]
    [WellFoundedLT α] (Z : ∀ n, Set (S n)) (hZ : ∀ n, IsClosed (Z n))
    (hZπ : ∀ n, MapsTo (π n) (Z (n + 1)) (Z n)) (ν : ∀ n, S n → α)
    (hν : ∀ n (t : S (n + 1)), t ∈ Z (n + 1) → π n t ∈ Z n → ν (n + 1) t < ν n (π n t)) :
    ∃ n, Z n = ∅ :=
  exists_eq_empty_of_forall_not_isBranch π hπ Z hZ hZπ (not_isBranch_of_strictAnti π Z ν hν)

end Hironaka.HironakaG10ChowCompactBranch
