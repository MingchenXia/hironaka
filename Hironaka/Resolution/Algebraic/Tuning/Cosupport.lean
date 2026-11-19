/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Tuning.Sheaf
import Hironaka.Resolution.Algebraic.Balanced.Order
import Hironaka.Resolution.Algebraic.Tuning.Sequence
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.StalkLe
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The cosupport of the tuned ideal

In Step 1 of the proof of [Kol07, Theorem 103], after tuning, `W_s(I)` is used as an unmarked ideal
of maximal order `s`. The pointwise content, at every point `x` of a smooth variety and for
`m, s ≥ 1`:

* `ord_x I ≥ m ⟹ ord_x W_s(I) ≥ s` (the order estimate `le_ord_W_of_le_ord` of
  `Hironaka.Resolution.Algebraic.Tuning.Sequence`), and
* `ord_x I < m ⟹ W_s(I)_x = 𝒪_x`: `MC(I) = D^{m−1}(I)` has order `0` at `x` ([Kol07, Lemma 74 (3)];
  `ord_MC_eq_zero`), so `MC(I)_x = 𝒪_x`, and `MC(I)^s ⊆ W_s(I)` (`MC_pow_le_W`)
  (`ord_W_eq_zero_of_ord_lt`).

Hence `s ≤ ord_x W_s(I) ⟺ m ≤ ord_x I` (`le_ord_W_iff`): `cosupp(W_s(I), s) = cosupp(I, m)`
(`cosupp_W`), and `W_s(I)` has order `0` or `≥ s` everywhere, so its support, the unmarked
cosupport, is the same set (`support_W`). No coordinates are used (the stalk bridge `stalkIdeal_W`
needs spanning coordinates, which exist at closed points only); the statements hold for every `I`.
At the parameters of Corollary 101 (`s = r·lcm(2, …, m)`, `m = max-ord I`) `support_W` is also
`IsDBalanced.cosupp_eq_support` of `Hironaka.Resolution.Algebraic.Balanced.Order` applied to
`isDBalanced_W`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (I : X.IdealSheafData) (m s : ℕ)

include n

/-- Where `I` has order `< m`, the tuned ideal `W_s(I)` is the unit ideal: `MC(I)_x = 𝒪_x` by
[Kol07, Lemma 74 (3)] and `MC(I)^s ⊆ W_s(I)` (compare [Kol07, Definition 83]). -/
theorem ord_W_eq_zero_of_ord_lt (hm : 1 ≤ m) {x : X} (hx : I.ord x < m) :
    (W f I m s).ord x = 0 := by
  have h1 : (MC f I m).stalkIdeal x = ⊤ :=
    stalkIdeal_eq_top_of_ord_eq_zero (ord_MC_eq_zero f n I hx)
  have h2 : (W f I m s).stalkIdeal x = ⊤ := by
    refine top_le_iff.mp ?_
    calc (⊤ : Ideal _) = (MC f I m ^ s).stalkIdeal x := by rw [stalkIdeal_pow, h1, Ideal.top_pow]
      _ ≤ (W f I m s).stalkIdeal x := stalkIdeal_mono (MC_pow_le_W f hm s I) x
  rw [ord_eq_ord_stalkIdeal, h2, IsLocalRing.ord_top]

/-- For `m, s ≥ 1`, `ord_x W_s(I) ≥ s` iff `ord_x I ≥ m`. -/
theorem le_ord_W_iff (hm : 1 ≤ m) (hs : 1 ≤ s) (x : X) :
    (s : ℕ∞) ≤ (W f I m s).ord x ↔ (m : ℕ∞) ≤ I.ord x := by
  refine ⟨fun h => ?_, fun h => Hironaka.Sequence.le_ord_W_of_le_ord f n I m s x h⟩
  by_contra hlt
  rw [not_le] at hlt
  rw [ord_W_eq_zero_of_ord_lt f n I m s hm hlt] at h
  have hs0 : (s : ℕ∞) = 0 := le_antisymm h bot_le
  rw [Nat.cast_eq_zero] at hs0
  omega

/-- `cosupp(W_s(I), s) = cosupp(I, m)` for `m, s ≥ 1` (Step 1 of the proof of [Kol07, Theorem 103]).
-/
theorem cosupp_W (hm : 1 ≤ m) (hs : 1 ≤ s) :
    {x | (s : ℕ∞) ≤ (W f I m s).ord x} = {x | (m : ℕ∞) ≤ I.ord x} := by
  ext x
  exact le_ord_W_iff f n I m s hm hs x

/-- The support of `W_s(I)` is `cosupp(I, m)`: `W_s(I)` has order `0` or `≥ s` at every point (the
remark "`cosupp(I, m) = cosupp I`" of [Kol07, Definition 83] for the D-balanced `W_s(I)`). At
`s = r·lcm(2, …, m)`, `m = max-ord I`, this is also `IsDBalanced.cosupp_eq_support` for
`isDBalanced_W`. -/
theorem support_W (hm : 1 ≤ m) (hs : 1 ≤ s) :
    ((W f I m s).support : Set X) = {x | (m : ℕ∞) ≤ I.ord x} := by
  ext x
  simp only [SetLike.mem_coe, Set.mem_ofPred_eq]
  rw [← one_le_ord_iff]
  constructor
  · intro h1
    by_contra hlt
    rw [not_le] at hlt
    rw [ord_W_eq_zero_of_ord_lt f n I m s hm hlt] at h1
    exact (not_le.mpr zero_lt_one) h1
  · intro h
    exact le_trans (by exact_mod_cast hs) (Hironaka.Sequence.le_ord_W_of_le_ord f n I m s x h)

end AlgebraicGeometry.Scheme.IdealSheafData
