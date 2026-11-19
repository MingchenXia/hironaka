/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.TuningParam
public import Hironaka.Resolution.Algebraic.Balanced.Basic
public import Hironaka.Resolution.Algebraic.MaximalContact.Invariant
public import Hironaka.Resolution.Algebraic.Tuning.Sheaf
public import Hironaka.Scheme.IdealSheaf.Order.Constructible
import Hironaka.Resolution.Algebraic.Tuning.Corollary101
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The tuning parameter and Corollary 101 at that parameter

The library tunes with the parameter `s(m) = tuningParam m = max (m − 1) 1 · lcm(2, …, m)`, which is
admissible for [Kol07, Corollary 101] for every `m ≥ 1` (it is `r · lcm(2, …, m)` with
`r = max (m − 1) 1 ≥ m − 1`). Kollár takes `s = m!` in the proof of Theorem 103 "to avoid further
choices"; `m!` is of the admissible form when `m ≤ 2` or `m ≥ 6` (by `(m − 1) · lcm(2, …, m) ≤ m!`,
[Kol07, Aside 99.10]; `Hironaka.Algebra.Local.TuningParam`), whereas `s(m)` is admissible for every
`m ≥ 1` without a case distinction. The order reduction of `Hironaka.Sequence` uses exactly:

* the values `s(1) = 1`, `s(2) = 2` (`tuningParam_one`, `tuningParam_two`), and `W_{s(1)}(I) = I`
  (`W_tuningParam_one`: `W_1(I) = MC(I)` with the parameter `1` is `D^0 I = I`, `W_one`), which the
  closed-embedding clauses of [Kol07, Lemma 102 (3)] and [Kol07, Theorem 103 (3)] need, an ideal
  containing the local equations of a hypersurface having order `1` and `I = W(I)`;
* Corollary 101 at `s = s(m)` (Step 1 of the proof of [Kol07, Theorem 103]): order reduction for
  `(X, I, m, E)` is order reduction for `(X, W_{s(m)}(I), s(m), E)` (`tuning_iff_tuningParam`,
  `tuning_iff_E` at `r = max (m − 1) 1`), and `W_{s(m)}(I)` is D-balanced and MC-invariant with
  respect to `s(m)` (`isDBalanced_W_tuningParam`, `isMCInvariant_W_tuningParam`), the sheaf forms of
  the coordinate lemmas of the same names in `Hironaka.Local`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme BlowUpSequence Scheme.IdealSheafData

namespace Hironaka.Local

open IsLocalRing

/-- `s(1) = max 0 1 · lcm(∅) = 1`. -/
theorem tuningParam_one : tuningParam 1 = 1 := by decide

/-- `s(2) = max 1 1 · lcm(2) = 2`. -/
theorem tuningParam_two : tuningParam 2 = 2 := by decide

end Hironaka.Local

namespace AlgebraicGeometry.Scheme.IdealSheafData

open Hironaka.Local IsLocalRing

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- `W_{s(1)}(I) = I`: with the parameter `1`, `W_1(I) = MC(I) = D^0(I) = I` (`W_one`, `MC_eq`); the
form in which the closed-embedding clauses of [Kol07, Lemma 102 (3)] and [Kol07, Theorem 103 (3)]
meet the tuned ideal. -/
theorem W_tuningParam_one (I : X.IdealSheafData) : W f I 1 (tuningParam 1) = I := by
  rw [tuningParam_one, W_one f le_rfl I, MC_eq, Nat.sub_self, derivativeIter_zero]

variable [CharZero k] (n : ℕ) [SmoothOfRelativeDimension n f] (S : BlowUpSequence X)
  (I : X.IdealSheafData) (E : DivisorFamily X) (m : ℕ)

include n

/-- [Kol07, Corollary 101] at `s = s(m)` (`tuning_iff_E` at `r = max (m − 1) 1`): order reduction
for `(X, I, m, E)` is order reduction for `(X, W_{s(m)}(I), s(m), E)`. -/
theorem tuning_iff_tuningParam (hI : I.maxOrd = m) (hm : 1 ≤ m) :
    S.IsOrderGeSeq f I m E ↔
      S.IsOrderGeSeq f (W f I m (tuningParam m)) (tuningParam m) E :=
  Hironaka.Sequence.tuning_iff_E f n S I E m hI hm (le_max_left _ _) (le_max_right _ _)

/-- [Kol07, Corollary 101] at `s = s(m)` (`isDBalanced_W`): `W_{s(m)}(I)` is D-balanced with respect
to `s(m)`. -/
theorem isDBalanced_W_tuningParam (hI : I.maxOrd = m) (hm : 1 ≤ m) :
    IsDBalanced f (W f I m (tuningParam m)) (tuningParam m) :=
  isDBalanced_W f n I m hI hm (le_max_left _ _)

/-- [Kol07, Corollary 101] at `s = s(m)` (`isMCInvariant_W`): `W_{s(m)}(I)` is MC-invariant with
respect to `s(m)`. -/
theorem isMCInvariant_W_tuningParam (hI : I.maxOrd = m) (hm : 1 ≤ m) :
    IsMCInvariant f (W f I m (tuningParam m)) (tuningParam m) :=
  isMCInvariant_W f n I m hI hm (one_le_tuningParam m)

end AlgebraicGeometry.Scheme.IdealSheafData
