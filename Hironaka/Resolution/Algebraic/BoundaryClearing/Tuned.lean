/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.TuningParam
public import Hironaka.Resolution.Algebraic.Tuning.Sheaf
public import Hironaka.Scheme.IdealSheaf.Order.Constructible
import Hironaka.Resolution.Algebraic.Kol07.Tuning
import Hironaka.Resolution.Algebraic.Tuning.Corollary101
import Hironaka.Resolution.Algebraic.Tuning.Parameter
import Hironaka.Resolution.Algebraic.Tuning.Sequence
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.Remark67
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The reduction to a D-balanced ideal

The proof of [Kol07, Lemma 102] opens by replacing `I` with the tuned ideal `W_{m!}(I)`, which is
D-balanced, order reduction for `(X, I, E)` being equivalent to order reduction for
`(X, W_{m!}(I), E)` by [Kol07, Corollary 101]. This library's tuning parameter is
`s(m) = tuningParam m` (`Hironaka/Algebra/Local/TuningParam.lean`), and Corollary 101 at that
parameter is `tuning_iff_tuningParam` (`Hironaka/Resolution/Algebraic/Tuning/Parameter.lean`), a
statement about the MARKED sequences of [Kol07, Definition 66]: "of order `≥ m` for `(X, I, m, E)`"
iff "of order `≥ s(m)` for `(X, W_{s(m)}(I), s(m), E)`". Lemma 102's functor is of order `m`
(unmarked), and `max-ord I = m`: [Kol07, Remark 67] (`isOrderGeSeq_iff_isOrderSeq`,
`Hironaka/Scheme/BlowUpSequence/Remark67.lean`) identifies the marked and the unmarked sequences on
the left, and again on the right since `max-ord W_{s(m)}(I) = s(m)` (`maxOrd_W`,
`Hironaka/Resolution/Algebraic/Tuning/Corollary101.lean`). That is `isOrderSeq_iff_tuned`.

"Order reduction … is equivalent": along such a sequence the cosupports agree stage by stage,
`cosupp(I_i, m) = cosupp(W_i, s(m))` (`le_ord_weakTransformSeq_iff_tuned`), by the two inclusions
of the proof of [Kol07, Theorem 100]: `W_i ⊆ W_{s}(I_i)` (`markedTransformSeq_W_le`) together with
`ord_x I_i ≥ m ⟹ ord_x W_s(I_i) ≥ s` (`le_ord_W_of_le_ord`, both in
`Hironaka/Resolution/Algebraic/Tuning/Sequence.lean`) give `⟹`; `I_i^{s'} ⊆ W_i` for `s = m s'`
(`pow_markedTransformSeq_le`, from `I^{s'} ⊆ W_{m s'}(I)`) with `ord_x (I_i^{s'}) = s' · ord_x I_i`
(`ord_pow`, both in `Hironaka/Resolution/Algebraic/Kol07/Tuning.lean`) gives `⟸`. Remark 67 makes
the marked transforms the weak ones on both sides. This transfers clause (1) of Lemma 102 from the
tuned ideal to `I` (`Assembly.lean`, `AssemblyTuned.lean`).

Used also by `OrderSeqAssignment.ofTunedClass`,
`Hironaka/Resolution/Algebraic/OrderReduction/Tuned.lean`,
`Hironaka/Resolution/Algebraic/OrderReduction/Step22Assembly.lean` and
`Hironaka/Resolution/Algebraic/OrderReduction/Step22Cosupp.lean`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme BlowUpSequence Scheme.IdealSheafData
  IsLocalRing Hironaka.Sequence

namespace Hironaka.BD

variable {X : Scheme.{u}} {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) [CharZero k] (n : ℕ)
  [SmoothOfRelativeDimension n f] (S : BlowUpSequence X) (I : X.IdealSheafData)
  (E : DivisorFamily X) (m : ℕ)

include n

/-- For `max-ord I = m ≥ 1`, a smooth blow-up sequence is of order `m` starting with `(X, I, E)`
iff it is of order `s(m)` starting with `(X, W_{s(m)}(I), E)` (the first paragraph of the proof of
[Kol07, Lemma 102]; [Kol07, Corollary 101] at `s(m)`, i.e. `tuning_iff_tuningParam`, with
[Kol07, Remark 67] on both sides). -/
theorem isOrderSeq_iff_tuned (hI : I.maxOrd = m) (hm : 1 ≤ m) :
    S.IsOrderSeq f I E m ↔ S.IsOrderSeq f (IdealSheafData.W f I m (tuningParam m)) E
        (tuningParam m) :=
  (isOrderGeSeq_iff_isOrderSeq f n hI).symm.trans
    ((IdealSheafData.tuning_iff_tuningParam f n S I E m hI hm).trans
      (isOrderGeSeq_iff_isOrderSeq f n (IdealSheafData.maxOrd_W f n I m hI hm _)))

/-- Along a smooth blow-up sequence of order `m` starting with `(X, I, E)`, `max-ord I = m ≥ 1`, at
every stage and point `ord_x I_i ≥ m ⟺ ord_x W_i ≥ s(m)`: the inclusions
`I_i^{s'} ⊆ W_i ⊆ W_s(I_i)` of the proof of [Kol07, Theorem 100]. -/
theorem le_ord_weakTransformSeq_iff_tuned (hI : I.maxOrd = m) (hm : 1 ≤ m)
    (h : S.IsOrderSeq f I E m) (i : Fin (S.length + 1)) (x : S.stage i) :
    (m : ℕ∞) ≤ (S.weakTransformSeq I i).ord x ↔
      (tuningParam m : ℕ∞) ≤ (S.weakTransformSeq (IdealSheafData.W f I m
          (tuningParam m)) i).ord x := by
  have hge : S.IsOrderGeSeq f I m E := (isOrderGeSeq_iff_isOrderSeq f n hI).mpr h
  have hW : S.IsOrderSeq f (IdealSheafData.W f I m (tuningParam m)) E (tuningParam m) :=
    (isOrderSeq_iff_tuned f n S I E m hI hm).mp h
  rw [← IsOrderSeq.markedTransformSeq_eq_weakTransformSeq f n h i,
    ← IsOrderSeq.markedTransformSeq_eq_weakTransformSeq f n hW i]
  have := IsSmooth.smoothOfRelativeDimension_stageMap (n := n) h.1 i
  constructor
  · intro hx
    have h1 := markedTransformSeq_W_le f n S I E m (tuningParam m) hge i
    have h2 := le_ord_W_of_le_ord (S.stageMap i ≫ f) n (S.markedTransformSeq I m i) m
      (tuningParam m) x hx
    exact h2.trans (Scheme.IdealSheafData.ord_anti h1 x)
  · intro hx
    obtain ⟨s', hs'⟩ : m ∣ tuningParam m := (dvd_Lcm hm le_rfl).mul_left _
    have hs'1 : 1 ≤ s' := by
      rcases Nat.eq_zero_or_pos s' with h0 | h0
      · have := one_le_tuningParam m
        rw [hs', h0, mul_zero] at this
        omega
      · exact h0
    have hpow : S.markedTransformSeq I m i ^ s' ≤
        S.markedTransformSeq (IdealSheafData.W f I m (tuningParam m)) (m * s') i :=
      pow_markedTransformSeq_le I (IdealSheafData.W f I m (tuningParam m)) m s' S
          (IdealSheafData.pow_le_W f hs'.le) i
    rw [← hs'] at hpow
    have h3 : (tuningParam m : ℕ∞) ≤ (S.markedTransformSeq I m i ^ s').ord x :=
      hx.trans (Scheme.IdealSheafData.ord_anti hpow x)
    rw [ord_pow (S.stageMap i ≫ f) n _ s' hs'1 x, hs', Nat.cast_mul, mul_comm] at h3
    exact (ENat.mul_le_mul_left_iff (Nat.cast_ne_zero.mpr (by omega))
      (ENat.natCast_ne_top s')).mp h3

end Hironaka.BD
