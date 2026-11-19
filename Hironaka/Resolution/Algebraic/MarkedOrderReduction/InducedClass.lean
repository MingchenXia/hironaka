/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Basic
public import Hironaka.Resolution.Algebraic.OrderReduction.Basic
public import Hironaka.Scheme.BlowUpSequence.Triple
import Hironaka.Scheme.Snc.DictionaryOrder
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The class of marked triples along a smooth blow-up sequence

The functor `BMO_{n,m}` of [Kol07, Theorem 107] is assembled by concatenating Step 1, Step 2 and the
geometric Step 3 of its proof, each run on the marked triple induced at the end of the previous step
([Kol07, 111]: after Step 1, "instead of `(X^1, (Π_1)^{-1}_*(I, m), (Π_1)^{-1}_{tot}(E))`, write
`(X, I, m, E)`"). Each step is defined on the class `BMOClass n m` (`1 ≤ m`, `dim X ≤ n`, the mark
`m`), so the induced marked triple must lie in the class again: the mark is unchanged, and every
stage of a smooth blow-up sequence over a scheme smooth of relative dimension `n'` over `k` is
smooth of the same relative dimension (`IsSmooth.stageMap_smoothOfRelativeDimension`; a smooth
blow-up of a smooth scheme is smooth, [Kol07, Notation 19]). Steps 1 and 2 prove this per round
(`bmoClass_roundTriple`, `bmoClass_step2Triple`); this module states it once, for any smooth blow-up
sequence of order `≥ m` and any stage `i`.

* `MarkedTriple.bmoClass_induced`: the marked triple induced at any stage of a smooth blow-up
  sequence of order `≥ m` for a marked triple of `BMOClass n m` is again of `BMOClass n m`.
* `BMO.bmoClass_of_boClass`: a triple of `BOClass n m` marked at `m` is a marked triple of
  `BMOClass n m` (the marked triple `(X, I, m, ∅)` of clause (3) of Theorem 107).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Hironaka Scheme.BlowUpSequence

namespace Hironaka.MarkedTriple

variable {k : Type u} [Field k] [CharZero k] {n m : ℕ}

/-- **The marked triple induced at any stage of a smooth blow-up sequence of order `≥ m` for a
marked triple of `BMOClass n m` is again of `BMOClass n m`** ([Kol07, 111]: the induced marked
triple is again written `(X, I, m, E)`): the mark is unchanged, `1 ≤ m` is carried, and the stage
map of a smooth blow-up sequence over a scheme smooth of relative dimension `n' ≤ n` is smooth of
relative dimension `n'` (`IsSmooth.stageMap_smoothOfRelativeDimension`). The general form of
`bmoClass_roundTriple` and `bmoClass_step2Triple`, which are its instances at the last stage of one
round. -/
theorem bmoClass_induced (T : MarkedTriple k) (hT : T.BMOClass n m)
    {S : Scheme.BlowUpSequence T.X.left}
    (hS : S.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E) (i : Fin (S.length + 1)) :
    (T.induced S hS i).BMOClass n m := by
  obtain ⟨n', hn'n, hn'⟩ := hT.2.1
  have : SmoothOfRelativeDimension n' (T.X.left ↘ Spec (.of k)) := hn'
  exact ⟨hT.1, ⟨n', hn'n, IsSmooth.stageMap_smoothOfRelativeDimension hS.1 i⟩,
    hT.2.2⟩

end Hironaka.MarkedTriple

namespace Hironaka.BMO

variable {k : Type u} [Field k] {n m : ℕ}

/-- A triple of `BOClass n m` marked at `m` is a marked triple of `BMOClass n m`: `1 ≤ m` and the
dimension bound are the class's, the mark is `m`. This is the marked triple `(X, I, m, ∅)` of clause
(3) of [Kol07, Theorem 107]. -/
theorem bmoClass_of_boClass (T : Triple k) (hT : T.BOClass n m) :
    MarkedTriple.BMOClass n m ⟨T, m⟩ :=
  ⟨hT.1, hT.2.1, rfl⟩

end Hironaka.BMO
