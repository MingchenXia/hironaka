/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.OrderReduction.Basic
public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Basic
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Monotonicity of the dimension-bounded classes

Kollár's "`dim X = n`" in [Kol07, Lemma 102, Theorem 103 and Theorem 107] is read throughout the
library as "`dim X ≤ n`" (`Triple.HasDimLE`), so that disjoint unions and the restriction to a
component of the boundary stay in the class; the classes of the stage-`n` functors —
`Triple.BOClass n m` and `MarkedTriple.BMOClass n m` — therefore grow with the dimension bound: a
triple of dimension `≤ n'` has dimension `≤ n` for `n' ≤ n`. These three one-line inclusions place a
triple of the smaller class in the larger one; the coherence statements of
`Hironaka.Resolution.Algebraic.Stage.Coherence` and the restriction of the stage-`n` functor to the
stage-`n'` class (`OrderSeqAssignment.restrict`) use them.
-/

public section

universe u

open AlgebraicGeometry

namespace Hironaka

variable {k : Type u} [Field k]

/-- A triple of dimension `≤ n'` has dimension `≤ n` for `n' ≤ n`. -/
theorem _root_.AlgebraicGeometry.Triple.hasDimLE_mono {n n' : ℕ} (h : n' ≤ n) {T : Triple k}
    (hT : T.HasDimLE n') : T.HasDimLE n := by
  obtain ⟨d, hd, hdim⟩ := hT
  exact ⟨d, le_trans hd h, hdim⟩

/-- The class `BOClass n' m` of [Kol07, Theorem 103] lies in `BOClass n m` for `n' ≤ n`. -/
theorem _root_.AlgebraicGeometry.Triple.boClass_mono {n n' m : ℕ} (h : n' ≤ n) {T : Triple k}
    (hT : T.BOClass n' m) : T.BOClass n m :=
  ⟨hT.1, Triple.hasDimLE_mono h hT.2.1, hT.2.2⟩

/-- The class `BMOClass n' m` of [Kol07, Theorem 107] lies in `BMOClass n m` for `n' ≤ n`. -/
theorem MarkedTriple.bmoClass_mono {n n' m : ℕ} (h : n' ≤ n) {T : MarkedTriple k}
    (hT : T.BMOClass n' m) : T.BMOClass n m :=
  ⟨hT.1, Triple.hasDimLE_mono h hT.2.1, hT.2.2⟩

end Hironaka
