/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Defs
public import Hironaka.Scheme.Snc.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Hironaka.Scheme.Snc.EmptyFamily
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
public import Hironaka.Resolution.Algebraic.Kol07.EraseEmptyEmbedding
public import Hironaka.Resolution.Algebraic.Snc.SncOnTransport
import Mathlib.AlgebraicGeometry.Scheme

/-!
# The empty boundary family on a smooth scheme

A small module in the closed-embedding chapter of the tower (Claim 71.2, [Kol07, 108]): it collects,
through its imports, the descent of the identity along a smooth surjection
(`Hironaka.Sequence.seq_eq_pushforward_of_cover`, the first bullet of [Kol07, 34.1] with the
injectivity of pull-back along a flat surjection) and the transport
`Hironaka.Sequence.isNonzeroEverywhere_map_of_isClosedImmersion` (the push-forward along a closed
immersion of an ideal sheaf with nonzero stalks has nonzero stalks, which makes the intermediate
triple `(Y_i, (Y ↪ Y_i)_* J, 1, ∅)` of Kollár's chain a triple in the sense of
[Kol07, Notation 64]), and it holds one corollary: `isSnc_of_isEmpty`, a boundary family with no
member is a simple normal crossing divisor on a smooth `k`-scheme.
-/

public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Scheme BlowUpSequence
  Scheme.IdealSheafData Hironaka.Sequence Hironaka.Snc

namespace Hironaka.Stage

section Descent

variable {k : Type u} [Field k]

end Descent

section Transports

variable {X Y : Scheme.{u}}

variable {k : Type u} [Field k]

/-- On a smooth `k`-scheme a boundary family without members is a simple normal crossing divisor
[Kol07, Definition 24]: the instance-argument form of `AlgebraicGeometry.isSnc_of_isEmpty`. -/
theorem isSnc_of_isEmpty (f : X ⟶ Spec (.of k)) [Smooth f] (E : DivisorFamily X)
    [IsEmpty E.ι] : E.IsSnc :=
  AlgebraicGeometry.isSnc_of_isEmpty f E inferInstance

end Transports

end Hironaka.Stage
