/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Stage.Theorem68
public import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.Triple
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The principalization functor `BP` on triples

Kollár's proof of the principalization theorem [Kol07, Theorem 35] runs as follows [Kol07, 72]:
make the components of `E` disjoint by the disjoining sequence `π : X' → X`
(`Hironaka/Resolution/Algebraic/Kol07/Thm35/Disjoin.lean`), so that `(X', π^* I, ∑ E^i)` "satisfies
the assumptions of (68)" (this is the triple `Hironaka.disjoinedTriple T`), then constructs
`Π_{(X,I,E)} : X_r → ⋯ → X_s = X' → ⋯ → X` "by composing `BMO_1(X', π^* I, 1, ∑ E^i)`" with the
disjoining sequence `X' → X`. Here `BMO_1` is the order reduction functor for marked ideals of
[Kol07, Theorem 69] at
mark `1` (`Hironaka.Stage.BMO_m 1 k`), evaluated at the marked triple `(X', π^* I, 1, ∑ E^i)`,
which lies in its domain `MarkedTriple.BMOClassFree 1` (`1 ≤ 1 ∧ m = 1`) by `⟨le_rfl, rfl⟩`, and
"composing" is the concatenation of blow-up sequences
(`AlgebraicGeometry.Scheme.BlowUpSequence.concat`).

**Empty blow-ups are deleted** (`BlowUpSequence.eraseEmpty`). The disjoining sequence always has
`card E.ι − 1` steps (`length_disjoinSeq`), and a step is empty whenever the components already
miss each other; Kollár: "ultimately the difference is only in some empty blow ups, and we can
forget about those at the end" [Kol07, 72], and the empty blow-up convention [Kol07, 32] says
that "the final outputs of the named blow-up sequence functors BD, BMO, BO, BP do not contain
empty blow-ups". The deletion is also what makes the functoriality clause for smooth morphisms
hold at the identity: it reads `S = S.eraseEmpty` there.

The functor is defined on the triples `(X, I, E)` of [Kol07, Notation 64]
(`AlgebraicGeometry.Triple`: `X` smooth and equidimensional over `k`, `I` nonzero on every
irreducible component, `E` a simple normal crossing divisor with ordered index set), the inputs of
Theorem 35, and the clauses (1)–(5) of Theorem 35 are proved in the modules
`Hironaka/Resolution/Algebraic/Kol07/Thm35/Principalization/*.lean`.

## Main declarations

* `Hironaka.Sequence.BP T : BlowUpSequence T.X.left`, the principalization sequence of a triple.
* `Hironaka.Sequence.disjoinSeq_of_isEmpty`: for `E = ∅` the disjoining sequence is empty.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory Scheme Hironaka BlowUpSequence Hironaka.Stage

namespace Hironaka.Sequence

variable {k : Type u} [Field k]

/-- The disjoining sequence of a family with an empty index type is the empty sequence ("we make
the `E_i` disjoint in `k − 1` steps" [Kol07, 72], with `k = 0`). -/
theorem disjoinSeq_of_isEmpty {X : Scheme.{u}} (E : DivisorFamily X) (hE : IsEmpty E.ι) :
    disjoinSeq E = nil X := by
  have := hE
  change disjoinSeqAux (Fintype.card E.ι) E.component = nil X
  rw [Fintype.card_eq_zero]
  rfl

/-- **The principalization sequence** `Π_{(X,I,E)} : X_r → ⋯ → X_s = X' → ⋯ → X_0 = X` of the
triple `T = (X, I, E)` [Kol07, 72]: the disjoining sequence `π : X' → X` of `E` followed by
`BMO_1(X', π^* I, 1, ∑ E^i)` (the order reduction functor for marked ideals of [Kol07, Theorem 69]
at mark `1`, on the disjoined triple `Hironaka.disjoinedTriple T`), with the empty
blow-ups deleted [Kol07, 32]. -/
noncomputable def BP [CharZero k] (T : Triple k) : BlowUpSequence T.X.left :=
  ((disjoinSeq T.E).concat
    ((BMO_m 1 k).seq ⟨disjoinedTriple T, 1⟩ ⟨le_rfl, rfl⟩)).eraseEmpty

end Hironaka.Sequence
