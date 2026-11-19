/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.BoundaryClearing.Data
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Indifference to empty boundary members for unmarked blow-up sequence functors

`Hironaka/Resolution/Algebraic/OrderReduction/EmptyIndifferent.lean` names the reindexing of [Kol07,
34.1] and the convention [Kol07, 32] as a property of a functor, indifference to empty boundary
members (deleting unit-ideal members of the boundary does not change the value), in two forms: for a
marked functor and for the boundary-clearing data of [Kol07, Lemma 102] at one mark over all
positions. This module adds the third form, for an unmarked functor of order `m` such as the
order-reduction functor `BO_{n,m}` of [Kol07, Theorem 103] (`Hironaka.BO.functor`): the same
relation between the two boundaries, the smaller family `E'` embedding order-preservingly into the
larger one `E` along `e : E'.ι ↪o E.ι`, members matched along `e`, the unit ideal at every index
outside the range of `e`, the ambient scheme and the ideal unchanged, and no distinguished
position, since an order-reduction functor has none. No invariance under permuting, combining or
splitting members is asserted.

* `OrderSeqAssignment.IndifferentToEmptyMembers B`, for a functor of order `m` on a class of
  triples.
* `BDFamily.NilAtUnitMember bdm`: the data of Lemma 102 at one mark are **nil at a unit member**
  when the round `BD_{n,m,j}(X, I, E)` is the empty sequence whenever the distinguished member
  `E^j` is the unit ideal. `BDFamily.IndifferentToEmptyMembers` relates the rounds at matched
  positions only, and the fields of `BDData` do not constrain the round at a unit member (the
  disjointness clause is vacuous there), so the indifference of Step 2.1 of Theorem 103, which
  runs one round per member, unit members included, needs this second property of the data. For
  the boundary-clearing data of `Hironaka/Resolution/Algebraic/BoundaryClearing/` it holds by
  construction: the blow-up of the unit ideal is erased and the inductive functor on the empty
  scheme is `nil`, which is Kollár's convention [Kol07, 32].
* `Triple.withBoundary T E' hsnc'`: the triple `T` with its boundary replaced by `E'`, given with
  its normal-crossings proof, `{ T with E := E', isSnc := hsnc' }`, the second triple of the
  indifference relation; reducible, so that every use unfolds to the structure literal in the
  definitions above.

The indifference of `BO_{n,m}` is proved in
`Hironaka/Resolution/Algebraic/OrderReduction/EmptyIndifferentStep2.lean` (the maximal-contact case)
and `EmptyIndifferentGlobal.lean` (the globalised functor); it is the input that the marked functor
of [Kol07, Theorem 107] needs
(`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Theorem107.lean`).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace Hironaka

open Scheme

/-- A blow-up sequence functor of order `m` on a class of triples is **indifferent to empty
boundary members** when deleting unit-ideal members from the boundary does not change its value:
for every triple `T`, every normal-crossings family `E'` on `T.X.left` embedding order-preservingly
into `T.E` along `e`, with the members matched along `e` and the unit ideal at every index outside
the range of `e`, the values at `T` and at `T` with boundary `E'` agree. Only deletion of empty
members is covered; no invariance under permuting or combining members is asserted. The unmarked
form of `OrderGeSeqAssignment.IndifferentToEmptyMembers`; not in the sources, it names the
reindexing of [Kol07, 34.1] and the convention [Kol07, 32]. -/
def OrderSeqAssignment.IndifferentToEmptyMembers {k : Type u} [Field k] {m : ℕ}
    {Dom : Triple k → Prop} (B : OrderSeqAssignment k m Dom) : Prop :=
  ∀ (T : Triple k) (E' : DivisorFamily T.X.left) (hsnc' : E'.IsSnc) (e : E'.ι ↪o T.E.ι),
    (∀ i, T.E.component (e i) = E'.component i) →
    (∀ b, b ∉ Set.range e → T.E.component b = ⊤) →
    ∀ (hT : Dom T) (hT' : Dom { T with E := E', isSnc := hsnc' }),
      B.seq T hT = B.seq { T with E := E', isSnc := hsnc' } hT'

/-- The data of [Kol07, Lemma 102] at one mark, `bdm : ∀ j, BDData n m j`, are **nil at a unit
member** when, for every field `k` of characteristic zero, position `j` and triple `T` of the class
whose distinguished member `E^j` is the unit ideal, the value of `bdm j` at `T` is the empty
sequence. The round of a unit member is what Kollár's convention [Kol07, 32] ignores "without
explicit mention"; the fields of `BDData` do not force it (the disjointness clause is vacuous when
`E^j = ⊤`), so it is a second property of the data beside `BDFamily.IndifferentToEmptyMembers`,
which relates matched positions only. Not in the sources. -/
def BDFamily.NilAtUnitMember {n m : ℕ} (bdm : ∀ j : ℕ, BDData.{u} n m j) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (j : ℕ) (T : Triple k) (hT : Triple.BDClass n m j T),
    T.E.nth ⟨j, hT.2.2⟩ = ⊤ → ((bdm j).functor k).seq T hT = BlowUpSequence.nil T.X.left

end Hironaka

namespace AlgebraicGeometry.Triple

open Hironaka

open Scheme

/-- The triple `T` with its boundary replaced by `E'`, given with its normal-crossings proof:
`{ T with E := E', isSnc := hsnc' }`, the second triple of the indifference relation
(`IndifferentToEmptyMembers`). Reducible, so that every use unfolds to the structure literal in
the definitions of the relation. -/
abbrev withBoundary {k : Type u} [Field k] (T : Triple k) (E' : DivisorFamily T.X.left)
    (hsnc' : E'.IsSnc) : Triple k :=
  { T with E := E', isSnc := hsnc' }

end AlgebraicGeometry.Triple

namespace Hironaka

open Scheme

end Hironaka
