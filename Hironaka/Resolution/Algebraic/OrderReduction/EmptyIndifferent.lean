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
# Indifference of blow-up sequence functors to empty boundary members

Kollár's convention [Kol07, 32] ignores empty blow-ups "without explicit mention", and the second
clause of [Kol07, 34.1] states functoriality for an arbitrary smooth morphism `h` "by deleting
every blow-up `h^*π_i` whose center is empty and reindexing the resulting blow-up sequence". In
this development the boundary of a triple is a family of divisors with an ordered index set
(`AlgebraicGeometry.Scheme.DivisorFamily`), the total transform appends one member per blow-up, and
the member appended by a trivial blow-up is the unit ideal: after the empty blow-ups are deleted
(`eraseEmpty`), the induced boundary of a pulled-back sequence has fewer members than the pull-back
of the induced boundary, whereas the relations `IsPullbackOf` and `IsBaseChangeOf` between triples
demand equal boundaries. Kollár's "reindexing" is therefore a property of a functor that has to be
named: **a functor is indifferent to empty boundary members** when its value does not change
under deleting unit-ideal members from the boundary. The smaller family `E'` embeds
order-preservingly into the larger one `E` (`e : E'.ι ↪o E.ι`), the members are matched along `e`,
every index outside the range of `e` carries the unit ideal, and the ambient scheme and the ideal
are unchanged. No invariance under permuting, combining or splitting members is asserted: the
boundary-clearing Step 2.1 of [Kol07, Theorem 103] runs position by position, so its functor is
not indifferent to replacing `(D₁, D₂, D₃)` by `(D₁, D₂ ⊔ D₃)`, which a pointwise "same members
through every point" relation would allow.

* `DivisorFamily.nthIdx` is the index of the `j`-th member (`nth` is the member itself).
* `OrderGeSeqAssignment.IndifferentToEmptyMembers B` is the property for a marked functor, such as
  the order-reduction functor for marked ideals of [Kol07, Theorem 69] in dimensions `< n`, the
  inductive input of the boundary-clearing functor.
* `BDFamily.IndifferentToEmptyMembers bdm` is the property for the data of [Kol07, Lemma 102] at
  one mark over all positions `j` (`bdm : ∀ j, BDData n m j`): the distinguished member `E^j` is
  carried along `e` (`e (E'.nthIdx j') = E.nthIdx j`), since deleted members before it move its
  position.

The unmarked form, for a functor of order `m`, is in
`Hironaka/Resolution/Algebraic/OrderReduction/EmptyIndifferentFunctor.lean`. These properties are
hypotheses of the functoriality statements for an arbitrary smooth morphism
(`Hironaka/Resolution/Algebraic/OrderReduction/Step2EraseEmpty.lean`) and are proved for the
boundary-clearing data in `Hironaka/Resolution/Algebraic/BoundaryClearing/Indifference.lean`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

open Hironaka

variable {X : Scheme.{u}}

/-- The index of the `j`-th member of a divisor family with ordered index set ([Kol07,
Definition 31]: "`E` a divisor on `X` with ordered index set"), positions counted from `0`;
`E.nth j = E.component (E.nthIdx j)`. -/
noncomputable def DivisorFamily.nthIdx (E : DivisorFamily X) (j : Fin (Fintype.card E.ι)) : E.ι :=
  monoEquivOfFin E.ι rfl j

theorem DivisorFamily.nth_eq_component_nthIdx (E : DivisorFamily X) (j : Fin (Fintype.card E.ι)) :
    E.nth j = E.component (E.nthIdx j) := rfl

/-- A marked blow-up sequence functor is **indifferent to empty boundary members** when deleting
unit-ideal members from the boundary does not change its value: for every marked triple `T`, every
normal-crossings family `E'` on `T.X.left` embedding order-preservingly into `T.E` along `e`, with
the members matched along `e` and the unit ideal at every index outside the range of `e`, the values
at `T` and at `T` with boundary `E'` agree. Only deletion of empty members is covered; no
invariance under permuting or combining members is asserted. Not in the sources: it names the
reindexing of [Kol07, 34.1] and the convention [Kol07, 32] as a property of the functor. -/
def _root_.Hironaka.OrderGeSeqAssignment.IndifferentToEmptyMembers {k : Type u} [Field k]
    {Dom : MarkedTriple k → Prop}
    (B : OrderGeSeqAssignment k Dom) : Prop :=
  ∀ (T : MarkedTriple k) (E' : DivisorFamily T.X.left) (hsnc' : E'.IsSnc) (e : E'.ι ↪o T.E.ι),
    (∀ i, T.E.component (e i) = E'.component i) → (∀ b, b ∉ Set.range e → T.E.component b = ⊤) →
    ∀ (hT : Dom T) (hT' : Dom { T with E := E', isSnc := hsnc' }),
      B.seq T hT = B.seq { T with E := E', isSnc := hsnc' } hT'

/-- The data of [Kol07, Lemma 102] at one mark, `bdm : ∀ j, BDData n m j`, are **indifferent to
empty boundary members** when deleting unit-ideal members from the boundary does not change their
value, the distinguished position being carried along: for every triple `T`, every
normal-crossings family `E'` on `T.X.left` embedding order-preservingly into `T.E` along `e`, with
the members matched along `e` and the unit ideal at every index outside the range of `e`, and
positions `j` of `T.E` and `j'` of `E'` with `e (E'.nthIdx j') = T.E.nthIdx j`, the values of
`bdm j` at `T` and of `bdm j'` at `T` with boundary `E'` agree. Only deletion of empty members is
covered; no invariance under permuting or combining members is asserted. Not in the sources: it
names the reindexing of [Kol07, 34.1] for the boundary-clearing functor. -/
def _root_.Hironaka.BDFamily.IndifferentToEmptyMembers {n m : ℕ} (bdm : ∀ j : ℕ,
    BDData.{u} n m j) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (T : Triple k) (E' : DivisorFamily T.X.left)
    (hsnc' : E'.IsSnc) (e : E'.ι ↪o T.E.ι),
    (∀ i, T.E.component (e i) = E'.component i) → (∀ b, b ∉ Set.range e → T.E.component b = ⊤) →
    ∀ (j j' : ℕ) (hj : j < Fintype.card T.E.ι) (hj' : j' < Fintype.card E'.ι),
      e (E'.nthIdx ⟨j', hj'⟩) = T.E.nthIdx ⟨j, hj⟩ →
      ∀ (hT : Triple.BDClass n m j T)
        (hT' : Triple.BDClass n m j' { T with E := E', isSnc := hsnc' }),
        ((bdm j).functor k).seq T hT =
          ((bdm j').functor k).seq { T with E := E', isSnc := hsnc' } hT'

end AlgebraicGeometry.Scheme
