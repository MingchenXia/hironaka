/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Snc.Dictionary
public import Hironaka.Resolution.Algebraic.BoundaryClearing.Data
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
/-!
# The componentwise blow-up sequence of a center: definitions

Kollár's smooth centers may be disconnected; clause (i) of Hironaka's Main Theorem II
[Hir64, Main Theorem II] asks for irreducible ones. The two are reconciled by blowing up a disjoint
union of smooth centers component by component, in a fixed order: the resulting sequence has the
same composite (the "silly counterexamples" of [Kol07, Remark 33]: blowing up disjoint `Z_1`, `Z_2`
one after the other or at once gives the same result). This module holds the definitions the
lemma is about.

* `AlgebraicGeometry.Scheme.BlowUpSequence.ofCenters c D`: for a list `D : Fin c → X.IdealSheafData`
  of centers on `X`, the sequence that blows up `D 0`, then the inverse image of `D 1` in the
  blow-up, then the inverse image of `D 2` in the second blow-up, and so on:
  `π_{Z_1} ∘ π_{Z_2'} ∘ ⋯ ∘ π_{Z_c'}` with `Z_k'` the preimage of `Z_k` in the intermediate scheme
  (for pairwise disjoint `Z_k` the
  preimage is isomorphic to `Z_k`, which is part of the lemma; the definition takes the inverse
  image for any list).
* `AlgebraicGeometry.Scheme.DivisorFamily.nth F`: the members of a divisor family listed in
  the order of its index set, as a `Fin (Fintype.card F.ι)`-indexed family (Mathlib's
  `monoEquivOfFin`).
* `AlgebraicGeometry.Scheme.IdealSheafData.componentwiseSeq Z`: the componentwise sequence of the
  closed subscheme `V(Z)`, `ofCenters` applied to the irreducible components of `V(Z)`
  (`componentFamily`: indexed by the generic points of `V(Z)`, each with its reduced structure,
  ordered by a well-ordering of the generic points).

The lemmas (`Hironaka/Resolution/Algebraic/Kol07/ComponentwiseBlowUp.lean`,
`ComponentwiseTransport.lean`, `ComponentwiseTransforms.lean`) say: for pairwise disjoint centers
the composite of `ofCenters c D` is a blow-up of `X` along `∏ i, D i` (the universal property of the
blow-up, [Hau14, Definition 4.4], iterated), canonically isomorphic to `(∏ i, D i).blowUp` over
`X`; a regular closed subscheme is the product of its (pairwise disjoint) irreducible components;
and the conditions of [Kol07, Definition 66] transport from the center to the componentwise
sequence.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme BlowUpSequence

namespace AlgebraicGeometry.Scheme.BlowUpSequence


variable {X : Scheme.{u}}

/-- The sequence blowing up the listed centers `D 0, D 1, …, D (c-1)` one after another, each
center `D k` replaced by its inverse image `Z_k'` under the composite of the earlier blow-ups:
`π_{Z_1} ∘ π_{Z_2'} ∘ ⋯ ∘ π_{Z_c'}`. -/
noncomputable def ofCenters :
    {X : Scheme.{u}} → (c : ℕ) → (Fin c → X.IdealSheafData) → BlowUpSequence X
  | X, 0, _ => nil X
  | X, c + 1, D => cons X (D 0) (ofCenters c fun i => (D i.succ).comap (D 0).blowUpπ)

@[simp]
theorem ofCenters_zero (D : Fin 0 → X.IdealSheafData) : ofCenters 0 D = nil X := rfl

@[simp]
theorem ofCenters_succ (c : ℕ) (D : Fin (c + 1) → X.IdealSheafData) :
    ofCenters (c + 1) D =
      cons X (D 0) (ofCenters c fun i => (D i.succ).comap (D 0).blowUpπ) := rfl

/-- The componentwise sequence of `c` centers has length `c`. -/
theorem length_ofCenters (c : ℕ) (D : Fin c → X.IdealSheafData) : (ofCenters c D).length = c := by
  induction c generalizing X with
  | zero => rfl
  | succ c ih => exact congrArg (· + 1) (ih _)

end AlgebraicGeometry.Scheme.BlowUpSequence

namespace AlgebraicGeometry.Scheme.DivisorFamily

variable {X : Scheme.{u}}

/-- Listing the members in order does not change their product. -/
theorem prod_orderedComponent (F : DivisorFamily X) :
    ∏ k, F.nth k = ∏ i, F.component i :=
  Fintype.prod_equiv (monoEquivOfFin F.ι rfl).toEquiv _ _ fun _ => rfl

end AlgebraicGeometry.Scheme.DivisorFamily

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- **The componentwise blow-up sequence** of the closed subscheme `V(Z)`: the irreducible
components of `V(Z)` (`componentFamily`, indexed by the generic points of `V(Z)` with their reduced
structures) blown up one after another in the order of the chosen well-ordering of the generic
points, each replaced by its inverse image under the earlier blow-ups. Needs finitely many
components (`Finite Z.support.genericPoints`, available as an instance when `X` is Noetherian). -/
noncomputable def componentwiseSeq (Z : X.IdealSheafData) [Finite Z.support.genericPoints] :
    BlowUpSequence X :=
  ofCenters _ Z.componentFamily.nth

/-- The componentwise sequence has one blow-up per irreducible component of `V(Z)`. -/
theorem length_componentwiseSeq (Z : X.IdealSheafData) [Finite Z.support.genericPoints] :
    Z.componentwiseSeq.length = Nat.card Z.support.genericPoints := by
  unfold componentwiseSeq
  rw [length_ofCenters]
  exact (@Nat.card_eq_fintype_card Z.componentFamily.ι Z.componentFamily.fintype).symm

end AlgebraicGeometry.Scheme.IdealSheafData
