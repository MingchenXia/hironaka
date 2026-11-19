/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Monomial.Geometric.Pieces
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Renumbering of a piece family

The geometric Step 3 `PieceFamily.realize` depends on a piece family only through its pieces (as
closed sets), their exponents and the order of their labels. This module defines the relation
under which the run is shown invariant in
`Hironaka/Resolution/Algebraic/Monomial/Geometric/RealizeCongr.lean`: the relation
`MonomialState.Rel ρ σ D P` of `Hironaka/Resolution/Algebraic/Monomial/Restrict/Rename.lean` lifted
to piece families. *`Φ.Rel ρ σ Φ'` says that `Φ'` is `Φ` renumbered*: the live components of `Φ` are
re-embedded by the strictly monotone `ρ` (so that the order of the component indices, which numbers
the new components of a blow-up through `rank`, is kept), the labels by the strictly monotone `σ`
(Kollár's choice reads label tuples lexicographically, which an order embedding of labels
preserves), with the same pieces and exponents, and the nerve of `Φ'` the image of the nerve of `Φ`;
`Φ'` may carry further dead components (empty pieces) and unused labels.

The two uses: the deletion of empty members of a boundary (an empty member has no components, so
the surviving components keep their relative order and the labels re-embed;
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/SmoothStep3.lean`), and the independence of the
run from the enumeration of the components whenever the two enumerations are order-compatible. A
congruence tolerating arbitrary permutations of the components is not proved; nothing needs it. Not
in the sources: Kollár's `E^j` are indexed by a fixed ordered set and the question does not arise.
-/

@[expose] public section

universe u

open AlgebraicGeometry TopologicalSpace

namespace Hironaka.Monomial.PieceFamily

variable {X : Scheme.{u}}

/-- *`Φ'` is `Φ` renumbered by `ρ` on components and `σ` on labels*: both strictly monotone on the
live ranges and landing below `Φ'`'s counters, the same pieces and exponents, the labels through
`σ`, and the nerve of `Φ'` the image of the nerve of `Φ` (so every further component of `Φ'` is
dead). The relation `MonomialState.Rel` on piece families. -/
structure Rel (Φ : PieceFamily X) (ρ σ : ℕ → ℕ) (Φ' : PieceFamily X) : Prop where
  /-- `ρ` is strictly monotone on the live components of `Φ`. -/
  mono : StrictMonoOn ρ (Set.Iio Φ.nextComp)
  /-- `ρ` lands below `Φ'`'s component counter. -/
  lt : ∀ c, c < Φ.nextComp → ρ c < Φ'.nextComp
  /-- The pieces are the same closed sets. -/
  piece_eq : ∀ c, c < Φ.nextComp → Φ'.piece (ρ c) = Φ.piece c
  /-- The exponents are the same. -/
  a_eq : ∀ c, c < Φ.nextComp → Φ'.a (ρ c) = Φ.a c
  /-- The labels are renamed by `σ`. -/
  label_eq : ∀ c, c < Φ.nextComp → Φ'.label (ρ c) = σ (Φ.label c)
  /-- `σ` is strictly monotone on the labels of `Φ`. -/
  σmono : StrictMonoOn σ (Set.Iio Φ.nextLabel)
  /-- `σ` lands below `Φ'`'s label counter. -/
  σlt : ∀ ℓ, ℓ < Φ.nextLabel → σ ℓ < Φ'.nextLabel
  /-- The nerve of `Φ'` is the image of the nerve of `Φ`. -/
  nerve_eq : Φ'.nerve = Φ.nerve.image (Finset.image ρ)

/-- The identity renumbering. -/
theorem Rel.refl (Φ : PieceFamily X) : Φ.Rel id id Φ where
  mono _ _ _ _ h := h
  lt _ hc := hc
  piece_eq _ _ := rfl
  a_eq _ _ := rfl
  label_eq _ _ := rfl
  σmono _ _ _ _ h := h
  σlt _ hℓ := hℓ
  nerve_eq := by
    have h : Φ.nerve.image (Finset.image (id : ℕ → ℕ)) = Φ.nerve.image id :=
      Finset.image_congr fun _ _ => Finset.image_id
    rw [h, Finset.image_id]

end Hironaka.Monomial.PieceFamily
