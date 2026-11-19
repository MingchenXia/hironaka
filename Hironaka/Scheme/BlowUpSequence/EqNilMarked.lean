/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
public import Hironaka.Scheme.IdealSheaf.Order.Constructible
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.IdealSheaf.Order.Specialization
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# A marked sequence of order `≥ m` for an ideal of maximal order `< m` is empty

The marked analogue of `eq_nil_of_isOrderSeq_of_maxOrd_lt`: a smooth blow-up sequence of order
`≥ m` starting with `(X, I, m, E)` [Kol07, Definition 66] and without empty blow-ups [Kol07, 32]
is the empty sequence when `max-ord I < m`. Its first center, being nonempty, contains a generic
point of one of its components (`Closeds.exists_mem_genericPoints_specializes`), where the order
of `I` is `≥ m` by condition (4′) of Definition 66, above the maximal order. The closed-embedding
clause of the order reduction functors uses this at `m = 1` for the unit ideal: when the ideal
`J` on the hypersurface is the unit ideal, both sides of the clause are the empty sequence. -/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme BlowUpSequence Scheme.IdealSheafData

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- A smooth blow-up sequence of order `≥ m` without empty blow-ups, for an ideal of maximal order
`< m`, is the empty sequence [Kol07, Definition 66 and 32]. -/
theorem eq_nil_of_isOrderGeSeq_of_maxOrd_lt (f : X ⟶ Spec (.of k)) {S : BlowUpSequence X}
    {I : X.IdealSheafData} {m : ℕ} {E : DivisorFamily X} (hS : S.IsOrderGeSeq f I m E)
    (hne : S.NoEmptyCenters) (hI : I.maxOrd < m) : S = nil X := by
  cases S with
  | nil => rfl
  | cons _ D rest =>
    exfalso
    rw [isOrderGeSeq_cons_iff] at hS
    rw [noEmptyCenters_cons_iff] at hne
    have hsup : (D.support : Set X) ≠ ∅ := fun h =>
      hne.1 ((IdealSheafData.support_eq_bot_iff D).mp (SetLike.coe_injective (by rw [h]; rfl)))
    obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hsup
    obtain ⟨η, hη, -⟩ := Closeds.exists_mem_genericPoints_specializes D.support hz
    have h1 : (m : ℕ∞) ≤ I.ord η := hS.1.2.2 η hη
    exact absurd (h1.trans (IdealSheafData.le_maxOrd I η)) (not_le.mpr hI)

end AlgebraicGeometry
