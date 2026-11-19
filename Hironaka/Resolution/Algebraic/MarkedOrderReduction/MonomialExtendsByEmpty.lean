/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.MonomialPart
public import Hironaka.Scheme.BlowUpSequence.PullbackEraseEmpty
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The monomial ideal of a family ignores unit members

[Kol07, Definition–Lemma 110] reads the monomial ideal `𝒪_X(−∑ c_i E^i)` on the irreducible
components of the members `E^i`; the convention [Kol07, 32] deletes empty blow-ups, whose
exceptional divisors survive here as unit members of the boundary. A unit member has empty
support, hence no irreducible components and the factor `1` in the product defining
`DivisorFamily.monomial`: the monomial ideal of a family extended by unit members
(`ExtendsByEmpty`) is the monomial ideal of the smaller family (`monomial_of_extendsByEmpty`),
through the general product identity `prod_component_of_extendsByEmpty`. The consequences for
the monomial and nonmonomial parts (`monomialPart_of_extendsByEmpty`,
`nonmonomialPart_of_extendsByEmpty`) are in
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/UpToUnits.lean`. This module imports both
`MonomialPart.lean` (the monomial ideal) and `Hironaka.Scheme.BlowUpSequence.PullbackEraseEmpty`
(`ExtendsByEmpty`), neither of which imports the other.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.DivisorFamily

variable {X : Scheme.{u}}

/-- A product over the members of a family extended by unit members, of a function equal to `1` on
the unit ideal, is the product over the members of the smaller family. -/
theorem prod_component_of_extendsByEmpty {α : Type*} [CommMonoid α] {E' E : DivisorFamily X}
    (hext : ExtendsByEmpty E' E) (G : X.IdealSheafData → α) (hG : G ⊤ = 1) :
    ∏ j, G (E.component j) = ∏ i, G (E'.component i) := by
  classical
  obtain ⟨ι, hinj, hcomp, htop⟩ := hext
  symm
  calc ∏ i, G (E'.component i) = ∏ i, G (E.component (ι i)) :=
        Finset.prod_congr rfl fun i _ => by rw [hcomp i]
    _ = ∏ j ∈ Finset.univ.image ι, G (E.component j) :=
        (Finset.prod_image (f := fun j => G (E.component j)) fun i _ i' _ h => hinj h).symm
    _ = ∏ j, G (E.component j) :=
        Finset.prod_subset (Finset.subset_univ _) fun j _ hj => by
          rw [htop j fun ⟨i, hi⟩ => hj (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩), hG]

/-- The monomial ideal of a family ignores unit members ([Kol07, Definition–Lemma 110] with the
convention [Kol07, 32]): the unit ideal has empty support, hence no irreducible components and the
factor `1`. -/
theorem monomial_of_extendsByEmpty {E' E : DivisorFamily X} (hext : ExtendsByEmpty E' E)
    (a : X → ℕ) : E.monomial a = E'.monomial a :=
  prod_component_of_extendsByEmpty hext
    (fun Z => ∏ᶠ η ∈ Z.support.genericPoints,
      Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {η}) ^ a η) (by
    change ∏ᶠ η ∈ (⊤ : X.IdealSheafData).support.genericPoints,
      Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {η}) ^ a η = 1
    rw [Scheme.IdealSheafData.support_top, Closeds.genericPoints_bot, finprod_mem_empty])

end AlgebraicGeometry.Scheme.DivisorFamily
