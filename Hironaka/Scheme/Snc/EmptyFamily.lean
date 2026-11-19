/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Snc.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Scheme.Snc.Family
/-!
# The empty boundary is a simple normal crossing divisor

[Kol07, Notation 64 (3)] asks the boundary `E = (E^1, …, E^s)` of a triple to be a simple normal
crossing divisor; for `s = 0` (the triple `(𝔸⁴, I, ∅)` of [Kol07, Example 106], for instance) the
two clauses of [Kol07, Definition 24] are vacuous except for the regular system of parameters at
each point, which a smooth `k`-scheme has (`exists_fin_span_eq_maximalIdeal_stalk`). Both the family
`DivisorFamily.empty X` and any family with an empty index type are covered.
-/

public section

universe u

open AlgebraicGeometry CategoryTheory Scheme

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- On a smooth `k`-scheme the empty boundary `DivisorFamily.empty X` is a simple normal crossing
divisor [Kol07, Definition 24]: no component to be regular, and at each point the regular system of
parameters of the stalk with the empty assignment. -/
theorem isSnc_empty_of_smooth (f : X ⟶ Spec (.of k)) [Smooth f] :
    (DivisorFamily.empty X).IsSnc :=
  ⟨fun i => i.elim, fun x =>
    have := isRegularLocalRing_stalk f x
    have : IsEmpty (DivisorFamily.empty X).ι := inferInstanceAs (IsEmpty PEmpty)
    exists_snc_data_of_isEmpty (DivisorFamily.empty X).component⟩

/-- `isSnc_empty_of_smooth` for ANY divisor family with an empty index type: no component to be
regular, and at each point the regular system of parameters of the stalk with the empty assignment.
Used for the restricted family `E.comap j` of a closed-embedding situation with `E = ∅` (clause (5)
of `AlgebraicGeometry.exists_functorial_principalization`). -/
theorem isSnc_of_isEmpty (f : X ⟶ Spec (.of k)) [Smooth f] (E : DivisorFamily X)
    (hE : IsEmpty E.ι) : E.IsSnc :=
  ⟨fun i => hE.elim i, fun x =>
    have := isRegularLocalRing_stalk f x
    have : IsEmpty E.ι := hE
    exists_snc_data_of_isEmpty E.component⟩

end AlgebraicGeometry
