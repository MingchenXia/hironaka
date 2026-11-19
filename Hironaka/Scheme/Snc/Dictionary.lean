/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.IdealSheaf.Order.Along
public import Hironaka.Scheme.Snc.Defs
/-!
# The dictionary between Hironaka's boundaries and Kollár's divisor families: the definitions

Hironaka's Main Theorem II [Hir64, Main Theorem II] speaks of one reduced closed subscheme `E` (an
ideal sheaf) "with only normal crossings" [Hir64, Definition 2]; Kollár's simple normal crossing
divisors [Kol07, Definition 24] are ordered finite families `E = ∑ E^i` of divisors
(`AlgebraicGeometry.Scheme.DivisorFamily`). Both directions of the passage are needed to state
Hironaka's theorem in terms of Kollár's sequences and vice versa:

* `IdealSheafData.componentFamily E`: the family of the irreducible components of `V(E)`, each
  with its reduced structure (the vanishing ideal sheaf of the component), indexed by the generic
  points of `V(E)` (`Closeds.genericPoints`: the points of `V(E)` maximal for specialization, one
  per irreducible component) and ordered by a well-ordering of that index set. This reads
  Hironaka's "irreducible component (i.e., a maximal reduced irreducible subscheme) of `E`"
  [Hir64, Definition 2] as Kollár's "`E = ∑ E^i` with ordered index set" [Kol07, Definition 31];
  the ordering plays no role in the dictionary.
* `DivisorFamily.unionIdeal F`: the reduced ideal sheaf of the union of the members of a family,
  the vanishing ideal sheaf of `⋃ᵢ V(E^i)`, Hironaka's `red(⋃ E^i)`, the shape of his boundary
  `E_{i+1} = red(f_i⁻¹(E_i) ∪ f_i⁻¹(D_i))` in clause (iii) of Main Theorem II (`reducedTransform`).

The index set of `componentFamily` is finite on a Noetherian space (`Closeds.genericPoints_finite`:
a closed set is a finite union of irreducible closed sets, Mathlib's
`NoetherianSpace.exists_finite_set_isClosed_irreducible`, and each of these has at most one
generic point), which is the `Fintype` instance Kollár's families carry. This module holds the
definitions only; the dictionary itself is proved in `Hironaka/Scheme/Snc/DictionaryOrder.lean`,
`DictionaryBoundary.lean` and `DictionaryComponents.lean`.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme

namespace TopologicalSpace.Closeds

variable {Y : Type*} [TopologicalSpace Y]

/-- In a Noetherian sober `T₀` space a closed set has finitely many generic points: it is a finite
union of irreducible closed sets (Mathlib's
`NoetherianSpace.exists_finite_set_isClosed_irreducible`), a generic point of `Z` is the generic
point of the member containing it (maximality,
`Closeds.mem_genericPoints_iff`), and an irreducible closed set has at most one generic point
(`T₀`). -/
theorem genericPoints_finite [T0Space Y] [QuasiSober Y] [NoetherianSpace Y] (Z : Closeds Y) :
    Z.genericPoints.Finite := by
  obtain ⟨S, hSf, hScl, hSirr, hZS⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible Z.isClosed
  have hsub : Z.genericPoints ⊆ ⋃ t ∈ S, {η | IsGenericPoint η t} := by
    intro η hη
    have hηZ : η ∈ (Z : Set Y) := hη.1
    rw [hZS] at hηZ
    obtain ⟨t, htS, hηt⟩ := Set.mem_sUnion.mp hηZ
    refine Set.mem_iUnion₂.mpr ⟨t, htS, ?_⟩
    have hmax := (Closeds.mem_genericPoints_iff Z η).mp hη
    have h1 : closure {η} ⊆ t :=
      (hScl t htS).closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hηt)
    have htZ : t ⊆ (Z : Set Y) := by
      rw [hZS]
      exact Set.subset_sUnion_of_mem htS
    have h2 : t ⊆ closure {η} := hmax.2 ⟨htZ, hSirr t htS⟩ h1
    exact isGenericPoint_def.mpr (le_antisymm h1 h2)
  refine (hSf.biUnion fun t _ => ?_).subset hsub
  exact Set.Subsingleton.finite fun a ha b hb => ha.eq hb

/-- The generic points of a closed set of a Noetherian sober `T₀` space form a finite type. -/
instance instFiniteGenericPoints [T0Space Y] [QuasiSober Y] [NoetherianSpace Y] (Z : Closeds Y) :
    Finite Z.genericPoints :=
  Z.genericPoints_finite.to_subtype

end TopologicalSpace.Closeds

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- **The family of the irreducible components of the closed subscheme `V(E)`**, as a divisor
family with ordered index set [Kol07, Definition 31]: indexed by the generic points of `V(E)`
(`Closeds.genericPoints`; one per irreducible component), each component the closed set
`closure {η}` with its reduced structure (the vanishing ideal sheaf), the index set ordered by a
well-ordering (Mathlib's `WellOrderingRel`; the ordering is immaterial to the dictionary). These
are Hironaka's "irreducible components (i.e., maximal reduced irreducible subschemes) of `E`"
[Hir64, Definition 2]. Finite when `X` is Noetherian (`Closeds.genericPoints_finite`). -/
noncomputable def componentFamily (E : X.IdealSheafData) [Finite E.support.genericPoints] :
    DivisorFamily X where
  ι := E.support.genericPoints
  fintype := Fintype.ofFinite _
  linearOrder := IsWellOrder.linearOrder WellOrderingRel
  component := fun η => vanishingIdeal (Closeds.closure {(η : X)})

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.DivisorFamily

variable {X : Scheme.{u}}

/-- **The reduced ideal sheaf of the union of the members** of a divisor family: the vanishing
ideal sheaf of `⋃ᵢ V(E^i)`, Hironaka's `red(∑ E^i)`, the operation behind the boundary
`red(f⁻¹(E) ∪ f⁻¹(D))` of [Hir64, Main Theorem II (iii)], applied to Kollár's total transform
[Kol07, Definition 25] with the ordering forgotten. -/
noncomputable def unionIdeal (F : DivisorFamily X) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal F.support

end AlgebraicGeometry.Scheme.DivisorFamily
