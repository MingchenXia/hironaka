/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Defs

/-!
# Morphisms of finite type

A morphism of schemes is of finite type (`AlgebraicGeometry.FiniteType`) if it is locally of finite
type and quasi-compact [Sta, Tag 01T0]. The class is bundled like Mathlib's `IsProper`: its parents
are instances, and conversely `FiniteType f` is inferred from the two parts (the instance
`FiniteType.of_locallyOfFiniteType_of_quasiCompact`), so that statements may carry the bundled class
while the lemmas feeding them keep the two unbundled ones. `finiteType_iff` unbundles it.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

attribute [mk_iff] FiniteType

/-- A morphism that is locally of finite type and quasi-compact is of finite type. -/
instance FiniteType.of_locallyOfFiniteType_of_quasiCompact {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] : FiniteType f where

end AlgebraicGeometry
