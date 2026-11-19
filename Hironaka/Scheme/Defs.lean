/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Properties of schemes and of morphisms of schemes

Properties, absent from Mathlib, of the schemes and structure morphisms over which the algebraic
main theorems quantify.

* A morphism of schemes is *of finite type* if it is locally of finite type and quasi-compact
  [Sta, Tag 01T0]. The class `AlgebraicGeometry.FiniteType` bundles Mathlib's
  `LocallyOfFiniteType` and `QuasiCompact`, as Mathlib's `IsProper` bundles its parts, and its
  parents are instances.
* `HasDisjointIntegralComponents X`: `X` is reduced and its irreducible components are pairwise
  disjoint — for a scheme of finite type over a field, a finite disjoint union of integral schemes,
  the schemes on which Kollár constructs the resolution functor before gluing
  [Kol07, Proposition 37 and the proof of Theorem 36].
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A morphism of schemes is of finite type if it is locally of finite type and quasi-compact. -/
@[stacks 01T0]
class FiniteType {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop
    extends LocallyOfFiniteType f, QuasiCompact f

end AlgebraicGeometry
