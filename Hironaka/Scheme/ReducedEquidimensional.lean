/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Resolution.Defs

/-!
# Reduced equidimensional schemes

The API of `AlgebraicGeometry.Scheme.IsReducedEquidimensional k X`
(`Hironaka.Scheme.Resolution.Defs`): `X` is reduced and its smooth locus over `k` is smooth of one
relative dimension. Its members are the objects of `AlgebraicGeometry.ReducedEquidimensionalScheme`,
the inputs of Kollár's Theorem 36, and the resolution functor of the library
(`Hironaka.Resolution.BRFunctor`) is constructed and proved on them.

The predicate is the equidimensionality of [Kol07, Notation 64 (1)] ("`X` is a smooth,
equidimensional (possibly reducible) scheme of finite type over a field of characteristic zero", in
force for the chapter that proves Theorem 36), transported to reduced, possibly singular schemes
through Mathlib's `Scheme.Hom.smoothLocus`. The irreducible components of a member may meet. The
class is stable under open subschemes and under finite disjoint unions of open subschemes of one
member (`Hironaka.Resolution.Algebraic.Kol07.Thm36.ClassClosure`); it is not stable under arbitrary
finite disjoint unions (a point and a line are not equidimensional). The empty scheme is a member
(its smooth locus is smooth of every relative dimension). Why the equidimensionality is needed, and
the stability of the class under change of fields and étale morphisms, are recorded in the docstring
of `AlgebraicGeometry.exists_functorial_resolution`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace Scheme.IsReducedEquidimensional

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))]

/-- A member is reduced. -/
theorem isReduced (h : X.IsReducedEquidimensional k) : IsReduced X := h.1

/-- The smooth locus of a member is smooth of one relative dimension. -/
theorem exists_smoothOfRelativeDimension (h : X.IsReducedEquidimensional k) :
    ∃ d : ℕ, SmoothOfRelativeDimension d ((X ↘ Spec (.of k)).smoothLocus.ι ≫ (X ↘ Spec (.of k))) :=
  h.2

end Scheme.IsReducedEquidimensional

end AlgebraicGeometry
