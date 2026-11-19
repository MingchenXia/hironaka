/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Regular points of a scheme

Hironaka's *simple points* and *non-singular* schemes in Mathlib's vocabulary. Hironaka calls a
point *simple* (resp. *multiple*) "if the local ring of the scheme at the point is regular (resp.
not regular)", in "the absolute sense of Grothendieck" [Hir64, Ch. I, p. 163; footnote 29, p. 161],
and asks of the resolving scheme `X̃` that it be "non-singular in the sense that all the local rings
of `X̃` are regular" [Hir64, Introduction, p. 112]. Accordingly a scheme `X` is *regular at* a point
`x` (`x` is a simple point) when the stalk `𝒪_{X,x}` is a regular local ring; `X` is *regular* (the
class `IsRegular X`, like Mathlib's `IsReduced X`) when it is regular at every point; the *singular
locus* `X.singularLocus` is the set of points at which `X` is not regular.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

namespace Scheme

variable (X : Scheme.{u})

/-- `X` is *regular at* `x`, and `x` is a *simple point* of `X`, when the stalk `𝒪_{X,x}` is a
regular local ring [Hir64, Ch. I, p. 163; footnote 29, p. 161]. -/
def IsRegularAt (x : X) : Prop :=
  IsRegularLocalRing (X.presheaf.stalk x)

/-- The *singular locus*: the set of points at which `X` is not regular. It is Hironaka's set of
multiple points, "the singular locus of an algebraic scheme V is by definition the set of multiple
points of V" [Hir64, Ch. I, p. 163]; the complement of "the open subscheme of X which consists of
the simple points of X" [Hir64, Introduction, p. 112]. It is closed when `X` is locally of finite
type over a perfect field. -/
def singularLocus : Set X :=
  {x | ¬ X.IsRegularAt x}

end Scheme

/-- `X` is *regular* when it is regular at every point.

Relation to the source.
* **Translation.** `IsRegular X` is Hironaka's "$X$ is non-singular": he asks of the resolving
  scheme $\tilde X$ that it be "non-singular in the sense that all the local rings of $\tilde X$
  are regular" [Hir64, Introduction, p. 112]. -/
class IsRegular (X : Scheme.{u}) : Prop where
  isRegularAt : ∀ x : X, X.IsRegularAt x

end AlgebraicGeometry
