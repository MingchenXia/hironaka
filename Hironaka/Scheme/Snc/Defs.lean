/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.Defs
public import Hironaka.Algebra.RegularSmooth.Defs
public import Hironaka.Scheme.BlowUp.Transform.Defs

/-!
# Normal crossings

The two readings of normal crossings in which the algebraic main theorems are stated, both at the
stalk, with a regular system of parameters (`IsLocalRing.IsRegularSystemOfParameters`) for
"local coordinates `z_1, …, z_n ∈ 𝔪_x`".

* Kollár's divisors with ordered index set [Kol07, Definition 31], `DivisorFamily X`: a finite
  linearly ordered family of closed subschemes, each given by its ideal sheaf. `IsSncAt` is the
  simple normal crossing condition of [Kol07, Definition 24] at one point (an injective assignment
  of local coordinates to the components through the point), `IsSnc` quantifies it over all points
  and asks the components to be regular, and `HasSncWith` is clause (4) of that definition. The
  support, the singular locus `Sing E` (the points on at least two components), the inverse image
  family `comap` and the empty family complete the vocabulary; `totalTransform` is the total
  transform of [Kol07, Definition 25] under one blow-up (the strict transforms of the components
  followed by the exceptional divisor, which receives the largest index, as in
  [Kol07, Definition 65]). `IsIdealOfSncDivisor I`: `I` is the ideal sheaf `𝒪(-∑ a_j F_j)` of an
  effective divisor supported on a simple normal crossing family.
* Hironaka's Definition 2 [Hir64, Ch. 0, §5, Definition 2], `IsSncBoundaryWith E D` and
  `IsSncBoundary E` (his "`E` has only normal crossings with `D`" and "`E` has only normal
  crossings"): at every point `x` of `D` some regular system of parameters of `𝒪_{X,x}` contains a
  generator of the ideal of each irreducible component of `E` through `x` (the minimal primes of
  `E_x`) and generators of the ideal of `D`. With `D := ⊥` (the zero ideal, i.e. `D = X`) this is
  "`E` has only normal crossings". On a scheme Hironaka's components are the global irreducible
  components of `E`, so the condition is simple normal crossings of the reduced subscheme `E`: it
  agrees with `DivisorFamily.IsSnc` and `DivisorFamily.HasSncWith` for the family of irreducible
  components of `E` [Kol07, Definition 24]
  (`Hironaka.Sequence.isSncBoundary_iff_isSnc_componentFamily`,
  `Hironaka.Sequence.isSncBoundaryWith_iff_hasSncWith_componentFamily`). The analytic counterparts
  are `AnalyticManifold.IdealSheaf.IsSncBoundary` and `AnalyticSpace.ClosedSubspace.IsSncBoundary`.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

open Scheme

variable {X Y : Scheme.{u}}

/-! ### Divisors with ordered index set (Kollár Definitions 24 and 31) -/

/-- Kollár's divisor `E = ∑ E^i` with ordered index set [Kol07, Definition 31]: a finite linearly
ordered family of closed subschemes `E^i ⊆ X`, each given by its ideal sheaf. -/
structure Scheme.DivisorFamily (X : Scheme.{u}) where
  /-- The (finite, linearly ordered) index set. -/
  ι : Type u
  [fintype : Fintype ι]
  [linearOrder : LinearOrder ι]
  /-- The ideal sheaf of the component `E^i`. -/
  component : ι → X.IdealSheafData

attribute [instance] DivisorFamily.fintype DivisorFamily.linearOrder

namespace Scheme.DivisorFamily

open IdealSheafData

/-- The empty divisor `E = ∅`. -/
def empty (X : Scheme.{u}) : DivisorFamily X where
  ι := PEmpty
  component := fun i => i.elim

/-- The set of points lying on at least one component. -/
def support (E : DivisorFamily X) : Closeds X :=
  ⨆ i, (E.component i).support

/-- The singular locus `Sing E` of the divisor `∑ E^i`: the points lying on at least two components
(where a simple normal crossing divisor is singular). The principalization of Theorem 35 is an
isomorphism over the complement of `cosupp I ∪ Sing E`
(`AlgebraicGeometry.exists_functorial_principalization`). -/
def singularLocus (E : DivisorFamily X) : Closeds X :=
  ⨆ (i) (j) (_ : i ≠ j), (E.component i).support ⊓ (E.component j).support

/-- The inverse image family `h⁻¹(E)` of [Kol07, 34.1]. -/
def comap (E : DivisorFamily X) (h : Y ⟶ X) : DivisorFamily Y where
  ι := E.ι
  component := fun i => (E.component i).comap h

/-- The simple normal crossing condition of [Kol07, Definition 24] at one point: the coordinates
`z : Fin n → 𝒪_{X,x}` form a regular system of parameters, and there is an injective assignment `c`
of a coordinate index to each component through `x` (and only to those) with `E^i = (z_{c(i)} = 0)`
near `x`, that is `(E^i)_x = (z_{c(i)})`. -/
def IsSncAt (E : DivisorFamily X) (x : X) {n : ℕ} (z : Fin n → X.presheaf.stalk x) : Prop :=
  IsLocalRing.IsRegularSystemOfParameters z ∧
  ∃ c : {i : E.ι // x ∈ (E.component i).support} → Fin n, Function.Injective c ∧
    ∀ i, (E.component i.1).stalkIdeal x = Ideal.span {z (c i)}

/-- Kollár's simple normal crossing divisor [Kol07, Definition 24 (1)–(3)]: each `E^i` is smooth,
and at each point `x` there are local coordinates `z_1, …, z_n ∈ 𝔪_x` (a regular system of
parameters of `𝒪_{X,x}`) such that every component through `x` is `(z_{c(i)} = 0)` near `x`, with
`c(i) ≠ c(i')` for distinct components through `x` (`IsSncAt`). -/
def IsSnc (E : DivisorFamily X) : Prop :=
  (∀ i, IsRegular (E.component i).subscheme) ∧
  ∀ x : X, ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x), E.IsSncAt x z

/-- [Kol07, Definition 24 (4)]: the closed subscheme `Z` has simple normal crossings with `E` if at
each point `x` of `Z` one can choose the coordinates `z_1, …, z_n` as in `IsSnc` such that in
addition `Z = (z_{j_1} = ⋯ = z_{j_s} = 0)` near `x`. -/
def HasSncWith (E : DivisorFamily X) (Z : X.IdealSheafData) : Prop :=
  ∀ x ∈ Z.support, ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x), E.IsSncAt x z ∧
    ∃ s : Finset (Fin n), Z.stalkIdeal x = Ideal.span (z '' ↑s)

/-- The total transform of [Kol07, Definition 25] under one blow-up with centre `D`: the birational
transforms of the components of `E`, followed by the exceptional divisor `f⁻¹(D)`, which receives
the largest index (new divisors come after old ones, [Kol07, Definition 65]). -/
def totalTransform (E : DivisorFamily X) (D : X.IdealSheafData) : DivisorFamily
    D.blowUp where
  ι := E.ι ⊕ₗ PUnit.{u + 1}
  component := fun i =>
    Sum.elim (fun j => (E.component j).strictTransform D) (fun _ => D.exceptionalDivisor)
      (ofLex i)

end Scheme.DivisorFamily

/-- `I` is the ideal sheaf of an effective divisor `∑ a_j F_j` supported on a simple normal crossing
family `F` [Kol07, Theorem 35 (2) and its proof in 72]. -/
def Scheme.IdealSheafData.IsIdealOfSncDivisor (I : X.IdealSheafData) : Prop :=
  ∃ (F : DivisorFamily X) (a : F.ι → ℕ), F.IsSnc ∧ I = ∏ j, F.component j ^ a j

/-! ### Normal crossings (Hironaka's Definition 2) -/

/-- `E` has only normal crossings with `D` [Hir64, Ch. 0, §5, Definition 2]
(equivalently, `D` has only normal crossings with `E`): at every point `x` of `D` there is a
regular system of parameters `(z_1, …, z_n)` of `𝒪_{X,x}` such that the ideal in `𝒪_{X,x}` of
each irreducible component of `E` containing `x` (a minimal prime of `E_x`) is generated by one
of the `z_i`, and the ideal of `D` in `𝒪_{X,x}` is generated by some of the `z_i`.

On a scheme Hironaka's components are the global irreducible components of `E` (their local
ideals at `x` are the minimal primes of `E_x`), each of which is asked to be cut out by a
parameter at each of its points of `D`; so at the points of `D` the condition is that the reduced
subscheme `E` has simple normal crossings there, and has them with `D`. On a Noetherian scheme it
agrees with `DivisorFamily.HasSncWith` of the family of irreducible components of `E`
[Kol07, Definition 24 (4)] (`Hironaka.Sequence.isSncBoundaryWith_iff_hasSncWith_componentFamily`),
which is also a condition at the points of `D` only.

Nothing is asserted at the points off `D`: for the unit ideal `D = ⊤` (the empty subscheme) the
condition holds for every `E`. The manifold predicate of the same name
(`AnalyticManifold.IdealSheaf.IsSncBoundaryWith`) says more: that its boundary is the ideal of a
simple normal crossings hypersurface family at every point of the manifold, and in addition has
simple normal crossings with `D` at the points of `D`. On a scheme the condition at every point is
`IsSncBoundary` below, asserted separately where it is wanted.

Relation to the source.
* **Translation.** `IsSncBoundaryWith E D` is Hironaka's "$E$ has only normal crossings with $D$",
  and `IsSncBoundary E`, which is `IsSncBoundaryWith E ⊥`, his "$E$ has only normal crossings".
* **Restatement.** The predicate demands a regular system of parameters at every point of `D` (at
  every point of `X` for `IsSncBoundary`), so the regularity of $\mathcal{O}_{X,x}$ there is part of
  it. On a regular scheme a reduced `E` whose components are cut out by parameters has an invertible
  ideal sheaf, so Hironaka's "everywhere of codimension one" follows from reducedness and normal
  crossings at the points of `D` (everywhere for `IsSncBoundary`) and is not a separate
  hypothesis. -/
def Scheme.IdealSheafData.IsSncBoundaryWith (E D : X.IdealSheafData) : Prop :=
  ∀ x ∈ D.support, ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x),
    IsLocalRing.IsRegularSystemOfParameters z ∧
    (∀ P ∈ (E.stalkIdeal x).minimalPrimes, ∃ i, P = Ideal.span {z i}) ∧
    ∃ s : Finset (Fin n), D.stalkIdeal x = Ideal.span (z '' ↑s)

/-- Hironaka's "`E` has only normal crossings" [Hir64, Ch. 0, §5, Definition 2], his Definition 2
with `D = X` ("we simply say that E has only normal crossings at x") at every point of `X` ("with
no reference to a point, if it is the case at every point of X"): `IsSncBoundaryWith E ⊥`, the
zero ideal sheaf `⊥` being the ideal of `X` itself.

On a scheme Hironaka's components are the global irreducible components of `E`, whose local
ideals are asked to be parameters, so the condition is simple normal crossings of the reduced
subscheme `E`. On a Noetherian scheme smooth over a field it agrees with `DivisorFamily.IsSnc` of
the family of irreducible components of `E` [Kol07, Definition 24 (1)–(3)]
(`Hironaka.Sequence.isSncBoundary_iff_isSnc_componentFamily`). -/
def Scheme.IdealSheafData.IsSncBoundary (E : X.IdealSheafData) : Prop :=
  IsSncBoundaryWith E ⊥

end AlgebraicGeometry

end
