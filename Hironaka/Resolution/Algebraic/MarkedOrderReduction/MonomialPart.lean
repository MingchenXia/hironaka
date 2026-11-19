/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.IdealSheaf.Order.Along
public import Hironaka.Scheme.Snc.Defs

/-!
# The monomial and nonmonomial parts of an ideal sheaf

[Kol07, Definition–Lemma 110]: the ideal sheaf `I` of a triple `(X, I, E)` factors uniquely as
`I = M(I) · N(I)`, where the monomial part `M(I) = 𝒪_X(−∑ c_i E^i)` is a monomial in the members of
`E` and the cosupport of the nonmonomial part `N(I)` contains none of the `E^i`; as the members
need not be irreducible, `cosupp N(I)` may still contain irreducible components of some `E^i`.

## Conventions

The split is taken in its fine form: the exponents are indexed by the irreducible components `D` of
the members `E^i`, not by the members, `M(I) := ∏_D 𝓘_D^{ord_D I}` with `ord_D I` the order of `I`
at the generic point of `D` ([Kol07, Definition 47]), and `N(I) := I · M(I)^{-1}`, so that
`I = M(I) · N(I)` uniquely with `ord_D N(I) = 0` for every `D`. This is the split of
[BM08, (5.2)], where `M(I)` is the product of the prime ideals of the irreducible components of the
members of `E` and no such prime divides `N(I)`, and of [Wlo05, Section 3, Step 2], the product of
the principal ideals of the irreducible components of the divisors in `E`.
Kollár's coarse form, one exponent per member [Kol07, 111], is not used: it does not commute with
open immersions, so clause (2) of [Kol07, Theorem 107] would fail for it; the Correction item of
`AlgebraicGeometry.exists_functorial_principalization` records this with a counterexample. The fine
split commutes with smooth pull-back
(`Hironaka/Resolution/Algebraic/MarkedOrderReduction/SplitFunctorial.lean`).

* `DivisorFamily.monomial E a` is the monomial ideal `𝒪_X(−∑_D a_D D)` of the family `E` with one
  exponent `a_D` per irreducible component `D` of the members `E^i`: the product over the members
  `i` and over the generic points `η` of `V(E^i)` (`Closeds.genericPoints`, one per irreducible
  component) of `𝓘_D^{a(η)}`, `𝓘_D` the reduced ideal of the component `D = closure {η}` (the
  vanishing ideal sheaf). The exponent is a function of the generic point. The inner product is a
  `finprod`, so that the definition needs no finiteness instance; on a Noetherian scheme the
  generic points of a closed set are finitely many and the product is the finite product. On a
  family with normal crossings the components of distinct members are distinct, so each
  irreducible component of `∑ E^i` contributes once.
* `BMO.monomialPart I E` is `M(I) = ∏_D 𝓘_D^{ord_D I}`: the monomial ideal of `E` with exponent
  `ord_η I` at the generic point `η` of `D`, read as a natural number by `ENat.toNat` (`ord_D I` is
  finite when `I` is nonzero on every irreducible component; for a vanishing `I` the exponent
  reads `0`).
* `BMO.nonmonomialPart I E` is `N(I) = I · M(I)^{-1}`, as the colon ideal sheaf `(I : M(I))`, the
  division by an invertible ideal sheaf: `M(I) · (I : M(I)) = I` exactly when `M(I)` divides `I`.

The properties of the split, that `M(I)` is invertible, `I = M(I) · N(I)`, `ord_D N(I) = 0`, the
uniqueness and the compatibility with smooth pull-back and change of fields, are proved in
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Split.lean`, `SplitOrder.lean`,
`SplitMain.lean`, `SplitSupport.lean`, `SplitFunctorial.lean` and, on a triple, `SplitTriple.lean`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.DivisorFamily

variable {X : Scheme.{u}}

/-- **The monomial ideal `𝒪_X(−∑_D a_D D)` of the family `E`** with one exponent per irreducible
component `D` of the members ([Kol07, Definition–Lemma 110], "`𝒪_X(−∑ c_i E^i)`", read on the
irreducible components of the `E^i` as in [BM08, (5.2)]): the product over the members `E^i` and
over the generic points `η` of `V(E^i)` of the `a(η)`-th power of the reduced ideal of the
component `closure {η}`. -/
noncomputable def monomial (E : DivisorFamily X) (a : X → ℕ) : X.IdealSheafData :=
  ∏ i, ∏ᶠ η ∈ (E.component i).support.genericPoints,
    Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {η}) ^ a η

end AlgebraicGeometry.Scheme.DivisorFamily

namespace Hironaka.BMO

open Scheme

variable {X : Scheme.{u}}

/-- **The monomial part `M(I)`** of `I` with respect to the family `E` ([Kol07, Definition–Lemma
110], "`M(I)` is called the monomial part of `I`", in the fine form `M(I) = ∏_D 𝓘_D^{ord_D I}` of
[BM08, (5.2)] and [Wlo05, Section 3, Step 2]): the monomial ideal of `E` whose exponent at the
irreducible component `D` is `ord_D I`, the order of `I` at the generic point of `D`
([Kol07, Definition 47]), as a natural number. -/
noncomputable def monomialPart (I : X.IdealSheafData) (E : DivisorFamily X) : X.IdealSheafData :=
  E.monomial fun η => (I.ord η).toNat

/-- **The nonmonomial part `N(I)`** of `I` with respect to `E` ([Kol07, Definition–Lemma 110],
"`N(I)` the nonmonomial part of `I`"): the quotient `I · M(I)^{-1}` of `I` by the invertible ideal
sheaf `M(I)`, as the colon ideal sheaf `(I : M(I))`. -/
noncomputable def nonmonomialPart (I : X.IdealSheafData) (E : DivisorFamily X) :
    X.IdealSheafData :=
  I.colon (monomialPart I E)

theorem monomialPart_eq_monomial (I : X.IdealSheafData) (E : DivisorFamily X) :
    monomialPart I E = E.monomial fun η => (I.ord η).toNat := rfl

theorem nonmonomialPart_eq_colon (I : X.IdealSheafData) (E : DivisorFamily X) :
    nonmonomialPart I E = I.colon (monomialPart I E) := rfl

end Hironaka.BMO
