/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MaximalContact.Basic
public import Hironaka.Scheme.Snc.SmoothDivisor
public import Hironaka.Scheme.IdealSheaf.Order.Constructible
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
/-!
# The classes of triples in the global case of the proof of Theorem 103

Kollár's Theorem 103 [Kol07, Theorem 103] constructs the order reduction functor `BO_{n,m}` "on
triples `(X, I, E)` with `dim X = n` and `max-ord I ≤ m`". The global case of its proof
[Kol07, 104, Step 3] covers `X` by open subsets `X^(j)` "such that on each `X^(j)` there is a
smooth hypersurface of maximal contact `H^(j) ⊂ X^(j)`", takes the disjoint union
`H^* := ∐ H^(j) ⊂ ∐ X^(j) =: X^*` ("a smooth hypersurface of maximal contact") with `g : X^* → X`
"the coproduct of the injections", and descends `BO_{n,m}(X^*, g^* I, g^{-1} E)` to `X` "as in
(37)". This is [Kol07, Theorem 105] with `M` = coproducts of open immersions
(`openImmersionCoprods`), `GT` = the triples of Theorem 103 and `LT` = those admitting a global
smooth hypersurface of maximal contact ([Kol07, 104, Step 2]: the assumption that a smooth
hypersurface of maximal contact `H ⊂ X` exists "is always satisfied in a suitable open
neighborhood of any point" by Theorem 80 (2), may hold globally, and is preserved under disjoint
unions).

This module defines the two classes, in the vocabulary of `IsMaximalContact` (the condition
`𝒪_X(−H) ⊆ MC(I)`), `IsSmoothDivisor` and `maxOrd`. That they satisfy the hypotheses (2)(i)–(ii)
of Theorem 105 is proved in `Hironaka/Resolution/Algebraic/Kol07/MaximalContactGlobalization.lean`.

* `Triple.HasDim T n`: `dim X = n`, i.e. the structure morphism is smooth of relative dimension
  `n` (the triple's `smoothOfRelativeDimension` fixes one such `n`).
* `Triple.OrderClass n m`: `GT_{n,m}`, the triples with `dim X = n` and `max-ord I ≤ m`.
* `Triple.HasMaximalContact T m`: `(X, I, E)` admits a global smooth hypersurface of maximal
  contact for `(I, m)`, a smooth divisor `H` with `𝒪_X(−H) ⊆ MC(I) = D^{m-1}(I)`.
* `Triple.MaximalContactClass n m`: `LT_{n,m}`, the members of `GT_{n,m}` admitting one.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Triple

open Hironaka

variable {k : Type u} [Field k]

/-- The triple's ambient scheme has dimension `n` ("triples `(X, I, E)` with `dim X = n`" in
[Kol07, Theorem 103]): its structure morphism is smooth of relative dimension `n` (the
equidimensionality of [Kol07, Notation 64], `Triple.smoothOfRelativeDimension`, made definite). -/
def HasDim (T : Triple k) (n : ℕ) : Prop :=
  SmoothOfRelativeDimension n (T.X.left ↘ Spec (CommRingCat.of k))

/-- The class `GT_{n,m}` of "triples `(X, I, E)` with `dim X = n` and `max-ord I ≤ m`"
[Kol07, Theorem 103]: the domain of `BO_{n,m}`, and the global triples of Theorem 105 in the
global case of the proof [Kol07, 104, Step 3]. -/
def OrderClass (n m : ℕ) (T : Triple k) : Prop :=
  T.HasDim n ∧ T.I.maxOrd ≤ (m : ℕ∞)

/-- The triple **admits a global smooth hypersurface of maximal contact** for the mark `m`
("assume that there is a smooth hypersurface of maximal contact `H ⊂ X`", [Kol07, 104, Step 2]):
a smooth divisor `H` (`IsSmoothDivisor`) with `𝒪_X(−H) ⊆ MC(I) = D^{m-1}(I)`
(`IsMaximalContact`). -/
def HasMaximalContact (T : Triple k) (m : ℕ) : Prop :=
  ∃ H : T.X.left.IdealSheafData, IsSmoothDivisor H ∧
    Scheme.IdealSheafData.IsMaximalContact (T.X.left ↘ Spec (CommRingCat.of k)) T.I m H

/-- The class `LT_{n,m}` of local triples: the members of `GT_{n,m}` admitting a global smooth
hypersurface of maximal contact. These are the local triples of Theorem 105 in the global case
of the proof of Theorem 103 [Kol07, 104, Step 3], the domain on which the maximal contact case
[Kol07, 104, Step 2] defines `BO_{n,m}`. -/
def MaximalContactClass (n m : ℕ) (T : Triple k) : Prop :=
  OrderClass n m T ∧ T.HasMaximalContact m

end AlgebraicGeometry.Triple
