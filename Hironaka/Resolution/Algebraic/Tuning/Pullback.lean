/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Tuning.Sheaf
import Hironaka.Resolution.Algebraic.Tuning.Transform
import Hironaka.Scheme.BlowUp.Transform.StrictTransform
import Hironaka.Scheme.IdealSheaf.Derivative.BaseChange
import Hironaka.Scheme.IdealSheaf.Derivative.Pullback
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Functoriality of the tuned ideal under smooth pull-back and change of fields

[Kol07, Lemma 74 (4)]: "if `f : Y → X` is smooth, then `D(f^* I) = f^*(D(I))`"
(`derivativeIter_comap_of_smooth`). The maximal coefficient ideal
`W_s(I) = ∑_{wt(e) ≥ s} ∏_j (D^j I)^{e_j}` of [Kol07, Definition 98] is built from the derivative
ideals by sums, products and powers, all of which commute with pull-back (`comap_iSup`,
`comap_finset_prod`, `comap_pow`); hence `W_s(g^* I) = g^* W_s(I)` for a smooth morphism `g : Y → X`
of smooth `k`-schemes (`W_comap_of_smooth`), the structure morphism of `Y` being `g ≫ f`. This is
what Step 2.3 of [Kol07, 104] and Step 3 of the proof of [Kol07, Theorem 103] need; compare [Wlo05,
Lemma 2.9.3] for the analogous statement about Włodarczyk's coefficient ideal.

The same computation, with the derivative ideals commuting with a change of the base field along
`σ : k → L` in characteristic zero (`derivativeIter_comap_of_isPullback_specMap` of
`Hironaka.Scheme.IdealSheaf.Derivative.BaseChange`), gives `W_s(p^* I) = p^* W_s(I)` on a cartesian
square `p : X_L → X` over `Spec σ` (`W_comap_of_isPullback_specMap`), the derivative ideals of `X_L`
being taken over `L`; this is the change-of-fields functoriality [Kol07, 34.2] for the tuned ideal.
-/

public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.IdealSheafData
  IsLocalRing

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) [Smooth f]
  [Smooth g]

/-- The tuned ideal commutes with pull-back along a smooth morphism, `W_s(g^* I) = g^* W_s(I)`
([Kol07, Lemma 74 (4)] applied to the construction of [Kol07, Definition 98]). -/
theorem W_comap_of_smooth (I : X.IdealSheafData) (m s : ℕ) :
    W (g ≫ f) (I.comap g) m s = (W f I m s).comap g := by
  rw [W_eq, W_eq, comap_iSup]
  refine iSup_congr fun e => ?_
  rw [comap_iSup]
  refine iSup_congr fun _ => ?_
  rw [comap_finset_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [comap_pow, derivativeIter_comap_of_smooth f g j I]

section BaseChange

variable {L : Type u} [Field L] {σ : k →+* L} {p : Y ⟶ X} {g' : Y ⟶ Spec (.of L)}

/-- The tuned ideal commutes with the change of fields along `σ : k → L` in characteristic zero: on
a cartesian square `p : X_L → X` over `Spec σ`, `W_s(p^* I) = p^* W_s(I)`, the derivative ideals of
`X_L` taken over `L` ([Kol07, Lemma 74 (4)] and [Kol07, 34.2]; compare [Wlo05, Lemma 2.9.3]). -/
theorem W_comap_of_isPullback_specMap [CharZero k]
    (sq : IsPullback p g' f (Spec.map (CommRingCat.ofHom σ))) (I : X.IdealSheafData) (m s : ℕ) :
    W g' (I.comap p) m s = (W f I m s).comap p := by
  rw [W_eq, W_eq, comap_iSup]
  refine iSup_congr fun e => ?_
  rw [comap_iSup]
  refine iSup_congr fun _ => ?_
  rw [comap_finset_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [comap_pow, derivativeIter_comap_of_isPullback_specMap sq j I]

end BaseChange

end AlgebraicGeometry.Scheme.IdealSheafData
