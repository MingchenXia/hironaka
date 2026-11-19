/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MaximalContact.Basic
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# MC-invariant ideal sheaves

[Kol07, 53.1]: `I` is *maximal contact invariant*, or *MC-invariant*, if `MC(I) · D(I) ⊂ I`, that
is, `D^{m−1}(I) · D(I) ⊂ I`. It is the hypothesis of [Kol07, Theorem 92] (uniqueness of maximal
contact up to étale equivalence), recalled in the paragraph before that theorem, and through it of
the independence of the order-reduction functor from the hypersurface of maximal contact
(`Hironaka/Resolution/Algebraic/MaximalContact/FunctorIndependence.lean`).

* **The predicate** (`IsMCInvariant f I m`): for the ideal sheaf `I` on the `k`-scheme `X` and the
  mark `m` (Kollár's `m = max-ord I`, a hypothesis of the theorems that use it, as for `MC`),
  `MC f I m * derivative f I ≤ I`, with the maximal contact ideal sheaf `MC(I) = D^{m−1}(I)`
  (`Hironaka/Resolution/Algebraic/MaximalContact/Basic.lean`), the derivative ideal sheaf `D(I)`,
  the product of ideal sheaves, and inclusion.
* **Relation to the ring-level predicate** (`RegularCoords.IsMCInvariant` in
  `Hironaka/Algebra/Local/MaximalContact.lean`): the same condition for an ideal of a regular local
  ring in coordinates; at a stalk with coordinates spanning the `k`-derivations the two meet through
  `stalkIdeal_derivative`, `derivative_eq_D`, `stalkIdeal_MC` and `stalkIdeal_mul`
  (`isMCInvariant_stalk` in `Hironaka/Resolution/Algebraic/MaximalContact/FormalEquivBridge.lean`).
  Not a duplicate: the sheaf-level form of the ring-level definition, as `MC` is of
  `RegularCoords.MC`.

The predicate is also used by the tuning of ideals (`Hironaka/Resolution/Algebraic/Tuning/`) and by
`Hironaka/Resolution/Algebraic/OrderReduction/Step22Indep.lean`.
-/

@[expose] public section

namespace AlgebraicGeometry.Scheme.IdealSheafData

open CategoryTheory

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- [Kol07, 53.1] in sheaf form: the ideal sheaf `I` is **MC-invariant** with respect to the mark
`m` if `MC(I) · D(I) ⊆ I`, with `MC(I) = D^{m−1}(I)` the maximal contact ideal sheaf and `D(I)` the
derivative ideal sheaf. The hypothesis of [Kol07, Theorem 92]. `RegularCoords.IsMCInvariant` is
the same definition for an ideal of a regular local ring in coordinates. -/
def IsMCInvariant (I : X.IdealSheafData) (m : ℕ) : Prop :=
  MC f I m * derivative f I ≤ I

/-- The definition unfolded. -/
theorem isMCInvariant_iff (I : X.IdealSheafData) (m : ℕ) :
    IsMCInvariant f I m ↔ MC f I m * derivative f I ≤ I :=
  Iff.rfl

end AlgebraicGeometry.Scheme.IdealSheafData
