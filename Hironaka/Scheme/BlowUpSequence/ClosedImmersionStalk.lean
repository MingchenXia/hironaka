/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.RestrictDivisors
import Hironaka.Scheme.Smooth.GraphCompletion
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Stalks of a closed subscheme through an isomorphism of the ambient stalks

"Since `Z_j` is smooth, `g` is not an isomorphism over any point of `Sing X̄`"
[Kol07, Theorem 27, proof]; read backwards, this gives the clause of [Kol07, Theorem 36 (3)] that
the resolution is an isomorphism exactly over the smooth locus: at a point `p` of the end result
`X_j ⊆ A_j` over which the ambient sequence is a local isomorphism
(`Hironaka/Resolution/Algebraic/Kol07/OffCenters.lean`), the local ring of `X_j` at `p` is the local
ring of `X` at `g(p)`, so `X` is smooth at `g(p)` because `X_j` is. The transport is a chain of ring
isomorphisms: the stalk of a closed subscheme is the quotient of the ambient stalk by the stalk of
its ideal (the first isomorphism theorem, the stalk map being surjective with kernel that stalk,
`ker_stalkMap_of_isClosedImmersion`), the ambient stalks are isomorphic, and the isomorphism
carries one ideal onto the other (`Ideal.quotientEquiv`).

* `stalkEquivQuotient_of_isClosedImmersion`: `𝒪_{Y,y} ≃ 𝒪_{X,g y} / (ker g)_{g y}`.
* `isRegularLocalRing_stalk_of_isIso_stalkMap_of_stalkIdeal_eq`: for two closed immersions
  `g : Y ⟶ X`, `g' : Y' ⟶ X'`, a morphism `f : X' ⟶ X` and points `p : Y'`, `y : Y` with
  `f (g' p) = g y`, `f` an isomorphism on stalks at `g' p` carrying `(ker g)_{f (g' p)}` onto
  `(ker g')_{g' p}`, the local ring of `Y` at `y` is regular when that of `Y'` at `p` is.

The schemes are arbitrary.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- The stalk of the source of a closed immersion `g` at `y` is the quotient of the stalk of the
target at `g y` by the stalk of `ker g` (the first isomorphism theorem for the surjective stalk
map, `ker_stalkMap_of_isClosedImmersion`). -/
noncomputable def stalkEquivQuotient_of_isClosedImmersion (g : Y ⟶ X) [IsClosedImmersion g]
    (y : Y) : X.presheaf.stalk (g y) ⧸ g.ker.stalkIdeal (g y) ≃+* Y.presheaf.stalk y :=
  (Ideal.quotEquivOfEq (ker_stalkMap_of_isClosedImmersion g y)).symm.trans
    (RingHom.quotientKerEquivOfSurjective (g.stalkMap_surjective y))

/-- For closed immersions `g : Y ⟶ X`, `g' : Y' ⟶ X'`, a morphism `f : X' ⟶ X` and points `p : Y'`,
`y : Y` with `f (g' p) = g y`, if `f` is an isomorphism on stalks at `g' p` carrying the stalk of
`ker g` onto the stalk of `ker g'`, then the local ring of `Y` at `y` is regular whenever the
local ring of `Y'` at `p` is:
`𝒪_{Y',p} ≃ 𝒪_{X',g' p}/(ker g') ≃ 𝒪_{X,f (g' p)}/(ker g) ≃ 𝒪_{X,g y}/(ker g) ≃ 𝒪_{Y,y}`. Not in
the sources in this form; it is the transport behind [Kol07, Theorem 27, proof] read backwards. -/
theorem isRegularLocalRing_stalk_of_isIso_stalkMap_of_stalkIdeal_eq {X' Y' : Scheme.{u}}
    (g : Y ⟶ X) [IsClosedImmersion g] (g' : Y' ⟶ X') [IsClosedImmersion g'] (f : X' ⟶ X)
    {p : Y'} {y : Y} (hpt : f (g' p) = g y) [IsIso (f.stalkMap (g' p))]
    (h2 : g'.ker.stalkIdeal (g' p) = (g.ker.stalkIdeal (f (g' p))).map (f.stalkMap (g' p)).hom)
    [IsRegularLocalRing (Y'.presheaf.stalk p)] : IsRegularLocalRing (Y.presheaf.stalk y) := by
  let e1 : Y'.presheaf.stalk p ≃+* X'.presheaf.stalk (g' p) ⧸ g'.ker.stalkIdeal (g' p) :=
    (stalkEquivQuotient_of_isClosedImmersion g' p).symm
  let α : X.presheaf.stalk (f (g' p)) ≃+* X'.presheaf.stalk (g' p) :=
    (asIso (f.stalkMap (g' p))).commRingCatIsoToRingEquiv
  have h2' : g'.ker.stalkIdeal (g' p) =
      (g.ker.stalkIdeal (f (g' p))).map (α : X.presheaf.stalk (f (g' p)) →+* _) := h2
  let e2 : X'.presheaf.stalk (g' p) ⧸ g'.ker.stalkIdeal (g' p) ≃+*
      X.presheaf.stalk (f (g' p)) ⧸ g.ker.stalkIdeal (f (g' p)) :=
    (Ideal.quotientEquiv (g.ker.stalkIdeal (f (g' p))) (g'.ker.stalkIdeal (g' p)) α h2').symm
  let σ : X.presheaf.stalk (f (g' p)) ≃+* X.presheaf.stalk (g y) :=
    (X.presheaf.stalkCongr (Inseparable.of_eq hpt)).commRingCatIsoToRingEquiv
  let e3 : X.presheaf.stalk (f (g' p)) ⧸ g.ker.stalkIdeal (f (g' p)) ≃+*
      X.presheaf.stalk (g y) ⧸ g.ker.stalkIdeal (g y) :=
    Ideal.quotientEquiv _ _ σ (stalkIdeal_map_stalkCongr g.ker hpt).symm
  let e4 : X.presheaf.stalk (g y) ⧸ g.ker.stalkIdeal (g y) ≃+* Y.presheaf.stalk y :=
    stalkEquivQuotient_of_isClosedImmersion g y
  exact IsRegularLocalRing.of_ringEquiv (e1.trans (e2.trans (e3.trans e4)))

end AlgebraicGeometry
