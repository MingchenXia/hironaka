/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.MonomialPart
public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
import Hironaka.Resolution.Algebraic.BoundaryClearing.Basic
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Split
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.SplitMain
import Hironaka.Resolution.Algebraic.Snc.ComponentStalks
import Hironaka.Resolution.Algebraic.Snc.DictionaryGenericPoints
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUp.Transform.StrictTransform
import Hironaka.Scheme.BlowUpSequence.BaseChangeOrder
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The monomial split, IV: smooth pull-back and change of fields

`M(h^* I) = h^* M(I)` and `N(h^* I) = h^* N(I)` for a smooth `h`, and likewise along a change of
fields: the two functoriality inputs of [Kol07, 34.1] and [Kol07, 34.2] for the marked order
reduction, whose construction is built on the split. Both are the case of a flat morphism
`p : Y → X` between the schemes of two triples carrying the pulled-back data `(p^* I, p^{-1} E)`:
the irreducible components of `p^{-1} E^i` are the components of the `p^{-1} D` (a generic point of
`p^{-1} E^i` lies over a generic point of `E^i`, `mem_genericPoints_support_of_flat`), the order of
`p^* I` at such a generic point is the order of `I` at its image
(`ord_comap_of_flat_of_stalkIdeal_eq`, the stalks of the members being the maximal ideals at the
generic points), and the stalk of `p^* 𝓘_D` at a point `y` is the image of the stalk of `𝓘_D` at
`p y`; so the stalks of `M(p^* I)` and of `p^* M(I)` agree at every `y`. The nonmonomial part
follows by the uniqueness of the split on `Y`.

* `monomialPart_comap_of_flat`, `nonmonomialPart_comap_of_flat`: for a flat `p` into a triple's
  scheme from a scheme smooth over a field, with the pulled-back family having normal crossings.
  The forms on triples, for a smooth morphism and for a change of fields, are in
  `Hironaka/Resolution/Algebraic/MarkedOrderReduction/SplitTriple.lean`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme.IdealSheafData IsLocalRing

namespace Hironaka.BMO

section Data

variable {k L : Type u} [Field k] [Field L] (T : Triple k) {Y : Scheme.{u}}
  (g : Y ⟶ Spec (.of L)) [Smooth g] [NoetherianSpace Y] (p : Y ⟶ T.X.left) [Flat p]
  (hsnc' : (T.E.comap p).IsSnc)

include hsnc'

/-- `M(p^* I) = p^* M(I)`: the monomial part of the pulled-back data along a flat `p` is the
pull-back of the monomial part. -/
theorem monomialPart_comap_of_flat :
    monomialPart (T.I.comap p) (T.E.comap p) = (monomialPart T.I T.E).comap p := by
  have hN := Hironaka.BD.noetherianSpace_triple T
  refine Scheme.IdealSheafData.ext_stalkIdeal fun y => ?_
  rw [Scheme.IdealSheafData.stalkIdeal_comap, monomialPart_eq_monomial, monomialPart_eq_monomial,
    stalkIdeal_monomial (T.E.comap p) (Snc.genericPoints_component_finite _) _ y,
    stalkIdeal_monomial T.E (Snc.genericPoints_component_finite T.E) _ (p y)]
  have hmap : ∀ F : T.E.ι → Ideal (T.X.left.presheaf.stalk (p y)),
      Ideal.map (p.stalkMap y).hom (∏ i, F i) = ∏ i, Ideal.map (p.stalkMap y).hom (F i) :=
    fun F => map_prod (Ideal.mapHom (p.stalkMap y).hom) F Finset.univ
  rw [hmap]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hx : p y ∈ (T.E.component i).support
  · have hy : y ∈ ((T.E.component i).comap p).support := by
      rw [Scheme.IdealSheafData.support_comap]
      exact hx
    obtain ⟨η, hη, hηx⟩ := exists_genericPoint_specializes _ hx
    obtain ⟨η', hη', hη'y⟩ := exists_genericPoint_specializes _ hy
    rw [Snc.finprod_stalk_eq_of_specializes (T.E.comap p) hsnc' hη' hη'y,
      Snc.finprod_stalk_eq_of_specializes T.E T.isSnc hη hηx, Ideal.map_pow,
      ← Scheme.IdealSheafData.stalkIdeal_comap]
    congr 1
    have hpη' : p η' ∈ (T.E.component i).support.genericPoints :=
      mem_genericPoints_support_of_flat p _ hη'
    have heq : p η' = η := Snc.genericPoint_eq_of_specializes T.E T.isSnc
      hpη' hη (hη'y.map p.continuous) hηx
    rw [ord_comap_of_flat_of_stalkIdeal_eq p (T.E.component i)
      (Snc.maximalIdeal_eq_stalkIdeal_component T.E T.isSnc hpη').symm
      (Snc.maximalIdeal_eq_stalkIdeal_component (T.E.comap p) hsnc' hη').symm, heq]
  · have hy : y ∉ ((T.E.component i).comap p).support := by
      rw [Scheme.IdealSheafData.support_comap]
      exact hx
    rw [Snc.finprod_stalk_eq_one_of_notMem (T.E.comap p) hy,
      Snc.finprod_stalk_eq_one_of_notMem T.E hx]
    simp only [Ideal.one_eq_top, Ideal.map_top]

include g in
/-- `N(p^* I) = p^* N(I)`: the nonmonomial part of the pulled-back data along a flat `p` is the
pull-back of the nonmonomial part. `p^* I = p^* M(I) · p^* N(I)` with `p^* M(I)` the monomial part
of `p^* I` and `p^* N(I)` of order `0` at every component's generic point, so it is the nonmonomial
part by uniqueness. -/
theorem nonmonomialPart_comap_of_flat [CharZero k] [CharZero L] :
    nonmonomialPart (T.I.comap p) (T.E.comap p) = (nonmonomialPart T.I T.E).comap p := by
  have hN := Hironaka.BD.noetherianSpace_triple T
  have hLN : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  have hsplit : (T.E.comap p).monomial (fun η => ((T.I.comap p).ord η).toNat) *
      (nonmonomialPart T.I T.E).comap p = T.I.comap p := by
    rw [← monomialPart_eq_monomial, monomialPart_comap_of_flat T p hsnc',
        ← Scheme.IdealSheafData.comap_mul,
      Snc.monomialPart_mul_nonmonomialPart (T.X.left ↘ Spec (.of k)) T.E T.isSnc T.I]
  have hN0 : ∀ i : (T.E.comap p).ι, ∀ η' ∈ ((T.E.comap p).component i).support.genericPoints,
      ((nonmonomialPart T.I T.E).comap p).ord η' = 0 := by
    intro i η' hη'
    have hpη' : p η' ∈ (T.E.component i).support.genericPoints :=
      mem_genericPoints_support_of_flat p _ hη'
    rw [ord_comap_of_flat_of_stalkIdeal_eq p (T.E.component i)
      (Snc.maximalIdeal_eq_stalkIdeal_component T.E T.isSnc hpη').symm
      (Snc.maximalIdeal_eq_stalkIdeal_component (T.E.comap p) hsnc' hη').symm]
    exact Snc.ord_nonmonomialPart_eq_zero (T.X.left ↘ Spec (.of k)) T.E T.isSnc
      T.isNonzeroEverywhere hpη'
  exact (Snc.monomial_eq_monomialPart_of_mul_eq g (T.E.comap p) hsnc' (T.I.comap p) hsplit
    hN0).2.symm

end Data

end Hironaka.BMO
