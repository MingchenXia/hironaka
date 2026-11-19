/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.IdealSheaf.Order.Along
public import Hironaka.Scheme.Snc.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseTransforms
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.MeetLocus
import Hironaka.Resolution.Algebraic.Snc.DictionaryComponents
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Hironaka.Scheme.IdealSheaf.Invertible
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Specialization
import Hironaka.Scheme.IdealSheaf.StalkLe
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
/-!
# The dictionary, continued: generic points, reduced ideals of components, and nonvanishing

General facts on a scheme `X` about the reduced ideal `vanishingIdeal (closure {η})` of an
irreducible component with generic point `η`: its stalk is the unit ideal off the closure
(`stalkIdeal_vanishingIdeal_closure_eq_top_of_not_specializes`) and the maximal ideal at `η`
(`stalkIdeal_vanishingIdeal_closure_self`); `η` is a generic point of its support; a point of a
closed set lies on one of its components (`exists_genericPoint_specializes`). Further, the stalk
of a `finprod` of ideal sheaves (`stalkIdeal_finprod_mem`); two facts about a divisor family that
need only the family (`Snc.genericPoints_component_finite`, the one-line corollary of
`Closeds.genericPoints_finite`; `Snc.finprod_stalk_eq_one_of_notMem`, the product over the
components of a member is the unit ideal off the member; `DivisorFamily.mem_support_iff_exists`);
and three generalities on `IsNonzeroEverywhere`, the condition that an ideal sheaf be nonzero on
every irreducible component in the sense of [Kol07, Definition 31]: overideals of a nonvanishing
ideal sheaf are nonvanishing, a nonvanishing ideal sheaf has finite order (Krull's intersection
theorem), an invertible ideal sheaf is nonvanishing.

These lemmas serve the splitting of an ideal into its monomial and nonmonomial parts along a
simple normal crossing divisor [Kol07, Definition–Lemma 110], in the marked order reduction.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme.IdealSheafData Scheme IsLocalRing
  Ideal

namespace Hironaka.BMO

/-! ### Generic points and the reduced ideal of a component -/

/-- The reduced ideal of a component not through `x` has the unit stalk at `x`. -/
theorem stalkIdeal_vanishingIdeal_closure_eq_top_of_not_specializes {X : Scheme.{u}} {η x : X}
    (h : ¬ η ⤳ x) : (vanishingIdeal (Closeds.closure {η})).stalkIdeal x = ⊤ := by
  apply stalkIdeal_eq_top_of_notMem_support
  rw [Hironaka.Sequence.support_vanishingIdeal_eq]
  exact fun hx => h (specializes_iff_mem_closure.mpr hx)

/-- A point of a closed set lies on one of its irreducible components
(`Closeds.exists_mem_genericPoints_specializes`). -/
theorem exists_genericPoint_specializes {X : Scheme.{u}} (Z : Closeds X) {x : X} (hx : x ∈ Z) :
    ∃ η ∈ Z.genericPoints, η ⤳ x :=
  Closeds.exists_mem_genericPoints_specializes _ hx

/-- The stalk of a `finprod` over a finite set of ideal sheaves is the `finprod` of the stalks. -/
theorem stalkIdeal_finprod_mem {X : Scheme.{u}} {s : Set X} (hs : s.Finite)
    (g : X → X.IdealSheafData) (x : X) :
    (∏ᶠ η ∈ s, g η).stalkIdeal x = ∏ᶠ η ∈ s, (g η).stalkIdeal x := by
  rw [finprod_mem_eq_finite_toFinset_prod _ hs, finprod_mem_eq_finite_toFinset_prod _ hs,
    stalkIdeal_finset_prod]

/-- The reduced ideal of the closure of a point has, at that point, the maximal ideal as its stalk
(`stalkIdeal_vanishingIdeal_closure_singleton` and the localization at the prime of the point). -/
theorem stalkIdeal_vanishingIdeal_closure_self {X : Scheme.{u}} (η : X) :
    (vanishingIdeal (Closeds.closure {η})).stalkIdeal η = maximalIdeal (X.presheaf.stalk η) := by
  obtain ⟨U, hηU⟩ := exists_affineOpens_mem η
  have hU : IsAffineOpen U.1 := U.2
  rw [Hironaka.Sequence.stalkIdeal_vanishingIdeal_closure_singleton U hηU hηU]
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨η, hηU⟩ : U.1)
  have := hU.isLocalization_stalk ⟨η, hηU⟩
  exact IsLocalization.AtPrime.map_eq_maximalIdeal (hU.primeIdealOf ⟨η, hηU⟩).asIdeal
    (X.presheaf.stalk η)

/-- The generic point of a component is a generic point of the component's support. -/
theorem isGenericPoint_support_vanishingIdeal_closure {X : Scheme.{u}} (η : X) :
    IsGenericPoint η ((vanishingIdeal (Closeds.closure {η})).support : Set X) := by
  rw [Hironaka.Sequence.support_vanishingIdeal_eq]
  exact isGenericPoint_closure

/-! ### `IsNonzeroEverywhere` -/

/-- A nonvanishing ideal sheaf's overideals are nonvanishing. -/
theorem isNonzeroEverywhere_of_le {X : Scheme.{u}} {I J : X.IdealSheafData} (hle : I ≤ J)
    (hI : IsNonzeroEverywhere I) : IsNonzeroEverywhere J := fun x h =>
  hI x (le_bot_iff.mp ((stalkIdeal_mono hle x).trans (le_of_eq h)))

/-- The order of a nonvanishing ideal sheaf is finite (Krull's intersection theorem: a nonzero
ideal of a Noetherian local ring lies in no `𝔪^r` for `r` large). -/
theorem ord_ne_top_of_isNonzeroEverywhere {X : Scheme.{u}} [IsLocallyNoetherian X]
    {J : X.IdealSheafData} (hJ : IsNonzeroEverywhere J) (x : X) : J.ord x ≠ ⊤ := fun h =>
  hJ x ((IdealSheafData.ord_eq_top_iff J x).mp h)

/-- An invertible ideal sheaf is nonzero at every point. -/
theorem isNonzeroEverywhere_of_isInvertible {X : Scheme.{u}} {K : X.IdealSheafData}
    (hK : K.IsInvertible) : IsNonzeroEverywhere K := fun x h => by
  obtain ⟨g, hg, hKx⟩ := hK.exists_ne_zero_stalkIdeal_eq_span x
  change K.stalkIdeal x = ⊥ at h
  rw [hKx] at h
  exact hg (Ideal.span_singleton_eq_bot.mp h)

/-! ### A divisor family: finitely many components, the inner product off a member -/

namespace Snc

variable {X : Scheme.{u}} (E : DivisorFamily X)

/-- The generic points of a member's support are finitely many on a Noetherian scheme
(`Closeds.genericPoints_finite`). -/
theorem genericPoints_component_finite [NoetherianSpace X] (i : E.ι) :
    ((E.component i).support.genericPoints).Finite :=
  Closeds.genericPoints_finite _

/-- At a point off `E^i` the product over the components of `E^i` of powers of their reduced
stalks is the unit ideal. -/
theorem finprod_stalk_eq_one_of_notMem {i : E.ι} {x : X} (hx : x ∉ (E.component i).support)
    (a : X → ℕ) :
    ∏ᶠ η ∈ (E.component i).support.genericPoints,
        ((vanishingIdeal (Closeds.closure {η})).stalkIdeal x) ^ a η = 1 := by
  refine finprod_mem_of_eqOn_one fun η hη => ?_
  have hnot : ¬ η ⤳ x := fun hηx => hx (hηx.mem_closed (E.component i).support.isClosed hη.1)
  change ((vanishingIdeal (Closeds.closure {η})).stalkIdeal x) ^ a η = 1
  rw [stalkIdeal_vanishingIdeal_closure_eq_top_of_not_specializes hnot, Ideal.top_pow]
  exact Ideal.one_eq_top.symm

end Snc

end Hironaka.BMO

/-- A point lies in the support of a divisor family iff it lies on one of the members. -/
theorem AlgebraicGeometry.Scheme.DivisorFamily.mem_support_iff_exists {X : Scheme.{u}}
    (E : DivisorFamily X) (x : X) : x ∈ E.support ↔ ∃ i, x ∈ (E.component i).support := by
  unfold DivisorFamily.support
  rw [← Finset.sup_univ_eq_iSup, Closeds.mem_finset_sup]
  simp only [Finset.mem_univ, true_and]
