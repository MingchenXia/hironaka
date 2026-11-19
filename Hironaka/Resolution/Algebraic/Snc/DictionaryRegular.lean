/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.IdealSheaf.Order.Along
public import Hironaka.Scheme.Snc.Defs
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseBlowUp
import Hironaka.Resolution.Algebraic.Snc.DictionaryComponents
import Hironaka.Resolution.Algebraic.Snc.DictionaryGenericPoints
import Hironaka.Scheme.Snc.Coordinates
import Hironaka.Scheme.Snc.ParameterAlgebra
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The dictionary, continued: components of a regular closed subscheme

General facts about a closed subscheme `Z` of a scheme `X` with `IsRegular Z.subscheme`, without a
structure morphism: its stalk ideal at a point of it is prime
(`Hironaka.Sequence.isPrime_stalkIdeal_of_isRegular`); the reduced ideal of the component
through `x` has the subscheme's stalk
(`stalkIdeal_vanishingIdeal_closure_eq_of_isRegular_subscheme`); the `finprod` over the components
of the powers of their reduced stalks is the power of the stalk
at the exponent of the one component through `x`
(`finprod_stalk_eq_of_specializes_of_isRegular_subscheme`); two components through a common point
coincide (`Hironaka.Sequence.eq_of_specializes_of_isRegular`); and, for a simple normal crossing
family
[Kol07, Definition 24] with a regular stalk at a generic point `η` of a component of `E^i`, no
other member passes through `η` (`notMem_support_of_ne_of_isSnc`).

These lemmas serve the monomial part of an ideal along a simple normal crossing divisor and the
combinatorics of its components (`Hironaka/Resolution/Algebraic/Monomial/`,
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/`), whose modules import this one and whose
namespace `Hironaka.Monomial` the declarations carry; their forms for a scheme smooth over a field
are in `Hironaka/Resolution/Algebraic/Snc/ComponentStalks.lean`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme Scheme.IdealSheafData IsLocalRing
  Ideal Hironaka.BMO

namespace Hironaka.Monomial

variable {X : Scheme.{u}}

/-- The reduced ideal of the component through `x` of a member with a regular subscheme has the
member's stalk at `x`: it is a minimal prime over the member's stalk, which is prime
(`Hironaka.Sequence.isPrime_stalkIdeal_of_isRegular`). The general form of
`Snc.stalkIdeal_vanishingIdeal_closure_eq_of_specializes`, whose smooth form is a corollary. -/
theorem stalkIdeal_vanishingIdeal_closure_eq_of_isRegular_subscheme
    {X : Scheme.{u}} {D : X.IdealSheafData} (hD : IsRegular D.subscheme) {η x : X}
    (hη : η ∈ D.support.genericPoints) (hηx : η ⤳ x) :
    (IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal x = D.stalkIdeal x := by
  have hx : x ∈ D.support := hηx.mem_closed D.support.isClosed hη.1
  have hmin := Hironaka.Sequence.stalkIdeal_vanishingIdeal_mem_minimalPrimes D hη hηx
  have := Hironaka.Sequence.isPrime_stalkIdeal_of_isRegular _ hD hx
  rwa [Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff] at hmin

/-- At a point `x` of a member with a regular subscheme, the product over the member's components
of the powers of their reduced stalks is the power of the member's stalk at the exponent of the
one component through `x`: two components through `x` coincide, their reduced stalks both being
the member's. The general form of `Snc.finprod_stalk_eq_of_specializes`. -/
theorem finprod_stalk_eq_of_specializes_of_isRegular_subscheme
    {X : Scheme.{u}} {D : X.IdealSheafData} (hD : IsRegular D.subscheme) {η₀ x : X}
    (hη₀ : η₀ ∈ D.support.genericPoints) (h₀ : η₀ ⤳ x) (a : X → ℕ) :
    ∏ᶠ η ∈ D.support.genericPoints, ((IdealSheafData.vanishingIdeal (Closeds.closure
        {η})).stalkIdeal x) ^ a η =
      (D.stalkIdeal x) ^ a η₀ := by
  rw [finprod_mem_def, finprod_eq_single _ η₀]
  · rw [Set.mulIndicator_of_mem hη₀,
      Hironaka.Monomial.stalkIdeal_vanishingIdeal_closure_eq_of_isRegular_subscheme hD hη₀ h₀]
  · intro η hne
    by_cases hη : η ∈ D.support.genericPoints
    · rw [Set.mulIndicator_of_mem hη]
      have hnot : ¬ η ⤳ x := fun hηx => hne
        (Hironaka.Sequence.eq_of_stalkIdeal_vanishingIdeal_closure_eq hηx h₀
          ((Hironaka.Monomial.stalkIdeal_vanishingIdeal_closure_eq_of_isRegular_subscheme hD hη
            hηx).trans
            (Hironaka.Monomial.stalkIdeal_vanishingIdeal_closure_eq_of_isRegular_subscheme hD hη₀
              h₀).symm))
      rw [stalkIdeal_vanishingIdeal_closure_eq_top_of_not_specializes hnot, Ideal.top_pow]
      exact Ideal.one_eq_top.symm
    · exact Set.mulIndicator_of_notMem hη _

/-- No member other than `E^j` passes through a generic point `η` of a component of `E^j` when the
stalk at `η` is regular: `𝔪_η = (E^j)_η = (z_c)` and another member would have `(z_{c'}) ⊆ (z_c)`
with `c' ≠ c`. The general form of `Snc.notMem_support_of_ne`, whose smooth form is a
corollary. -/
theorem notMem_support_of_ne_of_isSnc {X : Scheme.{u}}
    {E : DivisorFamily X} (hE : E.IsSnc) {i j : E.ι} (hji : j ≠ i) {η : X}
    (hreg : IsRegularLocalRing (X.presheaf.stalk η))
    (hη : η ∈ (E.component i).support.genericPoints) : η ∉ (E.component j).support := by
  intro hj
  have hi : η ∈ (E.component i).support := hη.1
  obtain ⟨n, z, hrs, c, hc, hstalk⟩ := hE.2 η
  have hi' : (E.component i).stalkIdeal η = span {z (c ⟨i, hi⟩)} := hstalk ⟨i, hi⟩
  have hne : c ⟨i, hi⟩ ≠ c ⟨j, hj⟩ := fun h => hji (congrArg Subtype.val (hc h)).symm
  have hmem : z (c ⟨j, hj⟩) ∈ maximalIdeal (X.presheaf.stalk η) :=
    (mem_maximalIdeal_and_notMem_sq_of_span_eq hrs _).1
  have hmax : maximalIdeal (X.presheaf.stalk η) = (E.component i).stalkIdeal η := by
    rw [← stalkIdeal_vanishingIdeal_closure_self η]
    exact Hironaka.Monomial.stalkIdeal_vanishingIdeal_closure_eq_of_isRegular_subscheme (hE.1 i) hη
      (specializes_refl η)
  rw [hmax, hi', Ideal.mem_span_singleton] at hmem
  exact not_dvd_of_ne hrs.1.symm hrs.2 hne hmem

end Hironaka.Monomial
