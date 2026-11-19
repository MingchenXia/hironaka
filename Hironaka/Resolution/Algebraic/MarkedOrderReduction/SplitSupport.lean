/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.MonomialPart
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.SplitMain
import Hironaka.Resolution.Algebraic.Snc.ComponentStalks
import Hironaka.Resolution.Algebraic.Snc.DictionaryComponents
import Hironaka.Resolution.Algebraic.Snc.DictionaryGenericPoints
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUp.ProductCenter
import Hironaka.Scheme.IdealSheaf.Invertible
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Constructible
import Hironaka.Scheme.IdealSheaf.Order.Specialization
import Hironaka.Scheme.IdealSheaf.StalkLe
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Scheme.Snc.Coordinates
import Hironaka.Scheme.Snc.ParameterAlgebra
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The monomial split, V: an invertible ideal sheaf supported on the family is a monomial

The uniqueness clause of [Kol07, Definition–Lemma 110] in the form used for the transforms
(`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Transform.lean`), which is the form of [BM08,
(5.2)] ("`N(I)` is divisible by no such prime ideal"): an invertible ideal sheaf `K` whose support
lies in the support of the normal-crossings family `E` equals its monomial part. Its nonmonomial
part `N` is invertible, supported on `E`, and of order `0` along every component; if `N ≠ 𝒪_X`, a
generic point `ξ` of `supp N` lies on some component `D` of some `E^i` with generic point `η`, `N_ξ
= (g)` with `g` a non-unit, `z_c ∤ g` (else `N_η ≠ 𝒪_{X,η}`), and `𝔪_ξ = √(g)` (the only minimal
prime over `(g)` is the prime of the generic point `ξ` itself, by the minimal-prime dictionary of
`Hironaka/Resolution/Algebraic/Snc/DictionaryGenericPoints.lean`), so `g ∣ z_c^n`; a divisor of a
power of the prime `z_c` not divisible by `z_c` is a unit, a contradiction.

* `Snc.eq_monomialPart_of_isInvertible_of_support_le`: the lemma; its form on a triple is in
  `Hironaka/Resolution/Algebraic/MarkedOrderReduction/SplitTriple.lean`.

The auxiliaries on invertible sheaves and divisor families are in
`Hironaka/Scheme/IdealSheaf/Invertible.lean` and
`Hironaka/Resolution/Algebraic/Snc/DictionaryGenericPoints.lean`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme Scheme.IdealSheafData IsLocalRing
  Ideal

namespace Hironaka.BMO

namespace Snc

open AlgebraicGeometry

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f]
  [NoetherianSpace X] (E : DivisorFamily X) (hE : E.IsSnc)

include f hE

/-- An invertible ideal sheaf whose support lies in the support of `E` is its own monomial part
(the uniqueness clause of [Kol07, Definition–Lemma 110]; [BM08, (5.2)]). -/
theorem eq_monomialPart_of_isInvertible_of_support_le {K : X.IdealSheafData} (hK : K.IsInvertible)
    (hsupp : K.support ≤ E.support) : K = monomialPart K E := by
  have hKne := isNonzeroEverywhere_of_isInvertible hK
  have hsplit := monomialPart_mul_nonmonomialPart f E hE K
  have hNinv : (nonmonomialPart K E).IsInvertible := by
    have h2 : (monomialPart K E * nonmonomialPart K E).IsInvertible := by
      rw [hsplit]
      exact hK
    exact (Scheme.IdealSheafData.IsInvertible.of_mul h2).2
  have hNsupp : (nonmonomialPart K E).support ≤ K.support :=
    IdealSheafData.support_antitone (IdealSheafData.le_colon_self K (monomialPart K E))
  suffices hN : nonmonomialPart K E = ⊤ by
    calc K = monomialPart K E * nonmonomialPart K E := hsplit.symm
      _ = monomialPart K E := by rw [hN, IdealSheafData.mul_top]
  refine Scheme.IdealSheafData.ext_stalkIdeal fun x => ?_
  rw [IdealSheafData.stalkIdeal_top]
  by_contra hne
  have hx : x ∈ (nonmonomialPart K E).support := by
    rw [IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal]
    exact IsLocalRing.le_maximalIdeal hne
  obtain ⟨ξ, hξ, hξx⟩ := Closeds.exists_mem_genericPoints_specializes _ hx
  have hξE : ξ ∈ E.support := hsupp (hNsupp hξ.1)
  obtain ⟨i, hξi⟩ := (DivisorFamily.mem_support_iff_exists E ξ).mp hξE
  obtain ⟨η, hη, hηξ⟩ := exists_genericPoint_specializes _ hξi
  obtain ⟨n, z, hz, c, hc⟩ := exists_stalkIdeal_component_eq_span_of_isSnc E hE hξi
  have hreg := isRegularLocalRing_stalk f ξ
  obtain ⟨g, hg0, hNξ⟩ := hNinv.exists_ne_zero_stalkIdeal_eq_span ξ
  -- (a) the generator is not divisible by the parameter of the component through `ξ`
  have hgz : ¬ z c ∣ g := by
    intro hdvd
    have hle : (nonmonomialPart K E).stalkIdeal ξ ≤
        (IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal ξ := by
      rw [hNξ, stalkIdeal_vanishingIdeal_closure_eq_of_specializes E hE hη hηξ, hc,
        Ideal.span_singleton_le_span_singleton]
      exact hdvd
    have hηN : η ∈ (nonmonomialPart K E).support := by
      rw [IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal,
          IdealSheafData.stalkIdeal_specializes _ hηξ,
        ← stalkIdeal_vanishingIdeal_closure_self η, IdealSheafData.stalkIdeal_specializes
            (IdealSheafData.vanishingIdeal _) hηξ]
      exact Ideal.map_mono hle
    exact
        ((Scheme.IdealSheafData.ord_eq_zero_iff _ η).mp
            (ord_nonmonomialPart_eq_zero f E hE hKne hη)) hηN
  -- (b) the maximal ideal at the generic point `ξ` of `supp N` is the radical of `N_ξ`
  have hrad : maximalIdeal (X.presheaf.stalk ξ) ≤ ((nonmonomialPart K E).stalkIdeal ξ).radical := by
    rw [← Ideal.sInf_minimalPrimes]
    refine le_sInf fun P hP => ?_
    obtain ⟨η'', hη'', hη''ξ, hP'⟩ :=
      Hironaka.Sequence.exists_mem_genericPoints_of_mem_minimalPrimes _ hP
    have hξξ : η'' = ξ := hξ.2 hη''.1 hη''ξ
    subst hξξ
    rw [← hP', stalkIdeal_vanishingIdeal_closure_self]
  have hzm : z c ∈ maximalIdeal (X.presheaf.stalk ξ) :=
    (mem_maximalIdeal_and_notMem_sq_of_span_eq hz.1 c).1
  obtain ⟨N, hN⟩ := Ideal.mem_radical_iff.mp (hrad hzm)
  rw [hNξ, Ideal.mem_span_singleton] at hN
  have hunit : IsUnit g := isUnit_of_dvd_pow_of_not_dvd hz.1.1.symm hz.1.2 hgz hN
  have htop : (nonmonomialPart K E).stalkIdeal ξ = ⊤ := by
    rw [hNξ, Ideal.span_singleton_eq_top]
    exact hunit
  have hξnot : ξ ∉ (nonmonomialPart K E).support := by
    rw [IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal, htop]
    exact fun h => (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp h)
  exact hξnot hξ.1

end Snc

end Hironaka.BMO
