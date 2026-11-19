/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.IdealSheaf.Order.Along
public import Hironaka.Scheme.Snc.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Hironaka.Algebra.Local.CohenIso
import Hironaka.Algebra.Local.Regular
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseBlowUp
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseTransforms
import Hironaka.Resolution.Algebraic.Snc.DictionaryGenericPoints
import Hironaka.Resolution.Algebraic.Snc.DictionaryRegular
import Hironaka.Scheme.BlowUp.Transform.WeakTransform
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Exceptional
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Scheme.Snc.HasSncWith
import Hironaka.Scheme.Snc.ParameterAlgebra
import Hironaka.Scheme.Snc.TrivialTotalTransform
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The components of an snc family on a smooth scheme, at a point and at a generic point

An snc family `E` on a scheme `X` smooth over a field `k` (regular stalks): Kollár's snc coordinates
at a point of `E^i` (`exists_stalkIdeal_component_eq_span_of_isSnc`), the stalk of `E^i` at a point
of `E^i` is prime, the reduced ideal of the component through `x` has the member's stalk
(`stalkIdeal_vanishingIdeal_closure_eq_of_specializes`), the components of a member are pairwise
disjoint (`genericPoint_eq_of_specializes`), the inner product of a monomial's components at a point
of `E^i` (`finprod_stalk_eq_of_specializes`); at the generic point `η` of a component:
`𝔪_η = (E^i)_η` (`maximalIdeal_eq_stalkIdeal_component`), no other member passes through `η`
(`notMem_support_of_ne`), the component's subscheme is integral
(`isIntegral_componentIdeal_subscheme`), the membership half of [Kol07, Definition–Lemma 110]
(`stalkIdeal_le_pow_of_specializes`) and, in characteristic zero, the orders
`ord ((E^i)_η^a · J) = a + ord J` and `ord ((E^i)_η^a) = a`. These are the facts about the
components of the boundary that the splitting of an ideal into its monomial and non-monomial parts
(`Hironaka.MarkedOrderReduction`, Step 3 of the proof of [Kol07, Theorem 107]) uses; the forms
without a structure morphism are in `Hironaka.Resolution.Algebraic.Snc.DictionaryRegular`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme Scheme.IdealSheafData IsLocalRing
  Ideal

namespace Hironaka.BMO

namespace Snc

open AlgebraicGeometry

/-! An snc family `E` on a scheme `X` smooth over `k` (regular stalks); the statements on triples in
`Hironaka.MarkedOrderReduction` are the instances of these at `T.X.left ↘ Spec k`, `T.E`, `T.I`. -/

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f]
  (E : DivisorFamily X) (hE : E.IsSnc)

/-! ### B. The components of a member at a point -/

include hE in
/-- Kollár's snc coordinates at a point of `E^i`: `E^i_x = (z_c)` for a regular system of parameters
`z` of `𝒪_{X,x}` [Kol07, Definition 24 (2)]. -/
theorem exists_stalkIdeal_component_eq_span_of_isSnc {i : E.ι} {x : X}
    (hx : x ∈ (E.component i).support) :
    ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x), E.IsSncAt x z ∧
      ∃ c : Fin n, (E.component i).stalkIdeal x = Ideal.span {z c} := by
  obtain ⟨n, z, hz⟩ := hE.2 x
  obtain ⟨-, c, -, hc⟩ := id hz
  exact ⟨n, z, hz, c ⟨i, hx⟩, hc ⟨i, hx⟩⟩

include f hE in
/-- The stalk of `E^i` at a point of `E^i` is prime (one member of a regular system of parameters of
the regular local ring `𝒪_{X,x}`). -/
theorem isPrime_stalkIdeal_component_of_isSnc {i : E.ι} {x : X} (hx : x ∈ (E.component i).support) :
    ((E.component i).stalkIdeal x).IsPrime := by
  obtain ⟨n, z, hz, c, hc⟩ := exists_stalkIdeal_component_eq_span_of_isSnc E hE hx
  have := isRegularLocalRing_stalk f x
  rw [hc]
  exact isPrime_span_singleton_of_parameters hz.1.1.symm hz.1.2 c

include hE in
/-- The reduced ideal of an irreducible component of `E^i` through `x` has, at `x`, the stalk of
`E^i` itself — it is a minimal prime over the prime `(E^i)_x = (z_c)`
(`stalkIdeal_vanishingIdeal_mem_minimalPrimes`), hence that prime. -/
theorem stalkIdeal_vanishingIdeal_closure_eq_of_specializes {i : E.ι} {η x : X}
    (hη : η ∈ (E.component i).support.genericPoints) (hηx : η ⤳ x) :
    (IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal x =
        (E.component i).stalkIdeal x := by
  exact Hironaka.Monomial.stalkIdeal_vanishingIdeal_closure_eq_of_isRegular_subscheme (hE.1 i) hη
    hηx

include hE in
/-- The irreducible components of a member are pairwise disjoint ([Kol07, Definition 24 (1)], `E^i`
smooth): two components through `x` coincide, their reduced ideals having the same (prime) stalk at
`x` (`eq_of_stalkIdeal_vanishingIdeal_closure_eq`); the corollary of
`Hironaka.Sequence.eq_of_specializes_of_isRegular`. -/
theorem genericPoint_eq_of_specializes {i : E.ι} {η η' x : X}
    (hη : η ∈ (E.component i).support.genericPoints)
    (hη' : η' ∈ (E.component i).support.genericPoints) (hηx : η ⤳ x) (hη'x : η' ⤳ x) :
    η = η' := by
  exact Hironaka.Sequence.eq_of_specializes_of_isRegular _ (hE.1 i) hη hη' hηx hη'x

include hE in
/-- At a point `x` of `E^i` the inner product of the monomial over the components of `E^i` is the
power of `(E^i)_x` at the exponent of the one component through `x`. -/
theorem finprod_stalk_eq_of_specializes {i : E.ι} {η₀ x : X}
    (hη₀ : η₀ ∈ (E.component i).support.genericPoints) (h₀ : η₀ ⤳ x) (a : X → ℕ) :
    ∏ᶠ η ∈ (E.component i).support.genericPoints,
        ((IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal x) ^ a η =
      ((E.component i).stalkIdeal x) ^ a η₀ := by
  exact Hironaka.Monomial.finprod_stalk_eq_of_specializes_of_isRegular_subscheme (hE.1 i) hη₀ h₀ a

/-! ### F. The component at its generic point -/

include hE

/-- At the generic point `η` of a component of `E^i`, the maximal ideal of `𝒪_{X,η}` is the stalk of
`E^i` — the component is a divisor and `𝒪_{X,η}` its local ring. -/
theorem maximalIdeal_eq_stalkIdeal_component {i : E.ι} {η : X}
    (hη : η ∈ (E.component i).support.genericPoints) :
    maximalIdeal (X.presheaf.stalk η) = (E.component i).stalkIdeal η := by
  rw [← stalkIdeal_vanishingIdeal_closure_self η]
  exact stalkIdeal_vanishingIdeal_closure_eq_of_specializes E hE hη (specializes_refl η)

include f in
/-- No member other than `E^i` passes through the generic point of a component of `E^i`
[Kol07, Definition 24] — its parameter would generate the maximal ideal `(z_c)` and be divisible by
`z_c`, against the independence of the parameters. -/
theorem notMem_support_of_ne {i j : E.ι} (hji : j ≠ i) {η : X}
    (hη : η ∈ (E.component i).support.genericPoints) : η ∉ (E.component j).support :=
  Hironaka.Monomial.notMem_support_of_ne_of_isSnc hE hji
    (isRegularLocalRing_stalk f η) hη

include f in
/-- The subscheme of a component's reduced ideal is integral — irreducible (the support is the
closure of the generic point) and with regular stalks (at a point `w` of the component the stalk is
`𝒪_{X,w} / (z_c)`, a regular local ring). -/
theorem isIntegral_componentIdeal_subscheme {i : E.ι} {η : X}
    (hη : η ∈ (E.component i).support.genericPoints) :
    IsIntegral (IdealSheafData.vanishingIdeal (Closeds.closure {η})).subscheme := by
  have hirr := irreducibleSpace_subscheme_of_isGenericPoint _
    (isGenericPoint_support_vanishingIdeal_closure (X := X) η)
  refine IdealSheafData.isIntegral_subscheme_of_isRegularLocalRing_stalk _ ?_
  refine (isRegular_subscheme_of_isRegularLocalRing_quotient _ fun w hw => ?_).isRegularAt
  rw [Hironaka.Sequence.support_vanishingIdeal_eq] at hw
  have hηw : η ⤳ w := specializes_iff_mem_closure.mpr hw
  have hwi : w ∈ (E.component i).support := hηw.mem_closed (E.component i).support.isClosed hη.1
  rw [stalkIdeal_vanishingIdeal_closure_eq_of_specializes E hE hη hηw]
  obtain ⟨n, z, hz, c, hc⟩ := exists_stalkIdeal_component_eq_span_of_isSnc E hE hwi
  have := isRegularLocalRing_stalk f w
  rw [hc]
  have hq := isRegularLocalRing_quotient_span_image_finset hz.1.1.symm hz.1.2 {c}
  rwa [Finset.coe_singleton, Set.image_singleton] at hq

include f in
/-- The membership half of [Kol07, Definition–Lemma 110], with the order along a subvariety of
[Kol07, Definition 47]: at a point `x` of a component `D` of `E^i` with generic point `η`,
`I_x ⊆ (E^i)_x^{ord_η I}` — the order along the prime `(E^i)_x = (z_c)` is `ord_η I`
(`ordAlong_stalkIdeal_eq_ord_stalkIdeal` on the integral component subscheme) and membership follows
for the prime element `z_c`. -/
theorem stalkIdeal_le_pow_of_specializes (I : X.IdealSheafData) {i : E.ι} {η x : X}
    (hη : η ∈ (E.component i).support.genericPoints) (hηx : η ⤳ x) :
    I.stalkIdeal x ≤ ((E.component i).stalkIdeal x) ^ (I.ord η).toNat := by
  have hx : x ∈ (E.component i).support := hηx.mem_closed (E.component i).support.isClosed hη.1
  have hxD : x ∈ (IdealSheafData.vanishingIdeal (Closeds.closure {η})).support := by
    rw [Hironaka.Sequence.support_vanishingIdeal_eq]
    exact specializes_iff_mem_closure.mp hηx
  have hint := isIntegral_componentIdeal_subscheme f E hE hη
  have hP : ((IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal x).IsPrime := by
    rw [stalkIdeal_vanishingIdeal_closure_eq_of_specializes E hE hη hηx]
    exact isPrime_stalkIdeal_component_of_isSnc f E hE hx
  have hord := ordAlong_stalkIdeal_eq_ord_stalkIdeal
    (IdealSheafData.vanishingIdeal (Closeds.closure {η})) I
        (isGenericPoint_support_vanishingIdeal_closure η) hxD
  obtain ⟨n, z, hz, c, hc⟩ := exists_stalkIdeal_component_eq_span_of_isSnc E hE hx
  have := isRegularLocalRing_stalk f x
  have hPeq : (IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal x = Ideal.span
      {z c} := by
    rw [stalkIdeal_vanishingIdeal_closure_eq_of_specializes E hE hη hηx, hc]
  rw [← stalkIdeal_vanishingIdeal_closure_eq_of_specializes E hE hη hηx]
  refine le_pow_of_le_ordAlong_of_eq_span (prime_of_parameters hz.1.1.symm hz.1.2 c) hPeq _ _ ?_
  rw [hord, ← IdealSheafData.ord_eq_ord_stalkIdeal]
  exact ENat.natCast_toNat_le_self _

/-! ### G. Orders at the generic point -/

variable [CharZero k]

include f in
/-- At the generic point `η` of a component of `E^i`, `ord ((E^i)_η^a · J) = a + ord J`
([Kol07, Definition 59, (3)]; the multiplicativity of the order on a regular local ring containing
`ℚ`). -/
theorem ord_stalkIdeal_component_pow_mul {i : E.ι} {η : X}
    (hη : η ∈ (E.component i).support.genericPoints) (a : ℕ) (J : Ideal (X.presheaf.stalk η)) :
    ord (((E.component i).stalkIdeal η) ^ a * J) =
      (a : ℕ∞) + ord J := by
  have := isRegularLocalRing_stalk f η
  let _ := f.stalkAlgebraRat η
  have hmul := ordElem_mul_of_algebraRat (X.presheaf.stalk η)
  obtain ⟨n, z, hz, c, hc⟩ := exists_stalkIdeal_component_eq_span_of_isSnc E hE hη.1
  rw [hc, Ideal.span_singleton_pow, ord_span_singleton_mul_of_ordElem_mul hmul,
    ordElem_pow_of_ordElem_mul hmul, ordElem_parameter hz.1 c, mul_one]

include f in
/-- `ord ((E^i)_η^a) = a` at the generic point of a component of `E^i`. -/
theorem ord_stalkIdeal_component_pow {i : E.ι} {η : X}
    (hη : η ∈ (E.component i).support.genericPoints) (a : ℕ) :
    ord (((E.component i).stalkIdeal η) ^ a) = a := by
  have h := ord_stalkIdeal_component_pow_mul f E hE hη a ⊤
  rwa [Ideal.mul_top, IsLocalRing.ord_top, add_zero] at h

end Snc

end Hironaka.BMO
