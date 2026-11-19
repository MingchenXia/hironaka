/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Snc.SmoothDivisor
public import Hironaka.Scheme.Snc.Defs
import Hironaka.Scheme.Snc.TotalTransformSnc
import Mathlib.Data.Nat.Choose.Multinomial
/-!
# The total-transform theorem on the predicates

The total transform of a simple normal crossing divisor under the blow-up along a centre having
simple normal crossings with it is again snc ([Hau14, Proposition 5.3]; [Kol07, Definition 25]).
This module states the theorem's ingredients on the predicates `IsSnc`, `HasSncWith`, `IsSncAt`
and on `totalTransform`, `strictTransform`, `exceptionalDivisor`, proved from the modules of
`Hironaka.Snc`, which are stated over families of ideal sheaves with the snc data as explicit
hypotheses (`totalTransformFamily Z E` for the total transform). The passage is definitional:
`(E.totalTransform Z).component (toLex k)` is `Sum.elim (strictTransform Z ∘ E.component) (fun _ =>
exceptionalDivisor X Z) k`, `strictTransform Z D` is `strictTransformAlong (blowUp.π Z) (Z.comap
(blowUp.π Z)) D` and `IsRegularSystemOfParameters z` is `span (range z) = 𝔪 ∧ n = dim`;
`hasSncWith_data` and `isSnc_data` unfold the two predicates.
`Hironaka.Scheme.Snc.TotalTransformSmoothBlowUp` assembles the theorem
`totalTransform_isSnc` from the three statements `exists_isSncAt_totalTransform_of_mem_support`,
`exists_isSncAt_totalTransform_of_notMem_support` and `isSmoothDivisor_totalTransform_component`;
the section on strict transforms restates the pointwise description of the strict transforms of
`Hironaka.Scheme.Snc.TotalTransformSnc` on the predicates.

The mathematics, module by module ([Hau14, Proposition 5.3; Proposition 5.4; Definition 6.2];
[Hau03, Appendix C]; [Kol07, Definition 24; Definition 25; Definition 60]):

* `Hironaka.Scheme.Snc.TotalTransformOffCentre`: over `X ∖ Z` the blow-up is an isomorphism, so
  `π^*` is an isomorphism of stalks, the strict transforms have stalks `π^*(D_x)`, and Kollár's data
  at `x = π(x')` transport to `x'` with the entry `F` absent.
* `Hironaka.Scheme.Snc.EtaleParameters`: for étale coordinates `y` of a `k`-algebra `A` and any
  prime `q`, `A_q` is regular and the coordinates vanishing at `q` extend to a regular system of
  parameters — the coordinate derivations detect independence modulo `𝔪_q²`.
* `Hironaka.Scheme.Snc.SpreadSnc`: the snc data at a closed point `x₀ ∈ Z` spread to a chart of
  étale coordinates adapted to `Z` on which the components through `x₀` are coordinate hyperplanes
  and the others are absent.
* `Hironaka.Scheme.Snc.ChartStalk`, `Hironaka.Scheme.Snc.ChartSncData`: the stalk at any point of
  `B_{Z∩U} U` is a localization of a chart ring `Γ(U)[J/x_j]`, in which the exceptional ideal is
  `(y_j)` and the total transform of a component is `(y_c y_j)`, `(y_j)`, `(y_c)` or `(1)`; with the
  étale parameters this is the shape `TotalTransformData`.
* `Hironaka.Scheme.Snc.TotalTransformData`: the shape, its transport along ring isomorphisms and the
  saturations `(y_c y_j) : y_j^∞ = (y_c)`, `(y_c) : y_j^∞ = (y_c)`, `(y_j) : y_j^∞ = (1)` that
  compute the strict transforms.
* `Hironaka.Scheme.Snc.TotalTransformOnCentre`: every point `x'` of `F` is reached — a closed point
  of the closure of `π(x')` is on `Z` (Jacobson), an affine neighbourhood of constant relative
  dimension, the chart, the point `x'` over the chart — and the shape transports back to `𝒪_{B,x'}`;
  a total transform inside the exceptional ideal comes from a component containing `Z`.
* `Hironaka.Scheme.Snc.TotalTransformSnc`: Kollár's (1)–(3) at the points of `F`, the strict
  transforms of transversal components and of components containing the centre, regular stalks of
  `B_Z X`, and every member of the total transform a smooth divisor.
-/

public section

universe u

open AlgebraicGeometry CategoryTheory IsLocalRing Ideal Scheme.IdealSheafData
  Scheme DivisorFamily
open AlgebraicGeometry

namespace AlgebraicGeometry


variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The data of [Kol07, Definition 24 (4)] behind `E.HasSncWith Z`, unfolded: at every point of `Z`
a regular system of parameters, the injective assignment of coordinates to the components through
the point, and the index set cutting out `Z`. -/
theorem hasSncWith_data (E : DivisorFamily X) (Z : X.IdealSheafData) (hZ : E.HasSncWith Z) :
    ∀ x ∈ Z.support, ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x),
      (span (Set.range z) = maximalIdeal (X.presheaf.stalk x) ∧
        (n : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x)) ∧
      (∃ c : {i : E.ι // x ∈ (E.component i).support} → Fin n, Function.Injective c ∧
        ∀ i, (E.component i.1).stalkIdeal x = span {z (c i)}) ∧
      ∃ s : Finset (Fin n), Z.stalkIdeal x = span (z '' ↑s) := by
  intro x hx
  obtain ⟨n, z, ⟨hrs, c, hcinj, hc⟩, s, hs⟩ := hZ x hx
  exact ⟨n, z, hrs, ⟨c, hcinj, hc⟩, s, hs⟩

/-- The data of [Kol07, Definition 24 (1)–(3)] behind `E.IsSnc` at every point, unfolded. -/
theorem isSnc_data (E : DivisorFamily X) (hE : E.IsSnc) :
    ∀ x : X, ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x),
      (span (Set.range z) = maximalIdeal (X.presheaf.stalk x) ∧
        (n : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x)) ∧
      ∃ c : {i : E.ι // x ∈ (E.component i).support} → Fin n, Function.Injective c ∧
        ∀ i, (E.component i.1).stalkIdeal x = span {z (c i)} := by
  intro x
  obtain ⟨n, z, hrs, c, hcinj, hc⟩ := hE.2 x
  exact ⟨n, z, hrs, c, hcinj, hc⟩

/-- [Hau14, Proposition 5.3; Proposition 5.4] ([Hau03, Appendix C]) at every point of the
exceptional divisor, not only the closed ones: there are local coordinates for which the total
transform satisfies Kollár's conditions (1)–(3). -/
theorem exists_isSncAt_totalTransform_of_mem_support
    [PerfectField k] (f : X ⟶ Spec (.of k))
    [Smooth f] (E : DivisorFamily X) (Z : X.IdealSheafData) (_hE : E.IsSnc) (hZ : E.HasSncWith Z)
    (x' : Z.blowUp) (hx' : x' ∈ Z.exceptionalDivisor.support) :
    ∃ (n : ℕ) (z : Fin n → Z.blowUp.presheaf.stalk x'),
      (E.totalTransform Z).IsSncAt x' z := by
  obtain ⟨-, m, z, hz, c', hc'inj, hc'⟩ :=
    exists_snc_data_totalTransform_of_mem_support f E.component Z (hasSncWith_data E Z hZ) x' hx'
  exact ⟨m, z, hz, c', hc'inj, hc'⟩

/-- [Kol07, Definition 25], the proof of [Hau14, Proposition 5.3]: at every point `x'` off the
exceptional divisor the blow-up is a local isomorphism and the total transform restricts to `E`, so
there are local coordinates for which it satisfies Kollár's (1)–(3). -/
theorem exists_isSncAt_totalTransform_of_notMem_support
    (_f : X ⟶ Spec (.of k))
    (E : DivisorFamily X) (Z : X.IdealSheafData) (hE : E.IsSnc) (_hZ : E.HasSncWith Z)
    (x' : Z.blowUp) (hx' : x' ∉ Z.exceptionalDivisor.support) :
    ∃ (n : ℕ) (z : Fin n → Z.blowUp.presheaf.stalk x'),
      (E.totalTransform Z).IsSncAt x' z := by
  obtain ⟨n, z, ⟨hspan, hdim⟩, c, hcinj, hc⟩ := hE.2 (Z.blowUpπ x')
  have h := exists_snc_data_totalTransform_of_notMem_support Z E.component hx' hspan.symm hdim c
    hcinj hc
  exact ⟨n, fun i => Z.blowUpπ.stalkMap x' (z i), ⟨h.1.1.symm, h.1.2⟩, h.2⟩

/-- [Hau14, Proposition 5.3]: every member of the total transform — the strict transforms of the
components and the exceptional divisor — is a smooth divisor of `B_Z X` (regular, and principal at
every point with a generator in `𝔪 ∖ 𝔪²`). -/
theorem isSmoothDivisor_totalTransform_component
    [PerfectField k] (f : X ⟶ Spec (.of k))
    [Smooth f] (E : DivisorFamily X) (Z : X.IdealSheafData) (hE : E.IsSnc) (hZ : E.HasSncWith Z)
    (i : (E.totalTransform Z).ι) :
    IsSmoothDivisor ((E.totalTransform Z).component i) :=
  isSmoothDivisor_totalTransformFamily f E.component Z (isSnc_data E hE) (hasSncWith_data E Z hZ)
    (ofLex i)

section StrictTransforms

/-- On the predicates: at `x' ∈ F` over `x` with snc coordinates `z` at `x` and a component
`E^i = (z_c = 0)` transversal to `Z` (`c ∉ s`), the strict transform has stalk `(π^* z_c)` —
`stalkIdeal_strictTransformAlong_of_notMem` of `Hironaka.Scheme.Snc.TotalTransformSnc`. -/
theorem stalkIdeal_strictTransform_of_notMem [PerfectField k] (f : X ⟶ Spec (.of k)) [Smooth f]
    (E : DivisorFamily X) (Z : X.IdealSheafData) (_hE : E.IsSnc) (hZ : E.HasSncWith Z) (i : E.ι)
    (x' : Z.blowUp) (hx' : x' ∈ Z.exceptionalDivisor.support) {n : ℕ}
    {z : Fin n → X.presheaf.stalk (Z.blowUpπ x')} (hz : E.IsSncAt
        (Z.blowUpπ x') z)
    {s : Finset (Fin n)} (hs : Z.stalkIdeal (Z.blowUpπ x') = Ideal.span (z '' ↑s))
        {c : Fin n}
    (hc : (E.component i).stalkIdeal (Z.blowUpπ x') = Ideal.span {z c}) (hcs : c ∉ s) :
    ((E.component i).strictTransform Z).stalkIdeal x' =
      Ideal.span {Z.blowUpπ.stalkMap x' (z c)} :=
  stalkIdeal_strictTransformAlong_of_notMem f E.component Z (hasSncWith_data E Z hZ) i x' hx' hz.1
    hs hc hcs

/-- On the predicates: the strict transform of a component transversal to `Z` contains the whole
fibre over `Z ∩ E^i` — `mem_support_strictTransformAlong_iff_of_notMem` of
`Hironaka.Scheme.Snc.TotalTransformSnc`. -/
theorem mem_support_strictTransform_iff_of_notMem [PerfectField k] (f : X ⟶ Spec (.of k))
    [Smooth f] (E : DivisorFamily X) (Z : X.IdealSheafData) (_hE : E.IsSnc) (hZ : E.HasSncWith Z)
    (i : E.ι) (x' : Z.blowUp) (hx' : x' ∈ Z.exceptionalDivisor.support) {n : ℕ}
    {z : Fin n → X.presheaf.stalk (Z.blowUpπ x')} (hz : E.IsSncAt
        (Z.blowUpπ x') z)
    {s : Finset (Fin n)} (hs : Z.stalkIdeal (Z.blowUpπ x') = Ideal.span (z '' ↑s))
        {c : Fin n}
    (hc : (E.component i).stalkIdeal (Z.blowUpπ x') = Ideal.span {z c}) (hcs : c ∉ s) :
    x' ∈ ((E.component i).strictTransform Z).support ↔
      Z.blowUpπ x' ∈ (E.component i).support :=
  mem_support_strictTransformAlong_iff_of_notMem f E.component Z (hasSncWith_data E Z hZ) i x' hx'
    hz.1 hs hc hcs

/-- On the predicates: for a component `E^i = (z_c = 0)` containing `Z` near `x` (`c ∈ s`) and a
generator `e` of the exceptional ideal at `x'`, `π^* z_c = u e` and the strict transform has stalk
`(u)` ([Hau14, Proposition 5.4 (7)]) — `exists_stalkIdeal_strictTransformAlong_eq_span_of_mem` of
`Hironaka.Scheme.Snc.TotalTransformSnc`. -/
theorem exists_stalkIdeal_strictTransform_eq_span_of_mem [PerfectField k] (f : X ⟶ Spec (.of k))
    [Smooth f] (E : DivisorFamily X) (Z : X.IdealSheafData) (_hE : E.IsSnc) (hZ : E.HasSncWith Z)
    (i : E.ι) (x' : Z.blowUp) (hx' : x' ∈ Z.exceptionalDivisor.support) {n : ℕ}
    {z : Fin n → X.presheaf.stalk (Z.blowUpπ x')} (hz : E.IsSncAt
        (Z.blowUpπ x') z)
    {s : Finset (Fin n)} (hs : Z.stalkIdeal (Z.blowUpπ x') = Ideal.span (z '' ↑s))
        {c : Fin n}
    (hc : (E.component i).stalkIdeal (Z.blowUpπ x') = Ideal.span {z c}) (hcs : c ∈ s)
    {e : Z.blowUp.presheaf.stalk x'}
    (he : Z.exceptionalDivisor.stalkIdeal x' = Ideal.span {e}) :
    ∃ u : Z.blowUp.presheaf.stalk x', Z.blowUpπ.stalkMap x'
        (z c) = u * e ∧
      ((E.component i).strictTransform Z).stalkIdeal x' = Ideal.span {u} :=
  exists_stalkIdeal_strictTransformAlong_eq_span_of_mem f E.component Z (hasSncWith_data E Z hZ) i
    x' hx' hz.1 hs hc hcs he

/-- On the predicates: where `π^* z_c` generates the exceptional ideal, the strict transform of
`E^i = (z_c = 0)` misses `x'` ([Hau14, Definition 6.2]) —
`notMem_support_strictTransformAlong_of_stalkIdeal_eq` of `Hironaka.Scheme.Snc.TotalTransformSnc`.
-/
theorem notMem_support_strictTransform_of_stalkIdeal_eq (_f : X ⟶ Spec (.of k))
    (E : DivisorFamily X) (Z : X.IdealSheafData) (_hE : E.IsSnc)
    (_hZ : E.HasSncWith Z) (i : E.ι) (x' : Z.blowUp)
    (_hx' : x' ∈ Z.exceptionalDivisor.support) {n : ℕ}
    {z : Fin n → X.presheaf.stalk (Z.blowUpπ x')} (_hz : E.IsSncAt
        (Z.blowUpπ x') z)
    {s : Finset (Fin n)} (_hs : Z.stalkIdeal (Z.blowUpπ x') = Ideal.span (z '' ↑s))
        {c : Fin n}
    (hc : (E.component i).stalkIdeal (Z.blowUpπ x') = Ideal.span {z c}) (_hcs : c ∈ s)
    (he : Z.exceptionalDivisor.stalkIdeal x' =
      Ideal.span {Z.blowUpπ.stalkMap x' (z c)}) :
    x' ∉ ((E.component i).strictTransform Z).support :=
  notMem_support_strictTransformAlong_of_stalkIdeal_eq Z (E.component i) x' hc he

end StrictTransforms

end AlgebraicGeometry

