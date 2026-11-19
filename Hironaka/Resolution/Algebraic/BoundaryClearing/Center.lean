/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.BoundaryClearing.Data
import Hironaka.Algebra.Local.Regular
import Hironaka.Resolution.Algebraic.BoundaryClearing.Basic
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.Center
import Hironaka.Resolution.Algebraic.Snc.DictionaryComponents
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.IdealSheaf.Invertible
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Scheme.Snc.Coordinates
import Hironaka.Scheme.Snc.DictionaryOrder
import Hironaka.Scheme.Snc.TrivialTotalTransform
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The first center `Z_{-1}` is a trivial smooth blow-up of order `m`

In the proof of [Kol07, Lemma 102], `Z_{-1}` is the union of the irreducible components of `E^j`
contained in `cosupp(I, m)`, and `π_{-1} : X_0 → X` its blow-up, an isomorphism. This module shows
that the blow-up is a smooth blow-up of order `m` of `(X, I, E)` in the sense of
[Kol07, Definition 65]: its center is smooth, has simple normal crossings with `E`, and
`ord_{Z_{-1}} I = m`.

**The stalks of `Z_{-1}`.** `E^j` is a component of the snc family `E` of a triple, so it is
reduced (its subscheme is regular, hence its stalks are domains) and equals the vanishing ideal of
its support; since `Z_{-1} ⊆ E^j` as closed sets, `E^j ⊆ Z_{-1}` as ideal sheaves
(`component_le_Zminus1`). At a point `x` of `Z_{-1}` some selected generic point `η` of `E^j`
specializes to `x`; the stalk of `Z_{-1}` at `x` lies in that of the reduced component
`closure {η}`, which is a minimal prime of `E^j_x` (`stalkIdeal_vanishingIdeal_mem_minimalPrimes`,
`Hironaka/Resolution/Algebraic/Snc/DictionaryComponents.lean`); and `E^j_x = (z_c)` for one member
of a regular system of parameters (Kollár's snc coordinates, [Kol07, Definition 24]; `IsSncAt`), a
prime ideal. A prime is its own only minimal prime, so `(Z_{-1})_x ⊆ E^j_x`, and with the reverse
inclusion `(Z_{-1})_x = E^j_x = (z_c)` (`stalkIdeal_Zminus1_eq`): near a point of `Z_{-1}` the two
subschemes coincide, the components of the regular `E^j` being pairwise disjoint.

**Consequences.** `Z_{-1}` has simple normal crossings with `E` (the same coordinates, `s = {c}`;
`hasSncWith_Zminus1`), hence is smooth over `k` (`smooth_of_hasSncWith`,
`Hironaka/Resolution/Algebraic/Kol07/Thm35/Disjoin/Center.lean`, `k` perfect); its stalks are the
unit ideal off its support and `(z_c)` on it, `z_c ∈ 𝔪_x ∖ 𝔪_x²` a nonzerodivisor of the regular
local ring `𝒪_{X,x}` (a domain), so `Z_{-1}` is a Cartier divisor (`isInvertible_Zminus1`, by the
stalkwise criterion of `Hironaka/Scheme/IdealSheaf/Invertible.lean`) and `π_{-1}` is an
isomorphism (`isIso_blowUpπ_Zminus1`; `blowUp.isIso_π_of_isInvertible`,
`Hironaka/Scheme/BlowUp/Glue/Trivial.lean`; [Kol07, Warning 20]).
The generic points of `Z_{-1}` are exactly the selected generic points of `E^j`
(`mem_genericPoints_support_Zminus1_iff`), along which `ord I ≥ m` by selection and
`≤ max-ord I = m`: `ord_{Z_{-1}} I = m` (`ordAlongEq_Zminus1`). Together: Definition 65 for the
center (`isOrderBlowUp_Zminus1`) and [Kol07, Definition 66] for the one-step sequence `π_{-1}`
(`isOrderSeq_piMinusOne`).

Used by `Transform.lean` and `Restriction.lean`, and outside this directory by
`Hironaka/Resolution/Algebraic/Wlo05/EmbeddedCP3Raw.lean`; imported (for
`BD.Zminus1`) by `Hironaka/Resolution/Algebraic/MarkedOrderReduction/Split.lean` and
`Hironaka/Resolution/Algebraic/Wlo05/EmbeddedNilCoreTools.lean`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka
  Scheme.BlowUpSequence Scheme.IdealSheafData IsLocalRing

namespace Hironaka.BD

section NoCharZero

variable {k : Type u} [Field k] (T : Triple k) (m : ℕ) (j : T.E.ι)

/-! ### `E^j` is reduced, hence contained in `Z_{-1}` as an ideal sheaf -/

/-- The subscheme of a component of the snc family of a triple is reduced: its stalks are regular
local rings (each `E^i` is smooth, [Kol07, Definition 24]), hence domains. -/
theorem isReduced_component : IsReduced (T.E.component j).subscheme := by
  have hreg : IsRegular (T.E.component j).subscheme := T.isSnc.1 j
  have : ∀ w, _root_.IsReduced ((T.E.component j).subscheme.presheaf.stalk w) := fun w =>
    haveI : IsRegularLocalRing ((T.E.component j).subscheme.presheaf.stalk w) := hreg.isRegularAt w
    haveI := isDomain_of_isRegularLocalRing
      ((T.E.component j).subscheme.presheaf.stalk w)
    inferInstance
  exact isReduced_of_isReduced_stalk _

/-- The closed set of `Z_{-1}` as a `Closeds`: the `⨆` of the closures of the selected generic
points (the support of a vanishing ideal sheaf is the closed set). -/
theorem support_Zminus1_eq :
    (Zminus1 T.I m (T.E.component j)).support =
      ⨆ η : {η : T.X.left // η ∈ (T.E.component j).support.genericPoints ∧ (m : ℕ∞) ≤ T.I.ord η},
        Closeds.closure {(η : T.X.left)} :=
  SetLike.coe_injective (Scheme.IdealSheafData.coe_support_vanishingIdeal _)

/-- `E^j ⊆ Z_{-1}` as ideal sheaves: `E^j` is reduced and `Z_{-1} ⊆ E^j` as closed sets. -/
theorem component_le_Zminus1 : T.E.component j ≤ Zminus1 T.I m (T.E.component j) := by
  have hred := isReduced_component T j
  calc T.E.component j = (T.E.component j).radical :=
        (radical_eq_self_of_isReduced_subscheme _).symm
    _ = Scheme.IdealSheafData.vanishingIdeal (T.E.component j).support :=
        Scheme.IdealSheafData.vanishingIdeal_support.symm
    _ ≤ Scheme.IdealSheafData.vanishingIdeal (Zminus1 T.I m (T.E.component j)).support :=
        Scheme.IdealSheafData.vanishingIdeal_antimono (support_Zminus1_le_support T.I m
            (T.E.component j))
    _ = Zminus1 T.I m (T.E.component j) := by rw [support_Zminus1_eq]; rfl

/-! ### The stalks of `Z_{-1}` -/

/-- Kollár's snc coordinates at a point of `E^j`: `E^j_x = (z_c)` for a regular system of
parameters `z` of `𝒪_{X,x}` ([Kol07, Definition 24, (2)]). -/
theorem exists_stalkIdeal_component_eq_span {x : T.X.left} (hx : x ∈ (T.E.component j).support) :
    ∃ (n : ℕ) (z : Fin n → T.X.left.presheaf.stalk x), T.E.IsSncAt x z ∧
      ∃ c : Fin n, (T.E.component j).stalkIdeal x = Ideal.span {z c} := by
  obtain ⟨n, z, hz⟩ := T.isSnc.2 x
  obtain ⟨-, c, -, hc⟩ := id hz
  exact ⟨n, z, hz, c ⟨j, hx⟩, hc ⟨j, hx⟩⟩

/-- The stalk of `E^j` at a point of `E^j` is prime: it is generated by one member of a regular
system of parameters of the regular local ring `𝒪_{X,x}` (`isPrime_span_singleton_of_parameters`,
`Hironaka/Scheme/Snc/TrivialTotalTransform.lean`). -/
theorem isPrime_stalkIdeal_component {x : T.X.left} (hx : x ∈ (T.E.component j).support) :
    ((T.E.component j).stalkIdeal x).IsPrime := by
  obtain ⟨n, z, hz, c, hc⟩ := exists_stalkIdeal_component_eq_span T j hx
  have := isRegularLocalRing_stalk (T.X.left ↘ Spec (.of k)) x
  rw [hc]
  exact isPrime_span_singleton_of_parameters hz.1.1.symm hz.1.2 c

/-- At a point of `Z_{-1}` the stalks of `Z_{-1}` and of `E^j` coincide (the components of the
regular `E^j` are pairwise disjoint). -/
theorem stalkIdeal_Zminus1_eq {x : T.X.left} (hx : x ∈ (Zminus1 T.I m (T.E.component j)).support) :
    (Zminus1 T.I m (T.E.component j)).stalkIdeal x = (T.E.component j).stalkIdeal x := by
  have hN := noetherianSpace_triple T
  obtain ⟨η, hη, hm, hηx⟩ :=
    (Set.ext_iff.mp (coe_support_Zminus1 T.I m (T.E.component j)) x).mp hx
  refine le_antisymm ?_ (Scheme.IdealSheafData.stalkIdeal_mono (component_le_Zminus1 T m j) x)
  have hle : Zminus1 T.I m (T.E.component j) ≤ Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure {η}) :=
    Scheme.IdealSheafData.vanishingIdeal_antimono (le_iSup (fun η' : {η' : T.X.left //
      η' ∈ (T.E.component j).support.genericPoints ∧ (m : ℕ∞) ≤ T.I.ord η'} =>
        Closeds.closure {(η' : T.X.left)}) ⟨η, hη, hm⟩)
  have hmin :=
    Hironaka.Sequence.stalkIdeal_vanishingIdeal_mem_minimalPrimes (T.E.component j) hη hηx
  have hxj : x ∈ (T.E.component j).support := support_Zminus1_le_support T.I m (T.E.component j) hx
  have := isPrime_stalkIdeal_component T j hxj
  rw [Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff] at hmin
  calc (Zminus1 T.I m (T.E.component j)).stalkIdeal x
      ≤ (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal x :=
          Scheme.IdealSheafData.stalkIdeal_mono hle x
    _ = (T.E.component j).stalkIdeal x := hmin

/-- At a point of `Z_{-1}` its stalk is `(z_c)` for Kollár's snc coordinates `z` at that point. -/
theorem exists_stalkIdeal_Zminus1_eq_span {x : T.X.left}
    (hx : x ∈ (Zminus1 T.I m (T.E.component j)).support) :
    ∃ (n : ℕ) (z : Fin n → T.X.left.presheaf.stalk x), T.E.IsSncAt x z ∧
      ∃ c : Fin n, (Zminus1 T.I m (T.E.component j)).stalkIdeal x = Ideal.span {z c} := by
  obtain ⟨n, z, hz, c, hc⟩ :=
    exists_stalkIdeal_component_eq_span T j (support_Zminus1_le_support T.I m (T.E.component j) hx)
  exact ⟨n, z, hz, c, by rw [stalkIdeal_Zminus1_eq T m j hx, hc]⟩

/-! ### Simple normal crossings with `E` -/

/-- `Z_{-1}` has simple normal crossings with `E` ([Kol07, Definition 24, (4)]): at each of its
points it is `(z_c = 0)` in Kollár's coordinates. -/
theorem hasSncWith_Zminus1 : T.E.HasSncWith (Zminus1 T.I m (T.E.component j)) := by
  intro x hx
  obtain ⟨n, z, hz, c, hc⟩ := exists_stalkIdeal_Zminus1_eq_span T m j hx
  refine ⟨n, z, hz, {c}, ?_⟩
  rw [hc, Finset.coe_singleton, Set.image_singleton]

end NoCharZero

section CharZero

variable {k : Type u} [Field k]

/-! ### Smooth, Cartier, `ord_{Z_{-1}} I = m`, the sequence -/

/-- `Z_{-1}` is smooth over `k` ([Kol07, Definition 65, (1)]; [Kol07, Notation 19]): a subscheme
with simple normal crossings with an snc family is smooth over a perfect field
(`smooth_of_hasSncWith`). -/
theorem smooth_Zminus1 [CharZero k] (T : Triple k) (m : ℕ) (j : T.E.ι) :
    Smooth ((Zminus1 T.I m (T.E.component j)).subschemeι ≫ (T.X.left ↘ Spec (.of k))) :=
  Hironaka.Sequence.smooth_of_hasSncWith (T.X.left ↘ Spec (.of k)) (hasSncWith_Zminus1 T m j)

/-- `Z_{-1}` is a Cartier divisor ([Kol07, Warning 20]): its stalk at every point is the unit ideal
or `(z_c)`, a nonzerodivisor of the regular local ring `𝒪_{X,x}`. -/
theorem isInvertible_Zminus1 (T : Triple k) (m : ℕ) (j : T.E.ι) :
    (Zminus1 T.I m (T.E.component j)).IsInvertible := by
  have : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  apply Scheme.IdealSheafData.isInvertible_of_forall_stalkIdeal_eq_span
  intro x
  by_cases hx : x ∈ (Zminus1 T.I m (T.E.component j)).support
  · obtain ⟨n, z, hz, c, hc⟩ := exists_stalkIdeal_Zminus1_eq_span T m j hx
    have := isRegularLocalRing_stalk (T.X.left ↘ Spec (.of k)) x
    have := isDomain_of_isRegularLocalRing (T.X.left.presheaf.stalk x)
    have hzc := mem_maximalIdeal_and_notMem_sq_of_span_eq hz.1 c
    refine ⟨z c, mem_nonZeroDivisors_of_ne_zero fun h0 => hzc.2 ?_, hc⟩
    rw [h0]
    exact Ideal.zero_mem _
  · refine ⟨1, Submonoid.one_mem _, ?_⟩
    rw [Scheme.IdealSheafData.stalkIdeal_eq_top_of_notMem_support _ hx, Ideal.span_singleton_one]

/-- `π_{-1} : X_0 → X` is an isomorphism ("The blow-up is an isomorphism", the proof of
[Kol07, Lemma 102]; [Kol07, Warning 20]). -/
theorem isIso_blowUpπ_Zminus1 (T : Triple k) (m : ℕ) (j : T.E.ι) :
    IsIso (Zminus1 T.I m (T.E.component j)).blowUpπ :=
  Scheme.IdealSheafData.blowUp.isIso_π_of_isInvertible _ (isInvertible_Zminus1 T m j)

/-- The generic points of `Z_{-1}` are exactly the selected generic points of `E^j`. -/
theorem mem_genericPoints_support_Zminus1_iff (T : Triple k) (m : ℕ) (j : T.E.ι)
    (η : T.X.left) :
    η ∈ (Zminus1 T.I m (T.E.component j)).support.genericPoints ↔
      η ∈ (T.E.component j).support.genericPoints ∧ (m : ℕ∞) ≤ T.I.ord η := by
  have hN := noetherianSpace_triple T
  have hcoe := Set.ext_iff.mp (coe_support_Zminus1 T.I m (T.E.component j))
  constructor
  · rintro ⟨hηZ, hmax⟩
    obtain ⟨η', hη', hm', hη'η⟩ := (hcoe η).mp hηZ
    have hη'Z : η' ∈ (Zminus1 T.I m (T.E.component j)).support :=
      (hcoe η').mpr ⟨η', hη', hm', specializes_refl _⟩
    obtain rfl := hmax hη'Z hη'η
    exact ⟨hη', hm'⟩
  · rintro ⟨hη, hm⟩
    refine ⟨(hcoe η).mpr ⟨η, hη, hm, specializes_refl _⟩, fun ξ hξZ hξη => ?_⟩
    obtain ⟨η'', hη'', -, hη''ξ⟩ := (hcoe ξ).mp hξZ
    obtain rfl : η'' = η := hη.2 hη''.1 (hη''ξ.trans hξη)
    exact (hξη.antisymm hη''ξ).eq

/-- For `max-ord I = m`, `ord_{Z_{-1}} I = m` ([Kol07, Definition 65, (2)]): `≥ m` at the selected
generic points, `≤ max-ord I` everywhere. -/
theorem ordAlongEq_Zminus1 (T : Triple k) (m : ℕ) (j : T.E.ι)
    (hmax : T.I.maxOrd = m) :
    T.I.OrdAlongEq (Zminus1 T.I m (T.E.component j)).support (m : ℕ∞) := by
  intro η hη
  obtain ⟨-, hm⟩ := (mem_genericPoints_support_Zminus1_iff T m j η).mp hη
  exact le_antisymm (hmax ▸ T.I.le_maxOrd η) hm

/-- For `max-ord I = m`, `Z_{-1}` is a smooth blow-up of order `m` of `(X, I, E)`
([Kol07, Definition 65]; the proof of [Kol07, Lemma 102]). -/
theorem isOrderBlowUp_Zminus1 [CharZero k] (T : Triple k) (m : ℕ) (j : T.E.ι)
    (hmax : T.I.maxOrd = m) : T.IsOrderBlowUp (Zminus1 T.I m (T.E.component j)) m :=
  ⟨smooth_Zminus1 T m j, hasSncWith_Zminus1 T m j, ordAlongEq_Zminus1 T m j hmax⟩

/-- For `max-ord I = m`, the one-step sequence `π_{-1}` is a smooth blow-up sequence of order `m`
starting with `(X, I, E)` ([Kol07, Definition 66]). -/
theorem isOrderSeq_piMinusOne [CharZero k] (T : Triple k) (m : ℕ) (j : T.E.ι)
    (hmax : T.I.maxOrd = m) :
    (piMinusOne T.I m (T.E.component j)).IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m :=
  (isOrderSeq_cons_iff (T.X.left ↘ Spec (.of k)) T.I T.E m _ (nil _)).mpr
    ⟨isOrderBlowUp_Zminus1 T m j hmax, isOrderSeq_nil _ _ _ _⟩

end CharZero

end Hironaka.BD
