/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Snc.Basic
public import Hironaka.Scheme.Snc.SmoothDivisor
import Hironaka.Algebra.Local.RegularSystem
import Hironaka.Scheme.BlowUpSequence.RestrictDivisors
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.Snc.ParameterSubset
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Simple normal crossings restricted to a smooth hypersurface

The proof of [Kol07, Corollary 85]: for `Z ⊆ H` smooth with `H + E` snc at every point, `Z` has
simple normal crossings with `E` in `X` iff it has them with `H + E` in `X` iff it has them with
`E|_H` in `H` — Kollár: "this poses the same restriction on order reduction", since `E|_H` is again
snc. Going down to a hypersurface of maximal contact
(`Hironaka.Resolution.Algebraic.MaximalContact.GoingDown`) needs the passage to `H`: when the centre
`Z_i ⊆ H_i` of a blow-up has simple normal crossings with `E_i + H_i` on `X_i` (from `Z_i` snc with
`E_i` and `H_i + E_i` snc, `hasSncWith_append_of_le`), the same centre, viewed in `H_i`, has simple
normal crossings with `E_i|_{H_i}`. This is clause (3′) of [Kol07, Definition 66] for the restricted
sequence.

**The point lemma.** Let `g : Y ⟶ X` be a closed immersion with image `H = V(ker g)`, and let `Z`
have simple normal crossings with `E + H` at `x = g(y) ∈ Z`: coordinates `z_1, …, z_n` (a regular
system of parameters of `𝒪_{X,x}`), `E^i = (z_{c(i)})` for the components through `x`, `H = (z_h)`,
and `Z = (z_s : s ∈ S)`. Since `Z ⊆ H`, `z_h ∈ (z_s : s ∈ S)`, so `h ∈ S` (`mem_span_image_iff` of
`Hironaka.Scheme.Snc.ParameterSubset`). The stalk map `φ : 𝒪_{X,x} → 𝒪_{Y,y}` is surjective with
kernel `(z_h)` (`ker_stalkMap_of_isClosedImmersion` of
`Hironaka.Scheme.BlowUpSequence.RestrictDivisors`), so the images of the `z_j`, `j ≠ h`, form a
regular system of parameters of `𝒪_{Y,y}` (`span_range_comp_compl_eq_maximalIdeal`,
`natCast_sub_card_eq_ringKrullDim_of_ker`), the components of `E|_H` through `y` are the `(φ
z_{c(i)})` with `c(i) ≠ h` (injectivity of `c`), and `Z|_H = (φ z_s : s ∈ S ∖ {h})` — the generator
`φ z_h = 0` drops out. The bookkeeping of the surviving indices is `complIndex` of
`Hironaka.Scheme.Snc.ParameterSubset`.

**The smooth divisor as a family.** For the case `E = ∅` of [Kol07, Definition 78] the restricted
sequence's clause (3′) is the normal crossing of the centres with the exceptional divisors on `H`,
and the restricted sequence needs "`∅ + H` is snc": a smooth divisor `H` alone is a simple normal
crossing family, because a generator of `H_x` in `𝔪_x ∖ 𝔪_x²` extends to a regular system of
parameters (`exists_span_eq_maximalIdeal_of_notMem_sq` of `Hironaka.Algebra.Local.RegularSystem`),
and at a point off `H` any regular system of parameters serves
(`isSnc_append_empty_of_isSmoothDivisor`).

Sources: [Kol07, Corollary 85] (the proof); [Kol07, Definition 24; Definition 66; Definition 78].
-/

public section

universe u

open AlgebraicGeometry CategoryTheory IsLocalRing Ideal Scheme TopologicalSpace

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- The restriction direction of the proof of [Kol07, Corollary 85]: for a closed immersion
`g : Y ⟶ X` with image `H = V(ker g)` and a closed subscheme `Z ⊆ H` having simple normal crossings
with `E + H`, the subscheme `Z` of `Y` has simple normal crossings with `E|_H = E.comap g`. -/
theorem hasSncWith_comap_of_isClosedImmersion (g : Y ⟶ X) [IsClosedImmersion g]
    (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) {E : DivisorFamily X}
    {Z : X.IdealSheafData} (hZ : (E.append g.ker).HasSncWith Z) (hle : g.ker ≤ Z) :
    (E.comap g).HasSncWith (Z.comap g) := by
  classical
  intro y hy
  have hx : g y ∈ Z.support := by rwa [Scheme.IdealSheafData.support_comap] at hy
  have := hreg (g y)
  obtain ⟨n, z, ⟨⟨hzspan, hzdim⟩, c, hcinj, hc⟩, s, hs⟩ := hZ (g y) hx
  have hxH : g y ∈ ((E.append g.ker).component (toLex (Sum.inr PUnit.unit))).support :=
    Scheme.IdealSheafData.support_antitone hle hx
  set h0 : Fin n := c ⟨toLex (Sum.inr PUnit.unit), hxH⟩ with hh0
  have hker : g.ker.stalkIdeal (g y) = span {z h0} := hc ⟨toLex (Sum.inr PUnit.unit), hxH⟩
  -- the stalk map: surjective with kernel `(z_{h0})`
  set φ : X.presheaf.stalk (g y) →+* Y.presheaf.stalk y := (g.stalkMap y).hom with hφdef
  have hφ : Function.Surjective φ := g.stalkMap_surjective y
  have hkerφ : RingHom.ker φ = span (z '' ↑({h0} : Finset (Fin n))) := by
    rw [hφdef, ker_stalkMap_of_isClosedImmersion, hker, Finset.coe_singleton,
      Set.image_singleton]
  -- the coordinates of `Y` at `y`: the images of the `z_j`, `j ≠ h0`
  set z' : Fin ({h0} : Finset (Fin n))ᶜ.card → Y.presheaf.stalk y :=
    φ ∘ z ∘ ({h0} : Finset (Fin n))ᶜ.orderEmbOfFin rfl with hz'
  have hz'span : span (Set.range z') = maximalIdeal (Y.presheaf.stalk y) :=
    span_range_comp_compl_eq_maximalIdeal hzspan.symm hφ hkerφ
  have hz'dim : ((({h0} : Finset (Fin n))ᶜ.card : ℕ) : WithBot ℕ∞) =
      ringKrullDim (Y.presheaf.stalk y) := by
    rw [Finset.card_compl, Fintype.card_fin]
    exact natCast_sub_card_eq_ringKrullDim_of_ker hzspan.symm hzdim hφ hkerφ
  -- the components of `E` through `y` are the components of `E` through `g y`
  have hEy : ∀ i : {i : E.ι // y ∈ ((E.comap g).component i).support},
      g y ∈ ((E.append g.ker).component (toLex (Sum.inl i.1))).support := fun i => by
    have hi := i.2
    rwa [show (E.comap g).component i.1 = (E.component i.1).comap g from rfl,
      Scheme.IdealSheafData.support_comap] at hi
  have hno : ∀ i : {i : E.ι // y ∈ ((E.comap g).component i).support},
      c ⟨toLex (Sum.inl i.1), hEy i⟩ ∉ ({h0} : Finset (Fin n)) := fun i hmem => by
    rw [Finset.mem_singleton, hh0] at hmem
    exact Sum.inl_ne_inr (toLex.injective (congrArg Subtype.val (hcinj hmem)))
  refine ⟨_, z', ⟨⟨hz'span, hz'dim⟩, fun i => complIndex (hno i), ?_, fun i => ?_⟩, ?_⟩
  · intro i i' hii'
    have h' := congrArg (({h0} : Finset (Fin n))ᶜ.orderEmbOfFin rfl) hii'
    simp only [orderEmbOfFin_complIndex] at h'
    exact Subtype.ext (Sum.inl_injective (toLex.injective (congrArg Subtype.val (hcinj h'))))
  · change ((E.component i.1).comap g).stalkIdeal y = span {z' (complIndex (hno i))}
    have hci : (E.component i.1).stalkIdeal (g y) = span {z (c ⟨toLex (Sum.inl i.1), hEy i⟩)} :=
      hc ⟨toLex (Sum.inl i.1), hEy i⟩
    rw [Scheme.IdealSheafData.stalkIdeal_comap, hci, Ideal.map_span, Set.image_singleton, hz']
    simp only [Function.comp_apply, orderEmbOfFin_complIndex]
    rfl
  · -- `Z|_H = (φ z_s : s ∈ S ∖ {h0})`
    refine ⟨Finset.univ.filter fun j' => ({h0} : Finset (Fin n))ᶜ.orderEmbOfFin rfl j' ∈ s, ?_⟩
    rw [Scheme.IdealSheafData.stalkIdeal_comap, hs, Ideal.map_span]
    apply le_antisymm
    · refine span_le.mpr ?_
      rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
      by_cases hjh : j = h0
      · have hz0 : φ (z j) = 0 := by
          rw [← RingHom.mem_ker, hkerφ]
          exact subset_span ⟨j, by simp [hjh], rfl⟩
        change φ (z j) ∈ _
        rw [hz0]
        exact zero_mem _
      · have hjc : j ∉ ({h0} : Finset (Fin n)) := by simpa using hjh
        refine subset_span ⟨complIndex hjc, ?_, ?_⟩
        · rw [Finset.mem_coe, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, by rw [orderEmbOfFin_complIndex]; exact hj⟩
        · simp only [hz', Function.comp_apply, orderEmbOfFin_complIndex]
          rfl
    · refine span_le.mpr ?_
      rintro _ ⟨j', hj', rfl⟩
      rw [Finset.mem_coe, Finset.mem_filter] at hj'
      exact subset_span ⟨z (({h0} : Finset (Fin n))ᶜ.orderEmbOfFin rfl j'), ⟨_, hj'.2, rfl⟩, rfl⟩

/-- A smooth divisor `H` alone is a simple normal crossing family — Kollár's `H + E` with `E = ∅`:
at a point of `H` the generator of `H_x` in `𝔪_x ∖ 𝔪_x²` extends to a regular system of parameters,
and off `H` any regular system of parameters serves; the only component is `H`. -/
theorem isSnc_append_empty_of_isSmoothDivisor
    (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) {H : X.IdealSheafData}
    (hH : IsSmoothDivisor H) : ((DivisorFamily.empty X).append H).IsSnc := by
  classical
  have hidx : ∀ (x : X) (i : {i : ((DivisorFamily.empty X).append H).ι //
      x ∈ (((DivisorFamily.empty X).append H).component i).support}),
      i.1 = toLex (Sum.inr PUnit.unit) := by
    intro x i
    obtain ⟨a, ha⟩ := toLex.surjective i.1
    rcases a with e | u
    · exact e.elim
    · cases u
      exact ha.symm
  refine ⟨fun i => ?_, fun x => ?_⟩
  · obtain ⟨a, rfl⟩ := toLex.surjective i
    rcases a with e | u
    · exact e.elim
    · exact hH.1
  · have := hreg x
    obtain ⟨d, w, hw, hd⟩ := exists_regularSystem (X.presheaf.stalk x)
    by_cases hx : x ∈ H.support
    · obtain ⟨a, ha, ha2, hHx⟩ := hH.2 x hx
      obtain ⟨z, ⟨i0, hi0⟩, hz⟩ :=
        exists_span_eq_maximalIdeal_of_notMem_sq hd ha ha2
      refine ⟨d, z, ⟨hz.symm, hd⟩, fun _ => i0, fun i i' _ => Subtype.ext ?_, fun i => ?_⟩
      · rw [hidx x i, hidx x i']
      · rw [show i.1 = toLex (Sum.inr PUnit.unit) from hidx x i]
        change H.stalkIdeal x = span {z i0}
        rw [hHx, hi0]
    · refine ⟨d, w, ⟨hw.symm, hd⟩, fun i => (hx ?_).elim, fun i => (hx ?_).elim,
        fun i => (hx ?_).elim⟩
      all_goals
        have hi := i.2
        rw [hidx x i] at hi
        exact hi

end AlgebraicGeometry
