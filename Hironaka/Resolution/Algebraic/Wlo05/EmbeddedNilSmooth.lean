/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedNilInvariant
public import Hironaka.Scheme.Snc.Dictionary
import Hironaka.Resolution.Algebraic.BoundaryClearing.Basic
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseBlowUp
import Hironaka.Resolution.Algebraic.Kol07.Prop37.Prop37Descent
import Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineEndResult
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The initial invariant of a smooth `Y`

For a smooth reduced `Y = V(I)` in a triple `(X, I, ∅)`, the loop's initial state
`(X, I, componentIdeals)` satisfies the invariant of
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedNilInvariant` (`invariant_componentIdeals`): the
components of `Y` — the reduced ideals of the closures of the generic points of `supp I` — have
pairwise disjoint supports and multiply to `I` (`prod_componentFamily_eq`,
`pairwise_disjoint_support_componentFamily`, for the regular `Y`: `isRegular_of_smooth`), and `I` is
regular stalkwise (`isRegularLocalRing_quotient_stalkIdeal`). The loop's member set is the image of
the component family's index type (`componentIdeals_eq_image_univ`; the component map is injective
on the generic points since a generic point is determined by its closure).

Given the core lemma, the empty succession follows: `BED(X, I_Y, ∅)` has length `0`
(`length_bedAux_eq_zero_of_invariant`), hence is the empty succession
(`bed_eq_nil_of_smooth_of_core`); the core lemma is proved in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedNilCore`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme BlowUpSequence
  Scheme.IdealSheafData Hironaka.Stage Hironaka.Sequence

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

omit [CharZero k] in
open Classical in
/-- The loop's member set is the image of the component family's index type. -/
theorem componentIdeals_eq_image_univ (T : Triple k) [NoetherianSpace T.X.left] :
    componentIdeals T = Finset.univ.image T.I.componentFamily.component := by
  ext c
  constructor
  · intro hc
    obtain ⟨η, hη, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_image.mpr ⟨⟨η, (Set.Finite.mem_toFinset _).mp hη⟩, Finset.mem_univ _, rfl⟩
  · intro hc
    obtain ⟨η, -, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_image.mpr ⟨η.1, (Set.Finite.mem_toFinset _).mpr η.2, rfl⟩

omit [CharZero k] in
/-- The component map is injective on the generic points: a generic point is determined by the
support of its component (its closure). -/
theorem componentFamily_component_injective (T : Triple k) [NoetherianSpace T.X.left] :
    Function.Injective T.I.componentFamily.component := by
  intro i j hij
  have hi : i.1 ∈ (T.I.componentFamily.component i).support :=
    (mem_support_componentFamily_iff T.I i i.1).mpr (specializes_refl _)
  rw [hij] at hi
  exact Subtype.ext (i.2.2 j.2.1 ((mem_support_componentFamily_iff T.I j i.1).mp hi)).symm

omit [CharZero k] in
/-- For a regular `Y = V(I)` the product of the loop's members is `I`
(`prod_componentFamily_eq`). -/
theorem prod_componentIdeals_eq (T : Triple k) [NoetherianSpace T.X.left]
    (hZ : IsRegular T.I.subscheme) : ∏ c ∈ componentIdeals T, c = T.I := by
  classical
  rw [componentIdeals_eq_image_univ,
    Finset.prod_image (componentFamily_component_injective T).injOn]
  exact prod_componentFamily_eq T.I hZ

omit [CharZero k] in
/-- For a regular `Y = V(I)` the loop's members have pairwise disjoint supports
(`pairwise_disjoint_support_componentFamily`). -/
theorem pairwise_disjoint_componentIdeals (T : Triple k) [NoetherianSpace T.X.left]
    (hZ : IsRegular T.I.subscheme) :
    ((componentIdeals T : Finset T.X.left.IdealSheafData) : Set T.X.left.IdealSheafData).Pairwise
      fun a b => Disjoint a.support b.support := by
  classical
  intro a ha b hb hab
  rw [Finset.mem_coe, componentIdeals_eq_image_univ, Finset.mem_image] at ha hb
  obtain ⟨i, -, rfl⟩ := ha
  obtain ⟨j, -, rfl⟩ := hb
  exact pairwise_disjoint_support_componentFamily T.I hZ fun h => hab (h ▸ rfl)

/-- **The initial invariant** — for a smooth `Y = V(I)` in a triple with empty boundary, the loop's
initial state `(X, I, componentIdeals)` satisfies the invariant. -/
theorem invariant_componentIdeals (T : Triple k) (hE : IsEmpty T.E.ι)
    (hY : Smooth (T.I.subschemeι ≫ (T.X.left ↘ Spec (CommRingCat.of k)))) :
    Invariant T.I T.E (componentIdeals T) := by
  classical
  have := Hironaka.BD.noetherianSpace_triple T
  have := hY
  have hZ : IsRegular T.I.subscheme :=
    isRegular_of_smooth (T.I.subschemeι ≫ (T.X.left ↘ Spec (CommRingCat.of k)))
  refine ⟨hE, (prod_componentIdeals_eq T hZ).symm, ?_, pairwise_disjoint_componentIdeals T hZ, ?_⟩
  · intro c hc
    obtain ⟨η, hη, rfl⟩ := Finset.mem_image.mp hc
    exact ⟨η, (Set.Finite.mem_toFinset _).mp hη, rfl⟩
  · intro x hx
    exact isRegularLocalRing_quotient_stalkIdeal T.I (T.X.left ↘ Spec (.of k)) hx

/-- **The empty succession given the core lemma** — for a smooth reduced `Y` the embedded
desingularization sequence `BED(X, I_Y, ∅)` is the empty succession ([Wlo05, 4.6]: at a smooth
point of `Y` the invariant is terminal). -/
theorem bed_eq_nil_of_smooth_of_core (hcore : Core k) (TX : Triple k) (hE : IsEmpty TX.E.ι)
    (hY : Smooth (TX.I.subschemeι ≫ (TX.X.left ↘ Spec (CommRingCat.of k)))) :
    BED TX = BlowUpSequence.nil TX.X.left := by
  rw [BED_eq]
  exact Hironaka.Sequence.eq_nil_of_length_eq_zero
    (length_bedAux_eq_zero_of_invariant hcore _ ⟨TX, 1⟩ rfl (componentIdeals TX) rfl
      (invariant_componentIdeals TX hE hY))

end Hironaka.Resolution
