/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Snc.SncOn
public import Hironaka.Scheme.Snc.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUpSequence.RestrictDivisors
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Scheme.Snc.ParameterSubset
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Simple normal crossings with an appended hypersurface along the center; sub-families

`hasSncWith_append_of_le` (`Hironaka/Scheme/BlowUpSequence/RestrictDivisors.lean`; [Kol07,
Definition 24 (4)]) takes `H + E` to have simple normal crossings on the whole scheme but uses the
data only at the points of the center `Z`. In the boundary-clearing step of the proof of Theorem 103
[Kol07, 104, Step 2.1] the family `H_k + E_k` has simple normal crossings only along the points
of order `≥ m` (the original members of `E` may meet `H` badly away from them), so this module
gives the variant `hasSncWith_append_of_le_on` with the hypothesis in the along-a-set form
`IsSncOn Z.support` (the same argument), and `HasSncWith.subfamily`: a center having simple normal
crossings with `E` has simple normal crossings with every sub-family of `E` (restrict the
injection of [Kol07, Definition 24 (3)]).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme BlowUpSequence IsLocalRing Ideal

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- A center having simple normal crossings with `E` has simple normal crossings with every
sub-family of `E`: restrict the injection of [Kol07, Definition 24 (3)]. -/
theorem HasSncWith.subfamily {E : DivisorFamily X} {Z : X.IdealSheafData} (h : E.HasSncWith Z)
    (p : E.ι → Prop) : (E.subfamily p).HasSncWith Z := by
  intro x hx
  obtain ⟨n, z, ⟨hrs, c, hcinj, hc⟩, s, hs⟩ := h x hx
  refine ⟨n, z, ⟨hrs, fun i => c ⟨i.1.1, i.2⟩, ?_, fun i => hc ⟨i.1.1, i.2⟩⟩, s, hs⟩
  intro i₁ i₂ h12
  have h0 : i₁.1.1 = i₂.1.1 := Subtype.mk.inj (hcinj h12)
  exact Subtype.ext (Subtype.ext h0)

variable {k : Type u} [Field k]

/-- `hasSncWith_append_of_le` with the hypothesis on `E + J` weakened to the points of the center:
a center `Z ⊆ V(J)` having simple normal crossings with `E`, such that `E + J` has simple normal
crossings at every point of `Z`, has simple normal crossings with `E + J`
[Kol07, Definition 24 (4)]. The proof exchanges a coordinate of `Z` for the equation of `J` in
`𝔪/𝔪²`, as in `hasSncWith_append_of_le`. -/
theorem hasSncWith_append_of_le_on (f : X ⟶ Spec (.of k)) [Smooth f]
    {E : DivisorFamily X} {J Z : X.IdealSheafData} (hE : (E.append J).IsSncOn Z.support)
    (hZ : E.HasSncWith Z) (hle : J ≤ Z) : (E.append J).HasSncWith Z := by
  classical
  intro x hx
  have hreg : IsRegularLocalRing (X.presheaf.stalk x) :=
    isRegularLocalRing_stalk f x
  obtain ⟨n, z, ⟨⟨hzspan, hzdim⟩, c, hcinj, hcE⟩, s, hs⟩ := hZ x hx
  obtain ⟨n', z', ⟨hz'span, hz'dim⟩, c', hc'inj, hc'⟩ := hE x hx
  have hxJ : x ∈ J.support := Scheme.IdealSheafData.support_antitone hle hx
  have hxH : x ∈ ((E.append J).component (toLex (Sum.inr PUnit.unit))).support := hxJ
  set g : X.presheaf.stalk x := z' (c' ⟨toLex (Sum.inr PUnit.unit), hxH⟩) with hg
  have hJg : J.stalkIdeal x = span {g} := hc' ⟨toLex (Sum.inr PUnit.unit), hxH⟩
  have hcE' : ∀ i : {i : E.ι // x ∈ (E.component i).support},
      (E.component i.1).stalkIdeal x = span {z' (c' ⟨toLex (Sum.inl i.1), i.2⟩)} :=
    fun i => hc' ⟨toLex (Sum.inl i.1), i.2⟩
  have hcEz : ∀ i : {i : E.ι // x ∈ (E.component i).support},
      (E.component i.1).stalkIdeal x = span {z (c i)} := fun i => hcE i
  have hZs : Z.stalkIdeal x = span (z '' ↑s) := hs
  have hgm : g ∈ maximalIdeal (X.presheaf.stalk x) := hz'span ▸ subset_span ⟨_, rfl⟩
  have hzm : ∀ t, z t ∈ maximalIdeal (X.presheaf.stalk x) := fun t => hzspan ▸ subset_span ⟨t, rfl⟩
  -- `g ∈ Z_x = (z_s)_{s ∈ S}`
  have hgZ : g ∈ span (Set.range fun t : ↥(↑s : Set (Fin n)) => z t) := by
    rw [← Set.image_eq_range, ← hZs]
    exact Scheme.IdealSheafData.stalkIdeal_mono hle x (hJg ▸ mem_span_singleton_self g)
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp hgZ
  -- the `E`-coordinates of the `z`-system lie in the span of those of the `z'`-system
  set S' : Finset (Fin n') := Finset.univ.image
    fun i : {i : E.ι // x ∈ (E.component i).support} => c' ⟨toLex (Sum.inl i.1), i.2⟩ with hS'
  have hspan_le : span (z '' Set.range c) ≤ span (z' '' ↑S') := by
    refine span_le.mpr ?_
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    have h1 : z (c i) ∈ (E.component i.1).stalkIdeal x := by
      rw [hcEz i]; exact mem_span_singleton_self _
    rw [hcE' i] at h1
    have h2 : span {z' (c' ⟨toLex (Sum.inl i.1), i.2⟩)} ≤ span (z' '' ↑S') :=
      span_le.mpr (Set.singleton_subset_iff.mpr (subset_span
        ⟨_, Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ i)), rfl⟩))
    exact h2 h1
  -- a unit coefficient at a non-`E` index
  have hex : ∃ t : ↥(↑s : Set (Fin n)), IsUnit (a t) ∧ (t : Fin n) ∉ Set.range c := by
    by_contra hcon
    have hcon' : ∀ t : ↥(↑s : Set (Fin n)), IsUnit (a t) → (t : Fin n) ∈ Set.range c :=
      fun t hu => by_contra fun hn => hcon ⟨t, hu, hn⟩
    have hmem : g ∈ maximalIdeal (X.presheaf.stalk x) ^ 2 ⊔ span (z '' Set.range c) := by
      rw [← ha]
      refine Ideal.sum_mem _ fun t _ => ?_
      by_cases hu : IsUnit (a t)
      · exact Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (subset_span ⟨t, hcon' t hu, rfl⟩))
      · have ham : a t ∈ maximalIdeal (X.presheaf.stalk x) :=
          (IsLocalRing.mem_maximalIdeal _).mpr hu
        exact Ideal.mem_sup_left (by rw [pow_two]; exact Ideal.mul_mem_mul ham (hzm t))
    have hmem' : g ∈ maximalIdeal (X.presheaf.stalk x) ^ 2 ⊔ span (z' '' ↑S') :=
      sup_le_sup_left hspan_le _ hmem
    refine notMem_sq_sup_span_image hz'span.symm hz'dim (s := S')
      (j := c' ⟨toLex (Sum.inr PUnit.unit), hxH⟩) ?_ hmem'
    intro hin
    rw [hS', Finset.mem_image] at hin
    obtain ⟨i, -, hi⟩ := hin
    exact Sum.inl_ne_inr (toLex.injective (congrArg Subtype.val (hc'inj hi)))
  obtain ⟨t₀, hu, ht₀⟩ := hex
  -- the exchanged system `z̃ = update z t₀ g`
  set zt := Function.update z (t₀ : Fin n) g with hzt
  have hzt_ne : ∀ t, t ≠ (t₀ : Fin n) → zt t = z t := fun t ht => Function.update_of_ne ht _ _
  have hzt_t₀ : zt t₀ = g := Function.update_self _ _ _
  -- `z t₀` in terms of `g` and the other coordinates
  have hsplit : g = a t₀ * z t₀ + ∑ t ∈ Finset.univ.erase t₀, a t * z t := by
    rw [Finset.add_sum_erase Finset.univ (fun t => a t * z t) (Finset.mem_univ t₀)]; exact ha.symm
  have hz₀ : z t₀ = ↑hu.unit⁻¹ * (g - ∑ t ∈ Finset.univ.erase t₀, a t * z t) := by
    have h1 : a t₀ * z t₀ = g - ∑ t ∈ Finset.univ.erase t₀, a t * z t := by
      rw [hsplit]; ring
    calc z t₀ = ↑hu.unit⁻¹ * (↑hu.unit * z t₀) := (Units.inv_mul_cancel_left _ _).symm
      _ = ↑hu.unit⁻¹ * (g - ∑ t ∈ Finset.univ.erase t₀, a t * z t) := by
        rw [IsUnit.unit_spec, h1]
  have hmem_zt : ∀ t, zt t ∈ maximalIdeal (X.presheaf.stalk x) := by
    intro t
    by_cases ht : t = t₀
    · rw [ht, hzt_t₀]; exact hgm
    · rw [hzt_ne t ht]; exact hzm t
  have hz₀_mem : ∀ T : Set (Fin n), (t₀ : Fin n) ∈ T →
      (∀ t : ↥(↑s : Set (Fin n)), (t : Fin n) ∈ T) → z t₀ ∈ span (zt '' T) := by
    intro T ht₀T hsT
    rw [hz₀]
    refine Ideal.mul_mem_left _ _ (Ideal.sub_mem _ ?_ (Ideal.sum_mem _ fun t ht => ?_))
    · rw [← hzt_t₀]; exact subset_span ⟨t₀, ht₀T, rfl⟩
    · have hne : (t : Fin n) ≠ t₀ := fun h => (Finset.mem_erase.mp ht).1 (Subtype.ext h)
      rw [← hzt_ne t hne]
      exact Ideal.mul_mem_left _ _ (subset_span ⟨t, hsT t, rfl⟩)
  have hspan_zt : span (Set.range zt) = maximalIdeal (X.presheaf.stalk x) := by
    refine le_antisymm (span_le.mpr ?_) ?_
    · rintro _ ⟨t, rfl⟩; exact hmem_zt t
    · rw [← hzspan]
      refine span_le.mpr ?_
      rintro _ ⟨t, rfl⟩
      by_cases ht : t = t₀
      · rw [ht, ← Set.image_univ]
        exact hz₀_mem _ (Set.mem_univ _) fun _ => Set.mem_univ _
      · rw [← hzt_ne t ht]; exact subset_span ⟨t, rfl⟩
  have hZ_zt : Z.stalkIdeal x = span (zt '' ↑s) := by
    rw [hZs]
    refine le_antisymm (span_le.mpr ?_) (span_le.mpr ?_)
    · rintro _ ⟨t, hts, rfl⟩
      by_cases ht : t = t₀
      · rw [ht]; exact hz₀_mem _ t₀.2 fun t' => t'.2
      · rw [← hzt_ne t ht]; exact subset_span ⟨t, hts, rfl⟩
    · rintro _ ⟨t, hts, rfl⟩
      by_cases ht : t = t₀
      · rw [ht, hzt_t₀, Set.image_eq_range]; exact hgZ
      · rw [hzt_ne t ht]; exact subset_span ⟨t, hts, rfl⟩
  refine ⟨n, zt, ⟨⟨hspan_zt, hzdim⟩, appendIdx c (t₀ : Fin n), ?_, ?_⟩, s, hZ_zt⟩
  · rintro ⟨i₁, h₁⟩ ⟨i₂, h₂⟩ heq
    obtain ⟨a₁, rfl⟩ := toLex.surjective i₁
    obtain ⟨a₂, rfl⟩ := toLex.surjective i₂
    rcases a₁ with i₁ | u₁ <;> rcases a₂ with i₂ | u₂
    · have := hcinj (show c ⟨i₁, h₁⟩ = c ⟨i₂, h₂⟩ from heq)
      exact Subtype.ext (congrArg (fun j => toLex (Sum.inl j)) (congrArg Subtype.val this))
    · exact absurd ⟨⟨i₁, h₁⟩, heq⟩ ht₀
    · exact absurd ⟨⟨i₂, h₂⟩, heq.symm⟩ ht₀
    · cases u₁; cases u₂; rfl
  · rintro ⟨i, hi⟩
    obtain ⟨a₀, rfl⟩ := toLex.surjective i
    rcases a₀ with i₀ | u
    · change (E.component i₀).stalkIdeal x = span {zt (c ⟨i₀, hi⟩)}
      rw [hzt_ne _ fun h => ht₀ ⟨⟨i₀, hi⟩, h⟩]
      exact hcEz ⟨i₀, hi⟩
    · change J.stalkIdeal x = span {zt t₀}
      rw [hzt_t₀]; exact hJg

end AlgebraicGeometry
