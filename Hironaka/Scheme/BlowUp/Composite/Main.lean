/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.Composite
public import Hironaka.Scheme.BlowUp.Composite.Descend
import Hironaka.Scheme.BlowUp.Composite.Bound
import Hironaka.Scheme.BlowUp.Glue.GlobalCharts
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Hironaka's `J(m)`: `K_m.comap b = J' · E^m` for `m` large

For `X` Noetherian there is `m₀` such that for all `m ≥ m₀` the inverse image of Hironaka's
descended centre `K_m = I^m ⊓ (J' · E^m).map b` along the blow-up map is `J' · E^m`
(`exists_comap_descendCenter_eq`): the existence of the coherent ideal `J(m)` with
`f₀⁻¹(J(m)) = f₀⁻¹(J₀)^m J₁` [Hir64, Ch. 0, §3, p. 133]; [Sta, Tag 080B].  The inequality `≤` is
the Galois connection (`comap_descendCenter_le`); `≥` is checked on the charts of finitely many
affine opens `U` of `X` (quasi-compactness) and finitely many generators `c` of each `I(U)`
(Noetherian), where it is the chart-level inequality of `Hironaka.Scheme.BlowUp.Composite.Bound`
with `m ≥ m₀(U, c)`, and `m₀` is the maximum of the finitely many `m₀(U, c)`.  The intrinsic
definition of `K_m` needs no gluing of local pieces.  `Hironaka.Scheme.BlowUp.Composite.Iso` turns
the equality into the isomorphism of blow-ups.
-/

public section

namespace AlgebraicGeometry

open Scheme.IdealSheafData

open AlgebraicGeometry CategoryTheory Scheme.IdealSheafData TopologicalSpace

universe u

section Cover

variable {X : Scheme.{u}}

/-- A quasi-compact scheme is covered by finitely many affine opens. -/
theorem exists_finset_affineOpens_iSup_eq_top [CompactSpace X] :
    ∃ 𝒰 : Finset X.affineOpens, ⨆ U ∈ 𝒰, (U : X.Opens) = ⊤ := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U.1 : Set X))
    (fun U => U.1.2) (fun x _ => by
      obtain ⟨U, hU⟩ := exists_affineOpens_mem x
      exact Set.mem_iUnion.mpr ⟨U, hU⟩)
  refine ⟨t, eq_top_iff.mpr fun x _ => ?_⟩
  obtain ⟨U, hU, hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  exact Opens.mem_iSup.mpr ⟨U, Opens.mem_iSup.mpr ⟨hU, hx⟩⟩

/-- A finite generating set of an ideal of `Γ(X, U)`, `X` locally Noetherian, as a finite set of
elements of the ideal. -/
theorem exists_finset_span_eq [IsLocallyNoetherian X] (I : X.IdealSheafData) (U : X.affineOpens) :
    ∃ s : Finset (I.ideal U), Ideal.span (Subtype.val '' (s : Set (I.ideal U))) = I.ideal U := by
  have := IsLocallyNoetherian.component_noetherian U
  obtain ⟨t, ht⟩ := IsNoetherian.noetherian (I.ideal U)
  have hsub : (t : Set Γ(X, U)) ⊆ I.ideal U := fun x hx => ht ▸ Ideal.subset_span hx
  have hfin : (Subtype.val ⁻¹' (t : Set Γ(X, U)) : Set (I.ideal U)).Finite :=
    t.finite_toSet.preimage Subtype.val_injective.injOn
  refine ⟨hfin.toFinset, ?_⟩
  rw [Set.Finite.coe_toFinset, Set.image_preimage_eq_of_subset]
  · exact ht
  · intro x hx
    exact ⟨⟨x, hsub hx⟩, rfl⟩

end Cover

section Main

variable {X : Scheme.{u}} (I : X.IdealSheafData) (J' : (blowUp I).IdealSheafData)
  (U : X.affineOpens) (c : I.ideal U)

/-- Membership in `L(chart c ''ᵁ ⊤)`, read on the affine open `⊤` of the chart. -/
theorem mem_ideal_chartOpen_iff (L : (blowUp I).IdealSheafData)
    (w : Γ(blowUp I, chartOpen I U c)) :
    w ∈ L.ideal (chartOpen I U c) ↔
      ((blowUp.chart I U c).appIso ⊤).hom w ∈
        (L.comap (blowUp.chart I U c)).ideal ⟨⊤, isAffineOpen_top _⟩ :=
  (Eq.to_iff (congrArg (fun v => v ∈ L.ideal (chartOpen I U c))
    (Iso.hom_inv_id_apply ((blowUp.chart I U c).appIso ⊤) w).symm)).trans
    (SetLike.ext_iff.mp
      (ideal_comap_of_isOpenImmersion L (blowUp.chart I U c) ⟨⊤, isAffineOpen_top _⟩) _).symm

/-- An inequality of ideal sheaves on the blow-up, pulled back along the chart of `c`, gives the
inequality of their ideals on the affine open `chart c ''ᵁ ⊤`. -/
theorem ideal_chartOpen_le_of_comap_le {L L' : (blowUp I).IdealSheafData}
    (h : L.comap (blowUp.chart I U c) ≤ L'.comap (blowUp.chart I U c)) :
    L.ideal (chartOpen I U c) ≤ L'.ideal (chartOpen I U c) := fun w hw =>
  (mem_ideal_chartOpen_iff I U c L' w).mpr
    (le_def.mp h ⟨⊤, isAffineOpen_top _⟩ ((mem_ideal_chartOpen_iff I U c L w).mp hw))

/-- The chart-level inequality of `Hironaka.Scheme.BlowUp.Composite.Bound` as an inequality of the
pulled-back ideal sheaves. -/
theorem comap_chart_le_of_ideal_le (m : ℕ)
    (h : chartIdeal I J' U c *
        Ideal.span {algebraMap Γ(X, U) (affineBlowUpAlgebra (I.ideal U) c) c} ^ m ≤
      ((descendCenter I J' m).ideal U).map
        (algebraMap Γ(X, U) (affineBlowUpAlgebra (I.ideal U) c))) :
    (J' * I.exceptionalDivisor ^ m).comap (blowUp.chart I U c) ≤
      ((descendCenter I J' m).comap (blowUpπ I)).comap (blowUp.chart I U c) := by
  rw [comap_mul_pow_chart, comap_comap_chart, specIdealSheaf_le_iff]
  exact h

/-- **Hironaka's `J(m)`** [Hir64, Ch. 0, §3, p. 133]; [Sta, Tag 080B]: for `X` Noetherian there
is `m₀` such that for all `m ≥ m₀`, `K_m.comap b = J' · E^m`. -/
theorem exists_comap_descendCenter_eq [IsNoetherian X] :
    ∃ m₀ : ℕ, ∀ m, m₀ ≤ m →
      (descendCenter I J' m).comap (blowUpπ I) = J' * I.exceptionalDivisor ^ m := by
  obtain ⟨𝒰, h𝒰⟩ := exists_finset_affineOpens_iSup_eq_top (X := X)
  choose s hs using exists_finset_span_eq I
  choose m₀ hm₀ using fun p : Σ V : 𝒰, s V.1 =>
    exists_chartIdeal_mul_pow_le I J' p.1.1 (s p.1.1) (hs p.1.1) p.2.1
  obtain ⟨M, hM⟩ := Finite.exists_le m₀
  refine ⟨M, fun m hm => le_antisymm (comap_descendCenter_le I J' m) ?_⟩
  have hcov : ⨆ p : Σ V : 𝒰, s V.1, (chartOpen I p.1.1 p.2.1).1 = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hy : blowUpπ I y ∈ ⨆ V ∈ 𝒰, (V : X.Opens) := by rw [h𝒰]; exact Opens.mem_top _
    obtain ⟨V, hV⟩ := Opens.mem_iSup.mp hy
    obtain ⟨hV𝒰, hyV⟩ := Opens.mem_iSup.mp hV
    have hy' : y ∈ ⋃ a ∈ (s V : Set (I.ideal V)), Set.range (blowUp.chart I V a) := by
      rw [blowUp.iUnion_range_chart_of_span_eq I V _ (hs V)]
      exact hyV
    obtain ⟨a, ha, z, rfl⟩ := Set.mem_iUnion₂.mp hy'
    refine Opens.mem_iSup.mpr ⟨⟨⟨V, hV𝒰⟩, ⟨a, ha⟩⟩, ?_⟩
    change blowUp.chart I V a z ∈ blowUp.chart I V a ''ᵁ ⊤
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact Scheme.Hom.mem_opensRange.mpr ⟨z, rfl⟩
  exact le_of_iSup_eq_top (fun p : Σ V : 𝒰, s V.1 => chartOpen I p.1.1 p.2.1) hcov fun p =>
    ideal_chartOpen_le_of_comap_le I p.1.1 p.2.1
      (comap_chart_le_of_ideal_le I J' p.1.1 p.2.1 m (hm₀ p m ((hM p).trans hm)))

end Main

end AlgebraicGeometry
