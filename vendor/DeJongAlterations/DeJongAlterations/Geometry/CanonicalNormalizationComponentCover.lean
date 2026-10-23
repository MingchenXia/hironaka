/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.Geometry.CanonicalNormalizationInclusion

/-! # The actual whole normalization is covered by its same canonical singleton pieces -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

namespace DeJongAlterations.Geometry.CanonicalNormalization

universe u

open StableModification.CurvesField StableModification.CurvesField.Genus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {T : Scheme.{u}} [IsAffineHom (pullback.diagonal (terminal.from T))]
  [Finite (genericPoints T)]

/-- The SAME original canonical singleton normalization, indexed by actual generic points. -/
abbrev component (η : genericPoints T) := normalizationPoints ({η.1} : Set T)

/-- The actual native inclusion of the SAME original canonical singleton piece. -/
abbrev componentIncl (η : genericPoints T) : component η ⟶ normalizationPoints (genericPoints T) :=
  normalizationPointsIncl (Set.singleton_subset_iff.mpr η.2)

instance (η : genericPoints T) : IsIntegral (component η) := inferInstance

instance (η : genericPoints T) : IsOpenImmersion (componentIncl η) := inferInstance

instance (η : genericPoints T) : IsFinite (componentIncl η) := inferInstance

instance (η : genericPoints T) : IsClosedImmersion (componentIncl η) := inferInstance

@[reassoc (attr := simp)]
theorem componentIncl_fromNormalization (η : genericPoints T) :
    componentIncl η ≫ normalizationPointsMap (genericPoints T) =
      normalizationPointsMap ({η.1} : Set T) := normalizationPointsIncl_fromNormalization _

@[reassoc (attr := simp)]
theorem componentIncl_toNormalization (η : genericPoints T) :
    (pointsMap T ({η.1} : Set T)).toNormalization ≫ componentIncl η =
      pointsIncl (Set.singleton_subset_iff.mpr η.2) ≫
        (pointsMap T (genericPoints T)).toNormalization := toNormalization_normalizationPointsIncl _

/-- Pairwise disjointness is derived from the actual dense original point scheme. -/
theorem pairwise_disjoint_componentIncl :
    Pairwise (fun η ξ : genericPoints T => Disjoint (componentIncl η).opensRange
      (componentIncl ξ).opensRange) := by
  intro η ξ hne
  rw [disjoint_iff, eq_bot_iff]
  intro x hx
  obtain ⟨w, hzη, hzξ⟩ :=
    (pointsMap T (genericPoints T)).toNormalization.denseRange.exists_mem_open
      ((componentIncl η).opensRange ⊓ (componentIncl ξ).opensRange).isOpen ⟨x, hx⟩
  have hwhole : normalizationPointsMap (genericPoints T)
      ((pointsMap T (genericPoints T)).toNormalization w) = pointsMap T (genericPoints T) w := by
    change ((pointsMap T (genericPoints T)).toNormalization ≫
      (pointsMap T (genericPoints T)).fromNormalization) w = _
    rw [Scheme.Hom.toNormalization_fromNormalization]
  have hl (v : genericPoints T)
      (hv : (pointsMap T (genericPoints T)).toNormalization w ∈ (componentIncl v).opensRange) :
      v.1 = pointsMap T (genericPoints T) w := by
    obtain ⟨t, ht⟩ := hv
    have hc := StableModification.Omega.ComponentNormalization.normalizationPointsMap_mem_closure v.1 t
    rw [← componentIncl_fromNormalization v, Scheme.Hom.comp_apply, ht, hwhole] at hc
    exact eq_of_mem_closure_of_mem_genericPoints (pointsMap_mem w) hc
  exact hne (Subtype.ext ((hl η hzη).trans (hl ξ hzξ).symm))

/-- Their actual finite closed union contains the dense original point scheme and is the whole. -/
theorem iSup_componentIncl_opensRange :
    (⨆ η : genericPoints T, (componentIncl η).opensRange) = ⊤ := by
  have hc : IsClosed (⋃ η : genericPoints T, Set.range (componentIncl η)) :=
    isClosed_iUnion_of_finite fun η => (componentIncl η).isClosedMap.isClosed_range
  have hr : Set.range (pointsMap T (genericPoints T)).toNormalization ⊆
      ⋃ η : genericPoints T, Set.range (componentIncl η) := by
    rintro _ ⟨w, rfl⟩
    let η : genericPoints T := ⟨pointsMap T (genericPoints T) w, pointsMap_mem w⟩
    obtain ⟨t, ht⟩ := mem_range_pointsIncl (Set.singleton_subset_iff.mpr η.2) w
      (show pointsMap T (genericPoints T) w ∈ ({η.1} : Set T) from rfl)
    refine Set.mem_iUnion.mpr ⟨η, ?_⟩
    refine ⟨(pointsMap T ({η.1} : Set T)).toNormalization t, ?_⟩
    change ((pointsMap T ({η.1} : Set T)).toNormalization ≫ componentIncl η) t = _
    rw [componentIncl_toNormalization, Scheme.Hom.comp_apply, ht]
  have hall : Set.univ ⊆ ⋃ η : genericPoints T, Set.range (componentIncl η) := by
    rw [← (pointsMap T (genericPoints T)).toNormalization.denseRange.closure_range]
    exact closure_minimal hr hc
  apply top_unique
  intro x _
  obtain ⟨η, hx⟩ := Set.mem_iUnion.mp (hall (Set.mem_univ x))
  exact Opens.mem_iSup.mpr ⟨η, hx⟩

end DeJongAlterations.Geometry.CanonicalNormalization
