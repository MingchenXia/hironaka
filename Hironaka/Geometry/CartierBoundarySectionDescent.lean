import Hironaka.Geometry.CartierBoundaryAlteredModel

/-!
# Closed section descent and componentwise coverage

An actual closed immersion admits a genuine lift from a reduced source
whenever the whole set-theoretic image lands in it. Generic landing from
an integral source is enough. No flatness or openness is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hironaka.Geometry.CartierBoundarySection

open Scheme.IdealSheafData CartierBoundaryComponentDimension

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {P T Y : Scheme.{u}}

/-- Closed landing of an actual generic point spreads to the full integral source. -/
theorem range_subset_of_generic_mem [IsIntegral Y] (j : T ⟶ P) [IsClosedImmersion j]
    (σ : Y ⟶ P) (hσ : σ (genericPoint Y) ∈ Set.range j) : Set.range σ ⊆ Set.range j := by
  have hclosed : IsClosed (σ ⁻¹' Set.range j) :=
    j.isClosedEmbedding.isClosed_range.preimage σ.continuous
  have hcl : closure ({genericPoint Y} : Set Y) ⊆ σ ⁻¹' Set.range j :=
    hclosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hσ)
  rw [genericPoint_closure] at hcl
  rintro _ ⟨y, rfl⟩
  exact hcl (Set.mem_univ y)

/-- The actual base-change closed immersion is an isomorphism, by reducedness. -/
theorem closedPullback_isIso [IsReduced Y] (j : T ⟶ P) [IsClosedImmersion j]
    (σ : Y ⟶ P) (hσ : Set.range σ ⊆ Set.range j) : IsIso (pullback.fst σ j) := by
  let : Surjective (pullback.fst σ j) := ⟨by
    intro y
    obtain ⟨t, ht⟩ := hσ ⟨y, rfl⟩
    obtain ⟨w, hw, _⟩ := Scheme.Pullback.exists_preimage_pullback y t ht.symm
    exact ⟨w, hw⟩⟩
  exact isIso_of_isClosedImmersion_of_surjective _

/-- A literal factor through the original closed immersion. -/
def closedLift [IsIntegral Y] (j : T ⟶ P) [IsClosedImmersion j]
    (σ : Y ⟶ P) (hσ : σ (genericPoint Y) ∈ Set.range j) : Y ⟶ T :=
  letI := closedPullback_isIso j σ (range_subset_of_generic_mem j σ hσ)
  inv (pullback.fst σ j) ≫ pullback.snd σ j

@[reassoc (attr := simp)]
theorem closedLift_fac [IsIntegral Y] (j : T ⟶ P) [IsClosedImmersion j]
    (σ : Y ⟶ P) (hσ : σ (genericPoint Y) ∈ Set.range j) : closedLift j σ hσ ≫ j = σ := by
  let := closedPullback_isIso j σ (range_subset_of_generic_mem j σ hσ)
  dsimp only [closedLift]
  rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]

/-- A dominant morphism sends the actual integral generic point to the target generic point. -/
theorem dominant_genericPoint {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (f : A ⟶ B) [IsDominant f] : f (genericPoint A) = genericPoint B :=
  genericPoint_map_of_isDominant f

/-- The actual generic point of a native reduced Cartier component has precisely that closure. -/
theorem component_genericPoint (E : T.IdealSheafData) (C : DivisorComponent E) :
    IsGenericPoint (componentInclusion E C (genericPoint (componentScheme E C)))
      (C.val : Set T) := by
  have h := (genericPoint_spec (componentScheme E C)).image (componentInclusion E C).continuous
  have hr : Set.range (componentInclusion E C) = (C.val : Set T) := range_subschemeι _
  rw [Set.image_univ, hr, C.val.isClosed.closure_eq] at h
  exact h

end Hironaka.Geometry.CartierBoundarySection
