import Hironaka.Geometry.CartierBoundarySectionComponents
import Hironaka.Geometry.CartierBoundarySectionDescent

/-!
# Select and descend the actual sections, then cover every boundary component

The componentwise generic dominance here is consumed by the final theorem
from the actual Cartier dimension producer. It is not a hypothesis of the
final boundary splitting theorem.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hironaka.Geometry.CartierBoundarySection

open Scheme.IdealSheafData CartierBoundaryComponentDimension

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Closed section images containing all the boundary-component generic points
cover the full actual support, even when the original boundary is not flat. -/
theorem exists_selected_sections {P T Y : Scheme.{u}} [IsIntegral Y]
    (r : P ⟶ Y) (j : T ⟶ P) [IsClosedImmersion j]
    (E : T.IdealSheafData)
    [∀ C : DivisorComponent E, IsDominant (componentInclusion E C ≫ (j ≫ r))]
    {ι : Type u} [Finite ι] (s : ι → (Y ⟶ P))
    (hs : ∀ i, s i ≫ r = 𝟙 Y) (hclosed : ∀ i, IsClosedImmersion (s i))
    (hboundary : ∀ (i : ι) (y : Y) (t : T), j t = s i y → t ∈ E.support)
    (hgeneric : ∀ t : T, t ∈ E.support → (j ≫ r) t = genericPoint Y →
      ∃ i : ι, s i (genericPoint Y) = j t) :
    ∃ (κ : Type u) (_ : Finite κ) (σ : κ → (Y ⟶ T)),
      (∀ a, σ a ≫ (j ≫ r) = 𝟙 Y ∧ IsClosedImmersion (σ a)) ∧
      ⋃ a, Set.range (σ a) = (E.support : Set T) := by
  let κ := {i : ι // s i (genericPoint Y) ∈ Set.range j}
  let σ : κ → (Y ⟶ T) := fun a => closedLift j (s a.val) a.property
  have hfac (a : κ) : σ a ≫ j = s a.val := closedLift_fac _ _ _
  have hσclosed (a : κ) : IsClosedImmersion (σ a) := by
    let : IsClosedImmersion (σ a ≫ j) := by rw [hfac]; exact hclosed a.val
    exact IsClosedImmersion.of_comp (σ a) j
  let (a : κ) : IsClosedImmersion (σ a) := hσclosed a
  have hσsupport (a : κ) (y : Y) : σ a y ∈ E.support := by
    apply hboundary a.val y (σ a y)
    exact congrArg (fun h => h y) (hfac a)
  refine ⟨κ, inferInstance, σ, (fun a => ⟨?_, hσclosed a⟩), ?_⟩
  · rw [← Category.assoc, hfac, hs]
  · apply Set.Subset.antisymm
    · rintro t ht
      obtain ⟨a, y, rfl⟩ := Set.mem_iUnion.mp ht
      exact hσsupport a y
    · intro t ht
      obtain ⟨C, c, hc⟩ := components_cover E t ht
      let z := componentInclusion E C (genericPoint (componentScheme E C))
      have hz : z ∈ E.support := by
        apply SNCSubdivisorComponent.component_le_support E C
        exact (range_subschemeι (vanishingIdeal C.val)).subset ⟨_, rfl⟩
      have hzg : (j ≫ r) z = genericPoint Y :=
        genericPoint_map_of_isDominant (componentInclusion E C ≫ (j ≫ r))
      obtain ⟨i, hi⟩ := hgeneric z hz hzg
      let a : κ := ⟨i, ⟨z, hi.symm⟩⟩
      have hσz : σ a (genericPoint Y) = z := by
        apply j.isClosedEmbedding.injective
        calc
          j (σ a (genericPoint Y)) = s i (genericPoint Y) :=
            congrArg (fun h => h (genericPoint Y)) (hfac a)
          _ = j z := hi
      have hcontains : closure ({z} : Set T) ⊆ Set.range (σ a) := by
        apply (σ a).isClosedEmbedding.isClosed_range.closure_subset_iff.mpr
        exact Set.singleton_subset_iff.mpr ⟨genericPoint Y, hσz⟩
      have hCclosure : closure ({z} : Set T) = (C.val : Set T) := component_genericPoint E C
      rw [hCclosure] at hcontains
      apply Set.mem_iUnion.mpr
      refine ⟨a, hcontains ?_⟩
      rw [← hc]
      exact (range_subschemeι (vanishingIdeal C.val)).subset ⟨c, rfl⟩

end Hironaka.Geometry.CartierBoundarySection
