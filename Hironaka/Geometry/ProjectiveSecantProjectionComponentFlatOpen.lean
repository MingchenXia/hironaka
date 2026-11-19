import Hironaka.Geometry.ProjectiveSecantProjectionComponentUnramified
import Hironaka.Geometry.FiniteBirationalNormalReducedComponents
import Hironaka.Geometry.FiniteVarietyDominance

/-!
# Original component dimensions internally produce actual dominance and dense flat-open preimages
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.ProjectiveSecant

open FiniteBirationalNormal

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual original component dimension internally forces dominance of its internally constructed native reduced component map. -/
theorem actual_componentMap_isDominant_of_dimension_le
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of k)) [IsVariety p] (f : X ⟶ Y) [IsFinite f]
    (C : irreducibleComponents X) (hdim : topologicalKrullDim Y ≤ topologicalKrullDim C.val) :
    IsDominant (reducedComponentInclusion X C ≫ f) := by
  apply FiniteVarietyDominance.isDominant_of_dimension_le p
  exact hdim

/-- Every actual nonempty original target open has dense preimage under the unchanged original finite map, from original component dimensions alone. -/
theorem dense_preimage_open_of_component_dimensions
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of k)) [IsVariety p] (f : X ⟶ Y) [IsFinite f]
    (hdim : ∀ C ∈ irreducibleComponents X, topologicalKrullDim Y ≤ topologicalKrullDim C)
    (V : Y.Opens) (hV : (V : Set Y).Nonempty) : Dense (f ⁻¹ᵁ V : Set X) := by
  have hηV : genericPoint Y ∈ V := (genericPoint_spec Y).mem_open_set_iff V.isOpen |>.mpr (by simpa using hV)
  apply original_open_dense_of_meets_components
  intro C hC
  let c : irreducibleComponents X := ⟨C, hC⟩
  let j := reducedComponentInclusion X c
  let : IsDominant (j ≫ f) := actual_componentMap_isDominant_of_dimension_le p f c (hdim C hC)
  let x := genericPoint (reducedComponent X c)
  refine ⟨j x, ?_, ?_⟩
  · have hx : j x ∈ Set.range (reducedComponentInclusion X c) := ⟨x, rfl⟩
    rwa [reducedComponentInclusion_range c] at hx
  · change (j ≫ f) x ∈ V
    rw [genericPoint_map_of_isDominant (j ≫ f)]
    exact hηV

end Hironaka.Geometry.ProjectiveSecant
