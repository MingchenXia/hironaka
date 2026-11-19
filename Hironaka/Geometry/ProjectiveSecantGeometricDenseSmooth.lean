import Hironaka.Geometry.ProjectiveSecantGeometricGenericSmooth
import Hironaka.Geometry.ProjectiveSecantOriginalComponents
import Hironaka.Geometry.ProjectiveSecantProjectionComponentBirational

/-!
# The original dense geometrically reduced open produces the exact original dense smooth locus
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.ProjectiveSecant

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The paper's actual original dense geometrically reduced open internally supplies dense smoothness of the same arbitrary original closed projective source, retaining all components and nilpotents. -/
theorem original_dense_smoothLocus_of_dense_geometricallyReduced_open
    (k : Type u) [Field k] (m : ℕ) {X : Scheme.{u}}
    (i : X ⟶ projectiveSpace k m) [IsClosedImmersion i]
    (U : X.Opens) (hU : Dense (U : Set X))
    [GeometricallyReduced (U.ι ≫ (i ≫ projectiveSpaceStructure k m))] :
    Dense ((i ≫ projectiveSpaceStructure k m).smoothLocus : Set X) := by
  apply original_open_dense_of_meets_components
  intro C hC
  let W := originalComponentGeometricOpen k m i C hC U
  let : IsIntegral W := originalComponentGeometricOpen_isIntegral k m i C hC U hU
  let : GeometricallyReduced (W.ι ≫ (i ≫ projectiveSpaceStructure k m)) :=
    originalComponentGeometricOpen_geometricallyReduced k m i C hC U
  have hpoint := genericPoint_mem_smoothLocus_of_geometricallyReduced
    (W.ι ≫ (i ≫ projectiveSpaceStructure k m))
  rw [← Scheme.Hom.preimage_smoothLocus_eq, Scheme.Hom.mem_preimage] at hpoint
  exact ⟨W.ι (genericPoint W), originalComponentGeometricOpen_subset_component k m i C hC U
    (genericPoint W).2, hpoint⟩

end Hironaka.Geometry.ProjectiveSecant
