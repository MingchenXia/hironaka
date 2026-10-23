import DeJongAlterations.Geometry.GenericFiberIntegral
import DeJongAlterations.Geometry.NormalizationInExtensionFunctionField

/-!
# The actual canonical function field of a native generic fibre

The map is the one induced by the original fibre inclusion. Dominance,
stalk isomorphisms and the field isomorphism are all proved internally.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.GenericFiberFunctionField

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X S : Scheme.{u}} [IsIntegral X] [IsIntegral S]
  (f : X ⟶ S) [IsDominant f]

/-- The actual generic-fibre inclusion has a range containing the source generic point. -/
theorem genericFiberι_isDominant : IsDominant (f.fiberι (genericPoint S)) := by
  let z : f.fiber (genericPoint S) := (f.fiberHomeo (genericPoint S)).symm
    ⟨genericPoint X, genericPoint_map_of_isDominant f⟩
  have hz : f.fiberι (genericPoint S) z = genericPoint X := f.fiberι_fiberHomeo_symm _ _
  have hr : closure ({genericPoint X} : Set X) ⊆
      closure (Set.range (f.fiberι (genericPoint S))) :=
    closure_mono (Set.singleton_subset_iff.mpr ⟨z, hz⟩)
  rw [(genericPoint_spec X).def] at hr
  constructor
  intro x
  exact hr (Set.mem_univ x)

/-- The actual generic-fibre inclusion induces an isomorphism on its canonical function fields. -/
theorem functionFieldMap_isIso :
    letI := GenericFiberIntegral.genericFiber_isIntegral f
    letI := genericFiberι_isDominant f
    IsIso (NormalizationInExtension.functionFieldMap (f.fiberι (genericPoint S))) := by
  let := GenericFiberIntegral.genericFiber_isIntegral f
  let := genericFiberι_isDominant f
  let : Flat (S.fromSpecResidueField (genericPoint S)) :=
    GenericFiberIntegral.fromSpecResidueField_flat S
  let : Flat (f.fiberι (genericPoint S)) := by
    change Flat (CategoryTheory.Limits.pullback.fst _ _)
    infer_instance
  let : IsIso ((f.fiberι (genericPoint S)).stalkMap
      (genericPoint (f.fiber (genericPoint S)))) :=
    GenericFiberIntegral.stalkMap_isIso_of_flat_preimmersion _ _
  dsimp only [NormalizationInExtension.functionFieldMap]
  infer_instance

/-- The actual original-inclusion field map, equipped with its proved native inverse. -/
def functionFieldIso :
    letI := GenericFiberIntegral.genericFiber_isIntegral f
    X.functionField ≅ (f.fiber (genericPoint S)).functionField := by
  let := GenericFiberIntegral.genericFiber_isIntegral f
  let := genericFiberι_isDominant f
  let := functionFieldMap_isIso f
  exact asIso (NormalizationInExtension.functionFieldMap (f.fiberι (genericPoint S)))

end DeJongAlterations.Geometry.GenericFiberFunctionField
