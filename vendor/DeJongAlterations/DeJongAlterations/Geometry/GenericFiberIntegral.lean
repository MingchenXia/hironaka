import DeJongAlterations.Composition
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Integrality of actual generic fibres

The fibre is the native scheme-theoretic fibre at the actual generic point.
No finite-type, affine presentation or integral-fibre certificate is required.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.GenericFiberIntegral

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{u}}

/-- Flat preimmersions induce actual isomorphisms on all local rings. -/
theorem stalkMap_isIso_of_flat_preimmersion (f : X ⟶ Y)
    [Flat f] [IsPreimmersion f] (x : X) : IsIso (f.stalkMap x) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨?_, f.stalkMap_surjective x⟩
  algebraize [(f.stalkMap x).hom]
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap f x) (f.toLRSHom.prop x)
  exact ‹RingHom.FaithfullyFlat (f.stalkMap x).hom›.injective

/-- Reducedness transfers through the actual local-ring isomorphisms. -/
theorem isReduced_of_flat_preimmersion (f : X ⟶ Y)
    [Flat f] [IsPreimmersion f] [IsReduced Y] : IsReduced X := by
  let : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    let : IsIso (f.stalkMap x) := stalkMap_isIso_of_flat_preimmersion f x
    exact isReduced_of_injective (inv (f.stalkMap x)).hom
      (ConcreteCategory.bijective_of_isIso (inv (f.stalkMap x))).1
  exact isReduced_of_isReduced_stalk X

/-- The actual point morphism at an integral scheme's generic point is flat. -/
theorem fromSpecResidueField_flat (Y : Scheme.{u}) [IsIntegral Y] :
    Flat (Y.fromSpecResidueField (genericPoint Y)) := by
  apply (Flat.iff_flat_stalkMap _).mpr
  intro x
  have hfield : IsField
      (Y.presheaf.stalk ((Y.fromSpecResidueField (genericPoint Y)) x)) := by
    rw [Scheme.fromSpecResidueField_apply]
    exact Field.toIsField Y.functionField
  let : Field (Y.presheaf.stalk ((Y.fromSpecResidueField (genericPoint Y)) x)) :=
    hfield.toField
  algebraize [((Y.fromSpecResidueField (genericPoint Y)).stalkMap x).hom]
  change Module.Flat _ _
  infer_instance

/-- The actual generic fibre has reduced local rings, without dominance. -/
theorem genericFiber_isReduced (f : X ⟶ Y) [IsReduced X] [IsIntegral Y] :
    IsReduced (f.fiber (genericPoint Y)) := by
  let : Flat (Y.fromSpecResidueField (genericPoint Y)) := fromSpecResidueField_flat Y
  let : Flat (f.fiberι (genericPoint Y)) := by
    change Flat (CategoryTheory.Limits.pullback.fst _ _)
    infer_instance
  exact isReduced_of_flat_preimmersion (f.fiberι (genericPoint Y))

/-- Every dominant morphism of integral schemes has an actual integral generic fibre. -/
theorem genericFiber_isIntegral (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsDominant f] :
    IsIntegral (f.fiber (genericPoint Y)) := by
  let z : f.fiber (genericPoint Y) := (f.fiberHomeo (genericPoint Y)).symm
    ⟨genericPoint X, genericPoint_map_of_isDominant f⟩
  have hz : f.fiberι (genericPoint Y) z = genericPoint X :=
    f.fiberι_fiberHomeo_symm _ _
  have hg : IsGenericPoint z (Set.univ : Set (f.fiber (genericPoint Y))) := by
    rw [isGenericPoint_iff_specializes]
    intro x
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    apply (f.fiberι (genericPoint Y)).isEmbedding.isInducing.specializes_iff.mp
    rw [hz]
    exact (genericPoint_spec X).specializes (Set.mem_univ _)
  let : IrreducibleSpace (f.fiber (genericPoint Y)) :=
    (irreducibleSpace_def _).mpr hg.isIrreducible
  let : IsReduced (f.fiber (genericPoint Y)) := genericFiber_isReduced f
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end DeJongAlterations.Geometry.GenericFiberIntegral
