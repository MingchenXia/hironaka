import Hironaka.Algebra.CompletionFlatMap
import Hironaka.Algebra.NodeEtaleFlat

/-! The actual point residue extension transported through literal local completion. -/

noncomputable section

open IsLocalRing

namespace Hironaka.Algebra.NodeGeometricCompletion

open CompletionRegularityBasics CompletionLocalMap CompletionFlatMap

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable (A B : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
  [IsNoetherianRing A] [IsNoetherianRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)]

attribute [local instance] CompletionFlatMap.completedAlgebra

local instance completionAlgebra_local :
    IsLocalHom (algebraMap (Completion A) (Completion B)) :=
  isLocalHom_completionMap (algebraMap A B)

/-- The exact residue action of the literal induced completed local map. -/
@[instance_reducible]
def completedResidueAlgebra : Algebra (ResidueField (Completion A)) (ResidueField (Completion B)) :=
  inferInstance

/-- The actual native residue maps form the original coefficient square. -/
theorem completedResidue_triangle :
    (ResidueField.map (completionMap (algebraMap A B))).comp
      (residueFieldEquiv A).toRingHom =
        (residueFieldEquiv B).toRingHom.comp (algebraMap (ResidueField A) (ResidueField B)) := by
  change (ResidueField.map (completionMap (algebraMap A B))).comp
      (ResidueField.map (algebraMap A (Completion A))) =
        (ResidueField.map (algebraMap B (Completion B))).comp
          (ResidueField.map (algebraMap A B))
  rw [← ResidueField.map_comp, ← ResidueField.map_comp]
  congr 1

/-- Original canonical finite residue degree gives finite degree for the actual completed map. -/
theorem completedResidue_finite [FiniteDimensional (ResidueField A) (ResidueField B)] :
    letI := completedResidueAlgebra A B
    FiniteDimensional (ResidueField (Completion A)) (ResidueField (Completion B)) := by
  let := completedResidueAlgebra A B
  exact Module.Finite.of_equiv_equiv (residueFieldEquiv A) (residueFieldEquiv B)
    (completedResidue_triangle A B)

/-- Original canonical residue separability gives separability for the exact completed action. -/
theorem completedResidue_separable [Algebra.IsSeparable (ResidueField A) (ResidueField B)] :
    letI := completedResidueAlgebra A B
    Algebra.IsSeparable (ResidueField (Completion A)) (ResidueField (Completion B)) := by
  let := completedResidueAlgebra A B
  exact Algebra.IsSeparable.of_equiv_equiv (residueFieldEquiv A) (residueFieldEquiv B)
    (completedResidue_triangle A B)

end Hironaka.Algebra.NodeGeometricCompletion
