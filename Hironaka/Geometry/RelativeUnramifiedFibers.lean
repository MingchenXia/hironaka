import Hironaka.Algebra.RelativeUnramifiedClosedFiberQuotient
import Hironaka.Geometry.NodeCompletedLocalFiberFieldSection
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-! # Formal unramifiedness from the ACTUAL original scheme fibres

The finite-type hypothesis is on the original morphism. No Noetherian base,
flatness, integrality, node model or residue separability is required.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace Hironaka.Geometry.RelativeUnramified
open NodeCompletedLocalMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S)
attribute [local instance] NodeCompletedLocalMap.originalAlgebra

/-- The actual original quotient-fibre coefficient map is unramified from the actual fibre. -/
theorem quotientClosedFiber_formallyUnramified (x : X)
    [FormallyUnramified (f.fiberToSpecResidueField (f x))] :
    letI : Algebra (S.residueField (f x)) (OriginalFiberRing f x) :=
      originalFiberResidueAlgebra f x
    Algebra.FormallyUnramified (S.residueField (f x)) (OriginalFiberRing f x) := by
  let : IsPreimmersion (originalFiberMap f x) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion)
      (originalFiberMap_isPullback f x).flip inferInstance
  let : FormallyUnramified (originalFiberMap f x) := inferInstance
  have h : FormallyUnramified
      (originalFiberMap f x ≫ f.fiberToSpecResidueField (f x)) :=
    MorphismProperty.comp_mem _ _ _ inferInstance inferInstance
  rw [originalFiberMap_residue, originalFiberToPointResidue_eq] at h
  exact (HasRingHomProperty.Spec_iff (P := @FormallyUnramified)).mp h

/-- Native formal unramifiedness of EVERY actual residue fibre implies it for the SAME original map. -/
theorem formallyUnramified_of_fibers [LocallyOfFiniteType f]
    (hf : ∀ s : S, FormallyUnramified (f.fiberToSpecResidueField s)) :
    FormallyUnramified f := by
  apply HasRingHomProperty.of_stalkMap (P := @FormallyUnramified)
    RingHom.FormallyUnramified.ofLocalizationPrime
  intro x
  let : IsLocalHom (algebraMap (S.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs <| IsLocalHom (f.stalkMap x).hom
  let : Algebra.EssFiniteType (S.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap f x
  let : FormallyUnramified (f.fiberToSpecResidueField (f x)) := hf (f x)
  have h := Algebra.RelativeUnramified.formallyUnramified_of_closedFiber
    (S.presheaf.stalk (f x)) (X.presheaf.stalk x)
    (quotientClosedFiber_formallyUnramified f x)
  rwa [← RingHom.formallyUnramified_algebraMap, RingHom.algebraMap_toAlgebra] at h

end Hironaka.Geometry.RelativeUnramified
