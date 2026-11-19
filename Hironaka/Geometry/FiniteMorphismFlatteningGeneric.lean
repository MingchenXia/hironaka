import Hironaka.Geometry.FiniteMorphismFlatteningLocality
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# The canonical fraction-field model of the native generic point

The actual fraction field is identified with the native generic residue
field using the original coefficient map and actual generic stalk.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Hironaka.Geometry.FiniteMorphismFlattening

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : CommRingCat.{u}) [IsDomain R]

/-- The native generic residue map is an isomorphism because the actual generic stalk is a field. -/
def genericResidueIso : (Spec R).functionField ≅
    (Spec R).residueField (genericPoint (Spec R)) := by
  let : IsIso ((Spec R).residue (genericPoint (Spec R))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨((Spec R).residue (genericPoint (Spec R))).hom.injective,
        IsLocalRing.residue_surjective⟩
  exact asIso ((Spec R).residue (genericPoint (Spec R)))

/-- The canonical fraction field and native generic residue field are identified through the original stalk. -/
def fractionGenericResidueIso : CommRingCat.of (FractionRing R) ≅
    (Spec R).residueField (genericPoint (Spec R)) :=
  (IsLocalization.algEquiv (nonZeroDivisors R) (FractionRing R)
    (Spec R).functionField).toRingEquiv.toCommRingCatIso ≪≫ genericResidueIso R

/-- The actual fraction-field point map is literally the native generic-point map through this isomorphism. -/
theorem fractionGenericResidueIso_structure :
    Spec.map (fractionGenericResidueIso R).inv ≫
      (Spec R).fromSpecResidueField (genericPoint (Spec R)) =
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) := by
  rw [Scheme.fromSpecResidueField, Spec.fromSpecStalk_eq,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  let e := IsLocalization.algEquiv (nonZeroDivisors R) (FractionRing R) (Spec R).functionField
  change (StructureSheaf.toStalk R _ ≫ (genericResidueIso R).hom) ≫
    ((genericResidueIso R).inv ≫ e.toRingEquiv.toCommRingCatIso.inv) = _
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  apply CommRingCat.hom_ext
  exact e.symm.toAlgHom.comp_algebraMap

end Hironaka.Geometry.FiniteMorphismFlattening
