import Hironaka.Geometry.QuotGrassmannPivotImageRestriction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-!
# Actual over-site restriction preserves original native images

Limit preservation is proved through the original native open equivalence,
using the actual already proved open-immersion restriction theorem. No
exactness, image-preservation, or local-factorization certificate is an input.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

/-- The actual original over-site functor preserves limits, by its native open equivalence. -/
theorem originalOverFunctor_preservesLimits (X : Scheme.{u}) (U : X.Opens) :
    PreservesLimits (SheafOfModules.overFunctor.{u} X.ringCatSheaf U) := by
  let F := SheafOfModules.overFunctor.{u} X.ringCatSheaf U
  let E := (Scheme.Modules.overEquiv U).functor
  let := originalOpenRestriction_preservesLimits U.ι
  let : PreservesLimits (F ⋙ E) :=
    preservesLimits_of_natIso (Scheme.Modules.overFunctorEquiv U).symm
  exact preservesLimits_of_reflects_of_preserves F E

/-- The actual original over-site functor preserves colimits, through the same native open equivalence. -/
theorem originalOverFunctor_preservesColimits (X : Scheme.{u}) (U : X.Opens) :
    PreservesColimits (SheafOfModules.overFunctor.{u} X.ringCatSheaf U) := by
  let F := SheafOfModules.overFunctor.{u} X.ringCatSheaf U
  let : F.IsLeftAdjoint :=
    (SheafOfModules.overPushforwardOverAdj (R := X.ringCatSheaf) U).isLeftAdjoint
  infer_instance

private def originalOverFunctorAbelianImageIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [PreservesLimits F] [PreservesColimits F]
    {M N : C} (f : M ⟶ N) : F.obj (Abelian.image f) ≅ image (F.map f) :=
  F.mapIso (Abelian.imageIsoImage f) ≪≫ (PreservesImage.iso F f).symm

private theorem originalOverFunctorAbelianImageIso_inclusion
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [PreservesLimits F] [PreservesColimits F]
    {M N : C} (f : M ⟶ N) :
    (originalOverFunctorAbelianImageIso F f).hom ≫ image.ι (F.map f) =
      F.map (Abelian.image.ι f) := by
  change (F.map (Abelian.imageIsoImage f).hom ≫
    (PreservesImage.iso F f).inv) ≫ image.ι (F.map f) = _
  rw [Category.assoc, PreservesImage.inv_comp_image_ι_map, ← F.map_comp,
    Abelian.imageIsoImage_hom_comp_image_ι]

private theorem originalOverFunctorAbelianImageIso_factor
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [PreservesLimits F] [PreservesColimits F]
    {M N : C} (f : M ⟶ N) :
    F.map (Abelian.factorThruImage f) ≫ (originalOverFunctorAbelianImageIso F f).hom =
      factorThruImage (F.map f) := by
  apply (cancel_mono (image.ι (F.map f))).mp
  rw [Category.assoc, originalOverFunctorAbelianImageIso_inclusion,
    ← F.map_comp, Abelian.image.fac, image.fac]

/-- The actual original over-site restriction has its internally constructed native image iso. -/
def originalOverImageIso (X : Scheme.{u}) (U : X.Opens)
    {M N : X.Modules} (f : M ⟶ N) :
    (Abelian.image f).over U ≅
      image ((SheafOfModules.overFunctor.{u} X.ringCatSheaf U).map f) := by
  let := originalOverFunctor_preservesLimits X U
  let := originalOverFunctor_preservesColimits X U
  exact originalOverFunctorAbelianImageIso
    (SheafOfModules.overFunctor.{u} X.ringCatSheaf U) f

/-- The same produced over-site image comparison preserves the actual inclusion. -/
theorem originalOverImageIso_inclusion (X : Scheme.{u}) (U : X.Opens)
    {M N : X.Modules} (f : M ⟶ N) :
    (originalOverImageIso X U f).hom ≫
      image.ι ((SheafOfModules.overFunctor.{u} X.ringCatSheaf U).map f) =
        (SheafOfModules.overFunctor.{u} X.ringCatSheaf U).map (Abelian.image.ι f) := by
  let := originalOverFunctor_preservesLimits X U
  let := originalOverFunctor_preservesColimits X U
  exact originalOverFunctorAbelianImageIso_inclusion
    (SheafOfModules.overFunctor.{u} X.ringCatSheaf U) f

/-- The same actual original quotient-factor triangle holds under actual over-site restriction. -/
theorem originalOverImageIso_factor (X : Scheme.{u}) (U : X.Opens)
    {M N : X.Modules} (f : M ⟶ N) :
    (SheafOfModules.overFunctor.{u} X.ringCatSheaf U).map (Abelian.factorThruImage f) ≫
      (originalOverImageIso X U f).hom =
        factorThruImage ((SheafOfModules.overFunctor.{u} X.ringCatSheaf U).map f) := by
  let := originalOverFunctor_preservesLimits X U
  let := originalOverFunctor_preservesColimits X U
  exact originalOverFunctorAbelianImageIso_factor
    (SheafOfModules.overFunctor.{u} X.ringCatSheaf U) f

/-- Actual original over-site restriction preserves the original free sheaf, with native basis maps. -/
def originalOverFreeIso (X : Scheme.{u}) (U : X.Opens) (I : Type u) :
    SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅
      (SheafOfModules.free (R := X.ringCatSheaf) I).over U :=
  by
    let := originalOverFunctor_preservesColimits X U
    exact SheafOfModules.mapFreeIso (SheafOfModules.overFunctor.{u} X.ringCatSheaf U) I (Iso.refl _)

/-- The actual original free-basis inclusion is preserved by the produced over-site free iso. -/
theorem originalOverFreeIso_inclusion (X : Scheme.{u}) (U : X.Opens) (I : Type u) (i : I) :
    SheafOfModules.ιFree i ≫ (originalOverFreeIso X U I).hom =
      (SheafOfModules.overFunctor.{u} X.ringCatSheaf U).map (SheafOfModules.ιFree i) := by
  let := originalOverFunctor_preservesColimits X U
  exact (SheafOfModules.ιFree_mapFreeIso_hom
    (SheafOfModules.overFunctor.{u} X.ringCatSheaf U) I (Iso.refl _) i).trans
      (Category.id_comp _)

end Hironaka.Geometry.QuotGrassmann
