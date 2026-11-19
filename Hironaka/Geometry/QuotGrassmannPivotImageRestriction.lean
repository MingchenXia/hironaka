import Hironaka.Geometry.QuotGrassmannPivotTwisting
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Actual native image comparison under original open restriction

No exactness certificate is supplied: native restriction preserves limits by
its actual site pushforward description and preserves colimits by its actual
left adjunction. The pure limit proof is adapted from
EnvelopeProperty/deps/aintlib-ep33/ModularCurves/ForMathlib/SchemeModuleRestrictLimits.lean,
source SHA256 aec11620000ec965c46d8e8b8d0e52f9893a254f07ae33b3f3b6a11ece175166.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem originalPresheafPushforward_preservesLimits
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}}
    (φ : S ⟶ F.op ⋙ R) :
    PreservesLimits (PresheafOfModules.pushforward.{u} φ) := by
  constructor
  intro J _
  constructor
  intro K
  constructor
  intro c hc
  refine ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun X => ?_)⟩
  let E := PresheafOfModules.evaluation R (F.op.obj X) ⋙
    ModuleCat.restrictScalars (φ.app X).hom
  exact isLimitOfPreserves E hc

private theorem originalSheafPushforward_preservesLimits
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} [Functor.IsContinuous F J K]
    {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R) :
    PreservesLimits (SheafOfModules.pushforward.{u} φ) := by
  let : PreservesLimits
      (SheafOfModules.pushforward.{u} φ ⋙ SheafOfModules.forget S) := by
    change PreservesLimits (SheafOfModules.forget R ⋙
      PresheafOfModules.pushforward φ.hom)
    let : PreservesLimits (PresheafOfModules.pushforward φ.hom) :=
      originalPresheafPushforward_preservesLimits φ.hom
    exact comp_preservesLimits _ _
  exact preservesLimits_of_reflects_of_preserves
    (SheafOfModules.pushforward φ) (SheafOfModules.forget S)

/-- The actual native open restriction preserves limits, proved internally from its site map. -/
theorem originalOpenRestriction_preservesLimits
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    PreservesLimits (Scheme.Modules.restrictFunctor j) := by
  dsimp only [Scheme.Modules.restrictFunctor]
  apply originalSheafPushforward_preservesLimits

private def originalFunctorAbelianImageIso
    {C D : Type u} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [PreservesLimits F] [PreservesColimits F]
    {M N : C} (f : M ⟶ N) : F.obj (Abelian.image f) ≅ image (F.map f) :=
  F.mapIso (Abelian.imageIsoImage f) ≪≫ (PreservesImage.iso F f).symm

private theorem originalFunctorAbelianImageIso_inclusion
    {C D : Type u} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [PreservesLimits F] [PreservesColimits F]
    {M N : C} (f : M ⟶ N) :
    (originalFunctorAbelianImageIso F f).hom ≫ image.ι (F.map f) =
      F.map (Abelian.image.ι f) := by
  change (F.map (Abelian.imageIsoImage f).hom ≫
    (PreservesImage.iso F f).inv) ≫ image.ι (F.map f) = _
  rw [Category.assoc, PreservesImage.inv_comp_image_ι_map, ← F.map_comp,
    Abelian.imageIsoImage_hom_comp_image_ι]

private theorem originalFunctorAbelianImageIso_factor
    {C D : Type u} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [PreservesLimits F] [PreservesColimits F]
    {M N : C} (f : M ⟶ N) :
    F.map (Abelian.factorThruImage f) ≫ (originalFunctorAbelianImageIso F f).hom =
      factorThruImage (F.map f) := by
  apply (cancel_mono (image.ι (F.map f))).mp
  rw [Category.assoc, originalFunctorAbelianImageIso_inclusion,
    ← F.map_comp, Abelian.image.fac, image.fac]

/-- Actual restriction of the original native image, with the exact native comparison produced. -/
def originalOpenRestrictionImageIso
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    {M N : Y.Modules} (f : M ⟶ N) :
    (Scheme.Modules.restrictFunctor j).obj (Abelian.image f) ≅
      image ((Scheme.Modules.restrictFunctor j).map f) := by
  let := originalOpenRestriction_preservesLimits j
  exact originalFunctorAbelianImageIso (Scheme.Modules.restrictFunctor j) f

/-- The actual image inclusion triangle is preserved by the produced native restriction iso. -/
theorem originalOpenRestrictionImageIso_inclusion
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    {M N : Y.Modules} (f : M ⟶ N) :
    (originalOpenRestrictionImageIso j f).hom ≫
      image.ι ((Scheme.Modules.restrictFunctor j).map f) =
        (Scheme.Modules.restrictFunctor j).map (Abelian.image.ι f) := by
  let := originalOpenRestriction_preservesLimits j
  exact originalFunctorAbelianImageIso_inclusion (Scheme.Modules.restrictFunctor j) f

/-- The actual original quotient factor triangle is preserved by the same produced restriction iso. -/
theorem originalOpenRestrictionImageIso_factor
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    {M N : Y.Modules} (f : M ⟶ N) :
    (Scheme.Modules.restrictFunctor j).map (Abelian.factorThruImage f) ≫
      (originalOpenRestrictionImageIso j f).hom =
        factorThruImage ((Scheme.Modules.restrictFunctor j).map f) := by
  let := originalOpenRestriction_preservesLimits j
  exact originalFunctorAbelianImageIso_factor (Scheme.Modules.restrictFunctor j) f

end Hironaka.Geometry.QuotGrassmann
