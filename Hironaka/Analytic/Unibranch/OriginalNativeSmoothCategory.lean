import Hironaka.Analytic.Unibranch.OriginalNativeSmoothComposition
import Mathlib.CategoryTheory.Widesubcategory

/-! The ordinary native smooth-arrow category, using STOCK wide subcategories.
Blueprint FIRST: original-native-smooth-category.tex.
No algorithm/history/lift fields; projection naturality is AFTER forget. -/
set_option autoImplicit false
open CategoryTheory
namespace Hironaka.Analytic.Unibranch.OriginalNativeSmoothCategory
noncomputable section
open SourceReducedComplexSpace OriginalNativeSmoothLocalProduct

def smoothProperty : MorphismProperty SourceReducedComplexSpace := fun _ _ f => IsSmoothMorphism f

instance smoothProperty_isMultiplicative : smoothProperty.IsMultiplicative where
  id_mem X := isSmoothMorphism_identity X
  comp_mem f g hf hg := OriginalNativeSmoothComposition.isSmoothMorphism_comp f g hf hg

abbrev Space := WideSubcategory smoothProperty

def ofSpace (X : SourceReducedComplexSpace) : Space := ⟨X⟩

def ofHom {X Y : SourceReducedComplexSpace} (f : X ⟶ Y) (hf : IsSmoothMorphism f) : ofSpace X ⟶ ofSpace Y :=
  ⟨f,hf⟩

theorem ofHom_native {X Y : SourceReducedComplexSpace} (f : X ⟶ Y) (hf : IsSmoothMorphism f) :
    (ofHom f hf).hom = f := rfl

theorem native_smooth {X Y : Space} (f : X ⟶ Y) : IsSmoothMorphism f.hom := f.property

def forget : Space ⥤ SourceReducedComplexSpace := wideSubcategoryInclusion smoothProperty

theorem forget_obj (X : Space) : forget.obj X = X.obj := rfl

theorem forget_map {X Y : Space} (f : X ⟶ Y) : forget.map f = f.hom := rfl

instance forget_faithful : forget.Faithful := by
  change (wideSubcategoryInclusion smoothProperty).Faithful
  infer_instance

end
end Hironaka.Analytic.Unibranch.OriginalNativeSmoothCategory
