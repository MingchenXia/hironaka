import Hironaka.Analytic.Unibranch.OriginalNativeSmoothCategory
import Hironaka.Analytic.Unibranch.OriginalNativeGlobalStrongSmoothFunctor

/-! The actual raw and strong resolution endofunctors, with projections
natural in all native maps after forgetting smoothness.
Blueprint first: original-native-global-resolution-functors.tex. -/
set_option autoImplicit false
open CategoryTheory
namespace Hironaka.Analytic.Unibranch.OriginalNativeGlobalResolutionFunctors
noncomputable section
open SourceReducedComplexSpace OriginalNativeSmoothCategory
  OriginalNativeSmoothLocalProduct OriginalNativeSmoothComposition

/-- The actual raw resolution on ordinary smooth arrows. -/
def raw : Space ⥤ Space where
  obj X := ofSpace (OriginalNativeHSGlobalResolution.source X.obj)
  map f := ofHom (OriginalNativeGlobalSmoothGluing.map f.hom f.property)
    (OriginalNativeGlobalSmoothGluing.map_smooth f.hom f.property)
  map_id X := by
    apply WideSubcategory.hom_ext
    exact OriginalNativeGlobalSmoothGluing.map_identity
  map_comp f g := by
    apply WideSubcategory.hom_ext
    exact (OriginalNativeGlobalSmoothGluing.map_composition f.hom f.property g.hom g.property).symm

/-- The literal strong cleanup of the same raw assignment. -/
def strong : Space ⥤ Space where
  obj X := ofSpace (OriginalNativeHSGlobalStrongResolution.source X.obj)
  map f := ofHom (OriginalNativeGlobalStrongSmoothFunctor.map f.hom f.property)
    (OriginalNativeGlobalStrongSmoothFunctor.map_smooth f.hom f.property)
  map_id X := by
    apply WideSubcategory.hom_ext
    exact OriginalNativeGlobalStrongSmoothFunctor.map_identity
  map_comp f g := by
    apply WideSubcategory.hom_ext
    exact (OriginalNativeGlobalStrongSmoothFunctor.map_composition f.hom f.property g.hom g.property).symm

/-- The raw projections are natural as native maps; they need not be smooth. -/
def rawProjection : raw ⋙ forget ⟶ forget where
  app X := OriginalNativeHSGlobalResolution.projection X.obj
  naturality := by
    intro X Y f
    exact OriginalNativeGlobalSmoothGluing.map_square f.hom f.property

/-- The strong projections are natural as native maps. -/
def strongProjection : strong ⋙ forget ⟶ forget where
  app X := OriginalNativeHSGlobalStrongResolution.projection X.obj
  naturality := by
    intro X Y f
    exact OriginalNativeGlobalStrongSmoothFunctor.map_square f.hom f.property

/-- The actual strong refinement is natural after forgetting smoothness. -/
def refinement : strong ⋙ forget ⟶ raw ⋙ forget where
  app X := OriginalNativeHSGlobalStrongResolution.refinement X.obj
  naturality := by
    intro X Y f
    exact OriginalNativeGlobalStrongSmoothFunctor.map_refinement f.hom f.property

end
end Hironaka.Analytic.Unibranch.OriginalNativeGlobalResolutionFunctors
