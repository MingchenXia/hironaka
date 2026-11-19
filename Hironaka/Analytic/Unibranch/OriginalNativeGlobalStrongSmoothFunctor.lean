import Hironaka.Analytic.Unibranch.OriginalNativeGlobalSmoothGluing
import Hironaka.Analytic.Unibranch.HironakaG1NativeStrongCleanupFunctor

/-! Actual smooth arrows on the literal global strong cleanup assignment.
Blueprint first: original-native-global-strong-smooth-functor.tex. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeGlobalStrongSmoothFunctor
noncomputable section
open Hironaka SourceReducedComplexSpace OriginalNativeSmoothLocalProduct
  OriginalNativeSmoothComposition

variable {X Y : SourceReducedComplexSpace} (f : X ⟶ Y) (hf : IsSmoothMorphism f)

include f hf in
/-- The held strong cleanup map for the actually constructed raw smooth map. -/
def map : OriginalNativeHSGlobalStrongResolution.source X ⟶ OriginalNativeHSGlobalStrongResolution.source Y :=
  HironakaG1NativeStrongCleanupFunctor.strongMap
    (OriginalNativeHSGlobalResolution.projection X) (OriginalNativeHSGlobalResolution.projection Y)
    (OriginalNativeHSGlobalResolution.resolution X) (OriginalNativeHSGlobalResolution.resolution Y)
    f hf (OriginalNativeGlobalSmoothGluing.map f hf) (OriginalNativeGlobalSmoothGluing.map_smooth f hf)
    (OriginalNativeGlobalSmoothGluing.map_square f hf).symm

theorem map_smooth : IsSmoothMorphism (map f hf) :=
  HironakaG1NativeStrongCleanupFunctor.strongMap_isSmooth
    (OriginalNativeHSGlobalResolution.projection X) (OriginalNativeHSGlobalResolution.projection Y)
    (OriginalNativeHSGlobalResolution.resolution X) (OriginalNativeHSGlobalResolution.resolution Y)
    f hf (OriginalNativeGlobalSmoothGluing.map f hf) (OriginalNativeGlobalSmoothGluing.map_smooth f hf)
    (OriginalNativeGlobalSmoothGluing.map_square f hf).symm

theorem map_refinement : map f hf ≫ OriginalNativeHSGlobalStrongResolution.refinement Y =
    OriginalNativeHSGlobalStrongResolution.refinement X ≫ OriginalNativeGlobalSmoothGluing.map f hf :=
  HironakaG1NativeStrongCleanupFunctor.strongMap_overY
    (OriginalNativeHSGlobalResolution.projection X) (OriginalNativeHSGlobalResolution.projection Y)
    (OriginalNativeHSGlobalResolution.resolution X) (OriginalNativeHSGlobalResolution.resolution Y)
    f hf (OriginalNativeGlobalSmoothGluing.map f hf) (OriginalNativeGlobalSmoothGluing.map_smooth f hf)
    (OriginalNativeGlobalSmoothGluing.map_square f hf).symm

theorem map_square : map f hf ≫ OriginalNativeHSGlobalStrongResolution.projection Y =
    OriginalNativeHSGlobalStrongResolution.projection X ≫ f :=
  HironakaG1NativeStrongCleanupFunctor.strongMap_overX
    (OriginalNativeHSGlobalResolution.projection X) (OriginalNativeHSGlobalResolution.projection Y)
    (OriginalNativeHSGlobalResolution.resolution X) (OriginalNativeHSGlobalResolution.resolution Y)
    f hf (OriginalNativeGlobalSmoothGluing.map f hf) (OriginalNativeGlobalSmoothGluing.map_smooth f hf)
    (OriginalNativeGlobalSmoothGluing.map_square f hf).symm

theorem map_identity : map (𝟙 X) (isSmoothMorphism_identity X) = 𝟙 _ := by
  apply OriginalNativeHSGlobalLiftUniqueness.strong_identity X
  simpa only [Category.comp_id] using map_square (𝟙 X) (isSmoothMorphism_identity X)

theorem map_composition {Z : SourceReducedComplexSpace} (g : Y ⟶ Z) (hg : IsSmoothMorphism g) :
    map f hf ≫ map g hg = map (f ≫ g) (isSmoothMorphism_comp f g hf hg) :=
  OriginalNativeHSGlobalLiftUniqueness.strong_composition X Y f hf Z g hg (map f hf) (map g hg)
    (map (f ≫ g) (isSmoothMorphism_comp f g hf hg)) (map_square f hf) (map_square g hg)
    (map_square (f ≫ g) (isSmoothMorphism_comp f g hf hg))

end
end Hironaka.Analytic.Unibranch.OriginalNativeGlobalStrongSmoothFunctor
