import Hironaka.Analytic.Unibranch.OriginalNativeHSGlobalResolution
import Hironaka.Analytic.Unibranch.HironakaG1NativeStrongFiniteReadout

/-! Actual ordinary-X SAME strong assignment and EVERY original precompact
finite restriction. Whole originalSing ideal/SNC mothers specialize to
these LITERAL source/maps; no new output packet or supplied resolution.
Blueprint FIRST: original-native-hs-global-strong-resolution.tex. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSGlobalStrongResolution
noncomputable section
open SourceReducedComplexSpace Hironaka HironakaIntrinsicComplexAnalyticRegularLocus

variable (X : SourceReducedComplexSpace)

def source : SourceReducedComplexSpace := HironakaG1NativeStrongCleanup.strongSource
  (OriginalNativeHSGlobalResolution.projection X) (OriginalNativeHSGlobalResolution.resolution X)

def refinement : source X ⟶ OriginalNativeHSGlobalResolution.source X := HironakaG1NativeStrongCleanup.strongRefinement
  (OriginalNativeHSGlobalResolution.projection X) (OriginalNativeHSGlobalResolution.resolution X)

def projection : source X ⟶ X := HironakaG1NativeStrongCleanup.strongMorphism
  (OriginalNativeHSGlobalResolution.projection X) (OriginalNativeHSGlobalResolution.resolution X)

theorem projection_eq : projection X = refinement X ≫ OriginalNativeHSGlobalResolution.projection X := rfl

theorem geometry : (source X).IsSmooth ∧ IsProperMap (refinement X).hom.left.base ∧
    IsResolution (projection X) ∧ IsProperMap (projection X).hom.left.base ∧
    Function.Surjective (projection X).hom.left.base ∧ IsIsoOver (projection X) (intrinsicRegularLocus X.obj) :=
  HironakaG1NativeStrongCleanup.strong_geometry (OriginalNativeHSGlobalResolution.projection X)
    (OriginalNativeHSGlobalResolution.resolution X) (OriginalNativeHSGlobalResolution.originalReg X)

theorem source_smooth : (source X).IsSmooth := (geometry X).1

theorem refinement_proper : IsProperMap (refinement X).hom.left.base := (geometry X).2.1

theorem resolution : IsResolution (projection X) := (geometry X).2.2.1

theorem proper : IsProperMap (projection X).hom.left.base := (geometry X).2.2.2.1

theorem surjective : Function.Surjective (projection X).hom.left.base := (geometry X).2.2.2.2.1

theorem originalReg : IsIsoOver (projection X) (intrinsicRegularLocus X.obj) := (geometry X).2.2.2.2.2

theorem scalar : (projection X).hom.left ≫ X.obj.hom = (source X).obj.hom := Over.w (projection X).hom

/-- The initial finite witness is derived internally on the SAME global initial map. -/
theorem finite (U : Opens X.obj.left) (hU : IsCompact (closure (U : Set X.obj.left))) :
    SmoothCentreModification.IsModification
      (OriginalRelativelyCompactRestriction.restrictionProjection U (projection X) hU (proper X)) :=
  HironakaG1NativeStrongFiniteReadout.strongMorphism_restriction_isModification
    (OriginalNativeHSGlobalResolution.projection X) (OriginalNativeHSGlobalResolution.resolution X)
    (OriginalNativeHSGlobalResolution.originalReg X) U hU (OriginalNativeHSGlobalResolution.finite X U hU)

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSGlobalStrongResolution
