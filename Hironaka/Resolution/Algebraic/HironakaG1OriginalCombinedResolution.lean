import Hironaka.Analytic.Unibranch.OriginalNativeGlobalResolutionFunctors
import Hironaka.Resolution.Algebraic.HironakaG1FamilyFieldCompatibility

/-! The actual analytic strong functor and the independently established
field-compatible algebraic family, on their original assignments.
Blueprint first: hironaka-g1-original-combined-resolution.tex. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open Hironaka.Sequence
universe u
namespace Hironaka.Resolution.Algebraic.HironakaG1OriginalCombinedResolution
noncomputable section
open Hironaka.Analytic.Unibranch Hironaka.Analytic.Unibranch.SourceReducedComplexSpace
  Hironaka.Analytic.Unibranch.OriginalNativeSmoothCategory
  Hironaka.Analytic.Unibranch.OriginalNativeGlobalResolutionFunctors
  Hironaka HironakaIntrinsicComplexAnalyticRegularLocus
  ActualReducedAlgebraicSmoothResolutionFamily

/-- The very same strong resolution functor on ordinary smooth arrows. -/
abbrev analyticFunctor := strong

/-- Its actual projection, natural after forgetting to all native maps. -/
abbrev analyticProjection := strongProjection

/-- Its actual refinement to the raw functor, also natural after forgetting. -/
abbrev analyticRefinement := refinement

/-- The actual global strong source is covered by its literal cleanup components. -/
abbrev analytic_component_cover (X : Space) :=
  HironakaG1NativeStrongCleanup.strong_component_cover
    (OriginalNativeHSGlobalResolution.projection X.obj) (OriginalNativeHSGlobalResolution.resolution X.obj)

/-- The whole original singular stalk ideal on each actual strong component. -/
abbrev analytic_component_wholeStalk (X : Space) :=
  HironakaG1NativeStrongCleanup.strong_component_wholeStalk
    (OriginalNativeHSGlobalResolution.projection X.obj) (OriginalNativeHSGlobalResolution.resolution X.obj)

/-- Actual covering terminal ranges and SNC support on those same components. -/
abbrev analytic_snc_ranges (X : Space) :=
  HironakaG1NativeStrongCleanup.strong_saturated_range_readout
    (OriginalNativeHSGlobalResolution.projection X.obj) (OriginalNativeHSGlobalResolution.resolution X.obj)

/-- The entire original singular ideal on each such actual terminal range. -/
abbrev analytic_range_wholeStalk (X : Space) :=
  HironakaG1NativeStrongCleanup.strong_range_wholeStalk
    (OriginalNativeHSGlobalResolution.projection X.obj) (OriginalNativeHSGlobalResolution.resolution X.obj)

/-- Adapted holomorphic unit-monomial generators on the same ranges. -/
abbrev analytic_unit_monomial (X : Space) :=
  HironakaG1NativeStrongCleanup.strong_range_unit_monomial_generator
    (OriginalNativeHSGlobalResolution.projection X.obj) (OriginalNativeHSGlobalResolution.resolution X.obj)

/-- The literal analytic strong projection and the literal algebraic family
satisfy their already established original-scope properties. -/
theorem original_contract :
    (∀ X : Space,
      ((analyticFunctor.obj X).obj).IsSmooth ∧
      IsProperMap (OriginalNativeHSGlobalStrongResolution.refinement X.obj).hom.left.base ∧
      IsResolution (analyticProjection.app X) ∧
      IsProperMap (analyticProjection.app X).hom.left.base ∧
      Function.Surjective (analyticProjection.app X).hom.left.base ∧
      IsIsoOver (analyticProjection.app X) (intrinsicRegularLocus X.obj.obj)) ∧
    (∀ (X : Space) (U : Opens X.obj.obj.left) (hU : IsCompact (closure (U : Set X.obj.obj.left))),
      SmoothCentreModification.IsModification
        (OriginalRelativelyCompactRestriction.restrictionProjection U (analyticProjection.app X) hU
          (OriginalNativeHSGlobalStrongResolution.proper X.obj))) ∧
    (∀ (k : Type u) [Field k] [CharZero k] (X : ReducedAlgebraicScheme k),
      @Scheme.BlowUpSequence.IsStrongResolution k _ X.obj (resolutionFamily k X)) ∧
    (∀ (k : Type u) [Field k] [CharZero k], CommutesWithSmoothMorphisms (resolutionFamily k)) ∧
    CommutesWithChangeOfFields resolutionFamily := by
  refine ⟨?_, ?_, resolutionFamily_isStrongResolution,
    resolutionFamily_commutesWithSmoothMorphisms,
    HironakaG1FamilyFieldCompatibility.resolutionFamily_commutesWithChangeOfFields⟩
  · intro X
    exact OriginalNativeHSGlobalStrongResolution.geometry X.obj
  · intro X U hU
    exact OriginalNativeHSGlobalStrongResolution.finite X.obj U hU

end
end Hironaka.Resolution.Algebraic.HironakaG1OriginalCombinedResolution
