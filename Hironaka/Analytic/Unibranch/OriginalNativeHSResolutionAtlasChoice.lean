import Hironaka.Analytic.Unibranch.OriginalNativeHSShadowOuterRun
import Hironaka.Analytic.Unibranch.OriginalNativePrescribedOpenHistory

/-! Actual ordinary-X family over ALL ORIGINAL precompact opens, with
literal K=closure U, same construction Runs/finite histories and ALL-X cover.
Blueprint FIRST: original-native-hs-resolution-atlas-choice.tex.
No supplied cover/transition/gluing packet/global countability. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSResolutionAtlasChoice
noncomputable section
open Hironaka SourceReducedComplexSpace OriginalNativeHSOuterHistory
  HironakaIntrinsicComplexAnalyticRegularLocus

def Index (X : SourceReducedComplexSpace) :=
  {U : Opens X.obj.left // IsCompact (closure (U : Set X.obj.left))}

variable {X : SourceReducedComplexSpace}

def openSet (i : Index X) : Opens X.obj.left := i.val

def compact (i : Index X) : Set X.obj.left := closure (openSet i : Set X.obj.left)

theorem compact_isCompact (i : Index X) : IsCompact (compact i) := i.property

theorem open_subset_compact (i : Index X) : (openSet i : Set X.obj.left) ⊆ compact i := subset_closure

def constructionRun (i : Index X) : OriginalNativeHSShadowOuterRun.Run (compact_isCompact i)
    (OriginalNativeHSShadowOuterState.initial X (compact i)) :=
  OriginalNativeHSShadowOuterRun.run (OriginalNativeHSShadowOuterState.initial X (compact i)) (compact_isCompact i)

def initialState (i : Index X) := OriginalNativeHSShadowOuterRun.nearCompactState X (compact i) (compact_isCompact i)

theorem initialState_eq_run (i : Index X) : initialState i = (constructionRun i).finalState := rfl

def base (i : Index X) : SourceReducedComplexSpace :=
  OriginalRelativelyCompactRestriction.restriction X (openSet i) (compact_isCompact i)

def baseInclusion (i : Index X) : base i ⟶ X :=
  OriginalRelativelyCompactRestriction.inclusion X (openSet i) (compact_isCompact i)

theorem baseInclusion_isOpenImmersion (i : Index X) :
    LocallyRingedSpace.IsOpenImmersion (baseInclusion i).hom.left :=
  OriginalRelativelyCompactRestriction.inclusion_isOpenImmersion _ _ _

theorem baseInclusion_range (i : Index X) : range (baseInclusion i).hom.left.base = (openSet i : Set X.obj.left) :=
  OriginalRelativelyCompactRestriction.inclusion_range _ _ _

def source (i : Index X) : SourceReducedComplexSpace :=
  OriginalNativePrescribedOpenHistory.source (initialState i).inclusion
    (initialState i).inclusion_isOpenImmersion (openSet i) (compact_isCompact i)
    (initialState i).contains (initialState i).history

def physicalHistory (i : Index X) : PhysicalHistory (base i) (source i) :=
  OriginalNativePrescribedOpenHistory.history (initialState i).inclusion
    (initialState i).inclusion_isOpenImmersion (openSet i) (compact_isCompact i)
    (initialState i).contains (initialState i).history

def projection (i : Index X) : source i ⟶ base i := (physicalHistory i).projection

def sourceInclusion (i : Index X) : source i ⟶ (initialState i).source :=
  OriginalNativePrescribedOpenHistory.sourceInclusion (initialState i).inclusion
    (initialState i).inclusion_isOpenImmersion (openSet i) (compact_isCompact i)
    (initialState i).contains (initialState i).history

theorem sourceInclusion_isOpenImmersion (i : Index X) :
    LocallyRingedSpace.IsOpenImmersion (sourceInclusion i).hom.left :=
  OriginalNativePrescribedOpenHistory.sourceInclusion_isOpenImmersion (initialState i).inclusion
    (initialState i).inclusion_isOpenImmersion (openSet i) (compact_isCompact i)
    (initialState i).contains (initialState i).history

theorem source_smooth (i : Index X) : (source i).IsSmooth :=
  OriginalNativePrescribedOpenHistory.source_smooth (initialState i).inclusion
    (initialState i).inclusion_isOpenImmersion (openSet i) (compact_isCompact i)
    (initialState i).contains (initialState i).history
    (OriginalNativeHSShadowOuterRun.nearCompact_smooth X (compact i) (compact_isCompact i))

theorem resolution (i : Index X) : IsResolution (projection i) :=
  (physicalHistory i).singularModification.isResolution (source_smooth i)

theorem finite (i : Index X) : SmoothCentreModification.IsModification (projection i) :=
  (physicalHistory i).singularModification.toIsModification

theorem proper (i : Index X) : IsProperMap (projection i).hom.left.base :=
  (physicalHistory i).singularModification.isProperMap

theorem surjective (i : Index X) : Function.Surjective (projection i).hom.left.base :=
  (physicalHistory i).singularModification.surjective

theorem originalReg (i : Index X) : IsIsoOver (projection i) (intrinsicRegularLocus (base i).obj) :=
  (physicalHistory i).singularModification.isIsoOver_intrinsicRegularLocus

theorem projection_square (i : Index X) : projection i ≫ baseInclusion i =
    sourceInclusion i ≫ (initialState i).history.projection ≫ (initialState i).inclusion :=
  OriginalNativePrescribedOpenHistory.projection_square (initialState i).inclusion
    (initialState i).inclusion_isOpenImmersion (openSet i) (compact_isCompact i)
    (initialState i).contains (initialState i).history

theorem scalar (i : Index X) : (projection i).hom.left ≫ (base i).obj.hom = (source i).obj.hom :=
  Over.w (projection i).hom

theorem projection_mem_open (i : Index X) (y : (source i).obj.left) :
    (projection i ≫ baseInclusion i).hom.left.base y ∈ openSet i :=
  ((projection i).hom.left.base y).property

theorem projection_mem_compact (i : Index X) (y : (source i).obj.left) :
    (projection i ≫ baseInclusion i).hom.left.base y ∈ compact i :=
  open_subset_compact i (projection_mem_open i y)

theorem base_cover (X : SourceReducedComplexSpace) (x : X.obj.left) :
    ∃ (i : Index X) (b : (base i).obj.left), (baseInclusion i).hom.left.base b = x := by
  let N := OriginalNativePrecompactNeighbourhood.neighbourhood X {x} isCompact_singleton ⊤ (by simp)
  let i : Index X := ⟨N.openSet, N.compactClosure⟩
  exact ⟨i, ⟨x, N.contains (by simp)⟩, rfl⟩

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSResolutionAtlasChoice
