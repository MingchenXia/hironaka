import Hironaka.Analytic.Unibranch.OriginalNativeProperFibreShrink
import Hironaka.Analytic.Unibranch.OriginalNativePhysicalHistoryRestriction
import Hironaka.Analytic.Unibranch.OriginalIntrinsicSingularLocus

/-! Ordinary PRESENT finite native history +EMPTY singular compact shadow
derives a genuine WHOLE smooth stopped source and SAME physical resolution.
Blueprint FIRST: original-native-hs-outer-empty-stop.tex.
No HS/profile/phaseSupplier/globalcompactness/endpoint packet. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSOuterEmptyStop
noncomputable section
open Hironaka SourceReducedComplexSpace OriginalNativeHSOuterHistory
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaG11SingularCentreModification

variable {B Y : SourceReducedComplexSpace} (h : PhysicalHistory B Y)
  (K : Set B.obj.left) (hK : IsCompact K)
  (hempty : intrinsicSingularLocus Y.obj ∩ h.projection.hom.left.base ⁻¹' K = ∅)

private abbrev regularOpen (Y : SourceReducedComplexSpace) : Opens Y.obj.left :=
  ⟨intrinsicRegularLocus Y.obj, isOpen_intrinsicRegularLocus Y.obj⟩

/-- Actual whole inverse compact shadow lies in the OLD original regular locus. -/
theorem shadow_regular
    (hempty : intrinsicSingularLocus Y.obj ∩ h.projection.hom.left.base ⁻¹' K = ∅) : h.projection.hom.left.base ⁻¹' K ⊆ (regularOpen Y : Set Y.obj.left) := by
  intro y hy
  by_contra hBad
  have hSing : y ∈ intrinsicSingularLocus Y.obj ∩ h.projection.hom.left.base ⁻¹' K := ⟨hBad, hy⟩
  rw [hempty] at hSing
  exact hSing

def neighbourhood := OriginalNativeProperFibreShrink.neighbourhood h.projection
  h.singularModification.isProperMap (regularOpen Y) K hK (shadow_regular h K hempty)

def source : SourceReducedComplexSpace := OriginalNativeProperFibreShrink.source h.projection
  h.singularModification.isProperMap (regularOpen Y) K hK (shadow_regular h K hempty)

/-- LITERAL inverse-open restriction of every physical arrow, with no stage omission. -/
def physicalHistory : PhysicalHistory (neighbourhood h K hK hempty).source (source h K hK hempty) :=
  OriginalNativePhysicalHistoryRestriction.restrict h (neighbourhood h K hK hempty).openSet
    (neighbourhood h K hK hempty).compactClosure

def sourceInclusion : source h K hK hempty ⟶ Y :=
  OriginalNativeProperFibreShrink.sourceInclusion h.projection h.singularModification.isProperMap
    (regularOpen Y) K hK (shadow_regular h K hempty)

theorem sourceInclusion_isOpenImmersion :
    LocallyRingedSpace.IsOpenImmersion (sourceInclusion h K hK hempty).hom.left :=
  OriginalNativeProperFibreShrink.sourceInclusion_isOpenImmersion h.projection
    h.singularModification.isProperMap (regularOpen Y) K hK (shadow_regular h K hempty)

def projection : source h K hK hempty ⟶ (neighbourhood h K hK hempty).source :=
  (physicalHistory h K hK hempty).projection

theorem projection_eq : projection h K hK hempty =
    OriginalNativeProperFibreShrink.projection h.projection h.singularModification.isProperMap
      (regularOpen Y) K hK (shadow_regular h K hempty) :=
  OriginalNativePhysicalHistoryRestriction.projection_restrict h
    (neighbourhood h K hK hempty).openSet (neighbourhood h K hK hempty).compactClosure

theorem projection_square : projection h K hK hempty ≫ (neighbourhood h K hK hempty).inclusion =
    sourceInclusion h K hK hempty ≫ h.projection :=
  OriginalNativePhysicalHistoryRestriction.projection_square h
    (neighbourhood h K hK hempty).openSet (neighbourhood h K hK hempty).compactClosure

theorem physical_length : (physicalHistory h K hK hempty).length = h.length :=
  OriginalNativePhysicalHistoryRestriction.length_restrict h
    (neighbourhood h K hK hempty).openSet (neighbourhood h K hK hempty).compactClosure

theorem compact_retained : K ⊆ range (neighbourhood h K hK hempty).inclusion.hom.left.base := by
  intro x hx
  exact ⟨⟨x, (neighbourhood h K hK hempty).contains hx⟩, rfl⟩

/-- EVERY point of the actual stopped native source is intrinsically regular. -/
theorem source_regular (y : (source h K hK hempty).obj.left) :
    y ∈ intrinsicRegularLocus (source h K hK hempty).obj := by
  have hGood : (sourceInclusion h K hK hempty).hom.left.base y ∈ intrinsicRegularLocus Y.obj :=
    OriginalNativeProperFibreShrink.source_in_goodOpen h.projection h.singularModification.isProperMap
      (regularOpen Y) K hK (shadow_regular h K hempty) ⟨y, rfl⟩
  exact (Set.ext_iff.mp (OriginalNativeProperFibreShrink.source_preimage_regular h.projection
    h.singularModification.isProperMap (regularOpen Y) K hK (shadow_regular h K hempty)) y).mp hGood

theorem singular_empty : intrinsicSingularLocus (source h K hK hempty).obj = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro y hy
  exact hy (source_regular h K hK hempty y)

theorem smooth : (source h K hK hempty).IsSmooth :=
  (OriginalIntrinsicSingularLocus.isSmooth_iff_intrinsicSingularLocus_eq_empty _).mpr
    (singular_empty h K hK hempty)

theorem resolution : IsResolution (projection h K hK hempty) :=
  (physicalHistory h K hK hempty).singularModification.isResolution (smooth h K hK hempty)

theorem proper : IsProperMap (projection h K hK hempty).hom.left.base :=
  (physicalHistory h K hK hempty).singularModification.isProperMap

theorem surjective : Function.Surjective (projection h K hK hempty).hom.left.base :=
  (physicalHistory h K hK hempty).singularModification.surjective

theorem originalReg : IsIsoOver (projection h K hK hempty)
    (intrinsicRegularLocus (neighbourhood h K hK hempty).source.obj) :=
  (physicalHistory h K hK hempty).singularModification.isIsoOver_intrinsicRegularLocus

theorem scalar : (projection h K hK hempty).hom.left ≫
    (neighbourhood h K hK hempty).source.obj.hom = (source h K hK hempty).obj.hom :=
  Over.w (projection h K hK hempty).hom

def shadow : Set (source h K hK hempty).obj.left :=
  OriginalNativeProperFibreShrink.shadow h.projection h.singularModification.isProperMap
    (regularOpen Y) K hK (shadow_regular h K hempty)

theorem shadow_compact : IsCompact (shadow h K hK hempty) :=
  OriginalNativeProperFibreShrink.shadow_compact h.projection h.singularModification.isProperMap
    (regularOpen Y) K hK (shadow_regular h K hempty)

theorem shadow_image : (sourceInclusion h K hK hempty).hom.left.base '' shadow h K hK hempty =
    h.projection.hom.left.base ⁻¹' K :=
  OriginalNativeProperFibreShrink.shadow_image h.projection h.singularModification.isProperMap
    (regularOpen Y) K hK (shadow_regular h K hempty)

theorem projection_comp {Z : SourceReducedComplexSpace} (r : B ⟶ Z) :
    projection h K hK hempty ≫ ((neighbourhood h K hK hempty).inclusion ≫ r) =
      sourceInclusion h K hK hempty ≫ (h.projection ≫ r) :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ r) (projection_square h K hK hempty)).trans (Category.assoc _ _ _))

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSOuterEmptyStop
