import Hironaka.Analytic.Unibranch.OriginalNativeHSResolutionProperAtlas
import Hironaka.Analytic.Unibranch.OriginalNativeResolutionAtlas
import Hironaka.Analytic.Unibranch.OriginalNativeProperAtlasRestriction

/-! Ordinary ORIGINAL-X global native resolution and REAL finite restriction
on EVERY original precompact U, on the SAME actual glued projection.
Blueprint FIRST: original-native-hs-global-resolution.tex.
All chart/history/transition inputs are internally constructed. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSGlobalResolution
noncomputable section
open Hironaka SourceReducedComplexSpace HironakaIntrinsicComplexAnalyticRegularLocus

variable (X : SourceReducedComplexSpace)
local notation "D" => OriginalNativeHSResolutionProperAtlas.data X
local notation "σ" => OriginalNativeHSResolutionProperAtlas.scalarMap X
local notation "HA" => OriginalNativeHSResolutionProperAtlas.local_analytic X
local notation "J" => OriginalNativeHSResolutionProperAtlas.baseInclusion X
local notation "P" => OriginalNativeHSResolutionProperAtlas.localMap X
local notation "HO" => OriginalNativeHSResolutionProperAtlas.full_overlap X
local notation "HR" => OriginalNativeHSResolutionProperAtlas.full_overlap_range X
local notation "HJ" => OriginalNativeHSResolutionProperAtlas.base_open X
local notation "HC" => OriginalNativeHSResolutionProperAtlas.base_cover X

abbrev source : SourceReducedComplexSpace := OriginalNativeHSResolutionProperAtlas.source X
abbrev projection : source X ⟶ X := OriginalNativeHSResolutionProperAtlas.projection X

private theorem localResolution (i : (D).J) : IsResolution ((P) i) :=
  OriginalNativeHSResolutionAtlasChoice.resolution i

private theorem localReg (i : (D).J) : IsIsoOver ((P) i)
    (intrinsicRegularLocus (OriginalNativeHSResolutionProperAtlas.localBase X i).obj) :=
  OriginalNativeHSResolutionAtlasChoice.originalReg i

theorem source_smooth : (source X).IsSmooth :=
  OriginalNativeResolutionAtlas.source_isSmooth (D) (σ) (HA) (J) (P) (HO) (HR) (HJ) (HC) (localResolution X)

theorem originalReg : IsIsoOver (projection X) (intrinsicRegularLocus X.obj) :=
  OriginalNativeResolutionAtlas.isIsoOver_intrinsicRegularLocus
    (D) (σ) (HA) (J) (P) (HO) (HR) (HJ) (HC) (localResolution X) (localReg X)

theorem proper : IsProperMap (projection X).hom.left.base :=
  OriginalNativeHSResolutionProperAtlas.projection_isProperMap X

theorem resolution : IsResolution (projection X) :=
  OriginalNativeResolutionAtlas.isResolution
    (D) (σ) (HA) (J) (P) (HO) (HR) (HJ) (HC) (localResolution X) (localReg X)

theorem surjective : Function.Surjective (projection X).hom.left.base := (resolution X).2.surjective

theorem originalSing_inverse_thin : interior ((projection X).hom.left.base ⁻¹' intrinsicSingularLocus X.obj) = ∅ :=
  OriginalNativeResolutionAtlas.interior_preimage_intrinsicSingularLocus
    (D) (σ) (HA) (J) (P) (HO) (HR) (HJ) (HC) (localResolution X)

theorem dense_originalReg : Dense ((projection X).hom.left.base ⁻¹' intrinsicRegularLocus X.obj) :=
  OriginalNativeResolutionAtlas.dense_preimage_intrinsicRegularLocus
    (D) (σ) (HA) (J) (P) (HO) (HR) (HJ) (HC) (localResolution X)

theorem scalar : (projection X).hom.left ≫ X.obj.hom = (source X).obj.hom := Over.w (projection X).hom

variable (U : Opens X.obj.left) (hU : IsCompact (closure (U : Set X.obj.left)))

def windowIndex : OriginalNativeHSResolutionAtlasChoice.Index X := ⟨U,hU⟩

private theorem local_range :
    range (OriginalNativeHSResolutionProperAtlas.localInclusion X (windowIndex X U hU)).hom.left.base =
      (projection X).hom.left.base ⁻¹' (U : Set X.obj.left) :=
  (OriginalNativeHSResolutionProperAtlas.preimage_chart_range X (windowIndex X U hU)).symm

private theorem local_square : (OriginalNativeHSResolutionAtlasChoice.physicalHistory (windowIndex X U hU)).projection ≫
      OriginalRelativelyCompactRestriction.inclusion X U hU =
    OriginalNativeHSResolutionProperAtlas.localInclusion X (windowIndex X U hU) ≫ projection X :=
  (OriginalNativeHSResolutionProperAtlas.localInclusion_projection X (windowIndex X U hU)).symm

/-- Compare the REAL U recipe with the literal inverse-U source of the SAME global p. -/
def restrictionComparison : OriginalNativeHSResolutionAtlasChoice.source (windowIndex X U hU) ≅
    OriginalRelativelyCompactRestriction.preimageRestriction U (projection X) hU (proper X) :=
  OriginalNativeProperAtlasRestriction.comparison (projection X) (proper X) U hU
    (OriginalNativeHSResolutionProperAtlas.localInclusion X (windowIndex X U hU))
    (OriginalNativeHSResolutionProperAtlas.localInclusion_isOpenImmersion X (windowIndex X U hU)) (local_range X U hU)

theorem restrictionComparison_inclusion : (restrictionComparison X U hU).hom ≫
    OriginalNativeProperAtlasRestriction.sourceInclusion (projection X) (proper X) U hU =
      OriginalNativeHSResolutionProperAtlas.localInclusion X (windowIndex X U hU) :=
  OriginalNativeProperAtlasRestriction.comparison_inclusion (projection X) (proper X) U hU
    (OriginalNativeHSResolutionProperAtlas.localInclusion X (windowIndex X U hU))
    (OriginalNativeHSResolutionProperAtlas.localInclusion_isOpenImmersion X (windowIndex X U hU)) (local_range X U hU)

theorem restrictionComparison_projection : (restrictionComparison X U hU).hom ≫
    OriginalRelativelyCompactRestriction.restrictionProjection U (projection X) hU (proper X) =
      OriginalNativeHSResolutionAtlasChoice.projection (windowIndex X U hU) :=
  OriginalNativeProperAtlasRestriction.comparison_projection (projection X) (proper X) U hU
    (OriginalNativeHSResolutionProperAtlas.localInclusion X (windowIndex X U hU))
    (OriginalNativeHSResolutionProperAtlas.localInclusion_isOpenImmersion X (windowIndex X U hU)) (local_range X U hU)
    (OriginalNativeHSResolutionAtlasChoice.physicalHistory (windowIndex X U hU)) (local_square X U hU)

theorem restrictionComparison_scalar : (restrictionComparison X U hU).hom.hom.left ≫
    (OriginalRelativelyCompactRestriction.preimageRestriction U (projection X) hU (proper X)).obj.hom =
      (OriginalNativeHSResolutionAtlasChoice.source (windowIndex X U hU)).obj.hom :=
  Over.w (restrictionComparison X U hU).hom.hom

/-- No local finite witness is supplied: U itself is an ACTUAL atlas index. -/
theorem finite : SmoothCentreModification.IsModification
    (OriginalRelativelyCompactRestriction.restrictionProjection U (projection X) hU (proper X)) :=
  OriginalNativeProperAtlasRestriction.finite (projection X) (proper X) U hU
    (OriginalNativeHSResolutionProperAtlas.localInclusion X (windowIndex X U hU))
    (OriginalNativeHSResolutionProperAtlas.localInclusion_isOpenImmersion X (windowIndex X U hU)) (local_range X U hU)
    (OriginalNativeHSResolutionAtlasChoice.physicalHistory (windowIndex X U hU)) (local_square X U hU)

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSGlobalResolution
