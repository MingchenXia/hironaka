import Hironaka.Analytic.Unibranch.OriginalNativeHSResolutionAtlasGlueData
import Hironaka.Analytic.Unibranch.OriginalNativeProperAtlas

/-! The actual proper native atlas and full global projection from ONLY X.
All gluing, overlap, local properness and cover inputs are internally derived.
Blueprint FIRST: original-native-hs-resolution-proper-atlas.tex. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSResolutionProperAtlas
noncomputable section
open Hironaka HironakaReducedComplexAnalyticSpaces SourceReducedComplexSpace

variable (X : SourceReducedComplexSpace)

abbrev data : LocallyRingedSpace.GlueData := OriginalNativeHSResolutionAtlasGlueData.glueData X

def scalarMap (i : (data X).J) : (data X).U i ⟶ complexPoint :=
  (OriginalNativeHSResolutionAtlasChoice.source i).obj.hom

theorem local_analytic (i : (data X).J) :
    sourceReducedComplexSpaceProperty (Over.mk (scalarMap X i)) :=
  (OriginalNativeHSResolutionAtlasChoice.source i).property

abbrev localBase (i : (data X).J) : SourceReducedComplexSpace :=
  OriginalNativeHSResolutionAtlasChoice.base i
abbrev baseInclusion (i : (data X).J) : localBase X i ⟶ X :=
  OriginalNativeHSResolutionAtlasChoice.baseInclusion i
abbrev localMap (i : (data X).J) :
    OriginalNativeProperAtlas.localSource (data X) (scalarMap X) (local_analytic X) i ⟶ localBase X i :=
  OriginalNativeHSResolutionAtlasChoice.projection i

theorem full_overlap (i j : (data X).J) :
    (data X).f i j ≫ OriginalNativeProperAtlas.localProjection (data X) (scalarMap X)
        (local_analytic X) (baseInclusion X) (localMap X) i =
      ((data X).t i j ≫ (data X).f j i) ≫ OriginalNativeProperAtlas.localProjection
        (data X) (scalarMap X) (local_analytic X) (baseInclusion X) (localMap X) j := by
  change OriginalNativeHSResolutionAtlasGlueData.overlapInclusion i j ≫
      OriginalNativeHSResolutionAtlasGlueData.localProjection i =
    (OriginalNativeHSResolutionAtlasGlueData.transition i j ≫
      OriginalNativeHSResolutionAtlasGlueData.overlapInclusion j i) ≫
      OriginalNativeHSResolutionAtlasGlueData.localProjection j
  simpa only [Category.assoc] using
    (OriginalNativeHSResolutionAtlasGlueData.overlap_square i j).symm

theorem full_overlap_range (i j : (data X).J) : range ((data X).f i j).base =
    (OriginalNativeProperAtlas.localProjection (data X) (scalarMap X) (local_analytic X)
      (baseInclusion X) (localMap X) i).base ⁻¹' range (baseInclusion X j).hom.left.base :=
  OriginalNativeHSResolutionAtlasGlueData.overlap_range i j

theorem base_open (i : (data X).J) : LocallyRingedSpace.IsOpenImmersion (baseInclusion X i).hom.left :=
  OriginalNativeHSResolutionAtlasChoice.baseInclusion_isOpenImmersion i

theorem base_cover (x : X.obj.left) :
    ∃ (i : (data X).J) (b : (localBase X i).obj.left), (baseInclusion X i).hom.left.base b = x :=
  OriginalNativeHSResolutionAtlasChoice.base_cover X x

theorem local_proper (i : (data X).J) : IsProperMap (localMap X i).hom.left.base :=
  OriginalNativeHSResolutionAtlasChoice.proper i

/-- The original reduced native source on the SAME actual glued locally ringed space. -/
def source : SourceReducedComplexSpace :=
  OriginalNativeProperAtlas.sourceObject (data X) (scalarMap X) (local_analytic X)
    (baseInclusion X) (localMap X) (full_overlap X) (full_overlap_range X)
    (base_open X) (base_cover X) (local_proper X)

/-- The full projection is derived by actual native descent. -/
def projection : source X ⟶ X :=
  OriginalNativeProperAtlas.projectionMorphism (data X) (scalarMap X) (local_analytic X)
    (baseInclusion X) (localMap X) (full_overlap X) (full_overlap_range X)
    (base_open X) (base_cover X) (local_proper X)

def localInclusion (i : (data X).J) : OriginalNativeHSResolutionAtlasChoice.source i ⟶ source X :=
  OriginalNativeProperAtlas.localMorphism (data X) (scalarMap X) (local_analytic X)
    (baseInclusion X) (localMap X) (full_overlap X) (full_overlap_range X)
    (base_open X) (base_cover X) (local_proper X) i

theorem localInclusion_isOpenImmersion (i : (data X).J) :
    LocallyRingedSpace.IsOpenImmersion (localInclusion X i).hom.left :=
  OriginalNativeProperAtlas.localMorphism_isOpenImmersion (data X) (scalarMap X) (local_analytic X)
    (baseInclusion X) (localMap X) (full_overlap X) (full_overlap_range X)
    (base_open X) (base_cover X) (local_proper X) i

theorem localInclusion_projection (i : (data X).J) : localInclusion X i ≫ projection X =
    OriginalNativeHSResolutionAtlasChoice.projection i ≫ OriginalNativeHSResolutionAtlasChoice.baseInclusion i :=
  OriginalNativeProperAtlas.localMorphism_projection (data X) (scalarMap X) (local_analytic X)
    (baseInclusion X) (localMap X) (full_overlap X) (full_overlap_range X)
    (base_open X) (base_cover X) (local_proper X) i

theorem localInclusion_cover (x : (source X).obj.left) :
    ∃ (i : (data X).J) (y : (OriginalNativeHSResolutionAtlasChoice.source i).obj.left),
      (localInclusion X i).hom.left.base y = x :=
  OriginalNativeProperAtlas.localMorphism_cover (data X) (scalarMap X) (local_analytic X)
    (baseInclusion X) (localMap X) (full_overlap X) (full_overlap_range X)
    (base_open X) (base_cover X) (local_proper X) x

theorem preimage_chart_range (i : (data X).J) :
    (projection X).hom.left.base ⁻¹' (OriginalNativeHSResolutionAtlasChoice.openSet i : Set X.obj.left) =
      range (localInclusion X i).hom.left.base := by
  have h := OriginalNativeProperAtlas.preimage_chart_range (data X) (scalarMap X) (local_analytic X)
    (baseInclusion X) (localMap X) (full_overlap X) (full_overlap_range X) i
  have hr : range (baseInclusion X i).hom.left.base =
      (OriginalNativeHSResolutionAtlasChoice.openSet i : Set X.obj.left) :=
    OriginalNativeHSResolutionAtlasChoice.baseInclusion_range i
  rw [hr] at h
  exact h

theorem projection_isProperMap : IsProperMap (projection X).hom.left.base :=
  OriginalNativeProperAtlas.projection_isProperMap (data X) (scalarMap X) (local_analytic X)
    (baseInclusion X) (localMap X) (full_overlap X) (full_overlap_range X)
    (base_open X) (base_cover X) (local_proper X)

theorem scalar : (projection X).hom.left ≫ X.obj.hom = (source X).obj.hom :=
  Over.w (projection X).hom

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSResolutionProperAtlas
