import Hironaka.Analytic.Unibranch.OriginalNativeHSShadowPhaseFactory
import Hironaka.Analytic.Unibranch.OriginalNativePrecompactNeighbourhood
import Hironaka.Analytic.Unibranch.OriginalNativeSmoothOpenLocality

/-! The ACTUAL factory base is restricted into the actual incoming old-source
overlap, retaining the ENTIRE compact fibre. Blueprint FIRST:
original-native-hs-factory-overlap-cut.tex. No supplied phase lift/packet. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSFactoryOverlapCut
noncomputable section
open SourceReducedComplexSpace Hironaka.HironakaIntrinsicComplexAnalyticRegularLocus

variable (Y : SourceReducedComplexSpace) (K : Set Y.obj.left) (hK : IsCompact K)
  (hSing : (K ∩ intrinsicSingularLocus Y.obj).Nonempty)
  {Z : SourceReducedComplexSpace} (a : Z ⟶ Y)
  (ha : LocallyRingedSpace.IsOpenImmersion a.hom.left)
  (C : Set Z.obj.left) (hC : IsCompact C) (hImage : a.hom.left.base '' C ⊆ K)
local notation "B" => OriginalNativeHSShadowPhaseFactory.base Y K hK hSing
local notation "J" => OriginalNativeHSShadowPhaseFactory.baseInclusion Y K hK hSing
local notation "hJ" => OriginalNativeHSShadowPhaseFactory.baseInclusion_isOpenImmersion Y K hK hSing

/-- ENTIRE inverse of the actual compact common fibre, inside the actual factory base. -/
def liftedCompact : Set (B).obj.left := (J).hom.left.base ⁻¹' (a.hom.left.base '' C)

include hImage in
private theorem image_in_base : a.hom.left.base '' C ⊆ range (J).hom.left.base :=
  hImage.trans (OriginalNativeHSShadowPhaseFactory.compact_retained Y K hK hSing)

include hC hImage in
theorem liftedCompact_isCompact : IsCompact (liftedCompact Y K hK hSing a C) :=
  (hJ).base_open.isEmbedding.isInducing.isCompact_preimage'
    (hC.image a.hom.left.base.hom.continuous) (image_in_base Y K hK hSing a C hImage)

private def goodOpen : Opens (B).obj.left :=
  ⟨(J).hom.left.base ⁻¹' range a.hom.left.base,
    ha.base_open.isOpen_range.preimage (J).hom.left.base.hom.continuous⟩

private theorem lifted_in_good : liftedCompact Y K hK hSing a C ⊆ goodOpen Y K hK hSing a ha := by
  rintro b ⟨c,hc,heq⟩
  exact ⟨c,heq⟩

/-- Honest whole-image control on the closure of the actual precompact cut. -/
def neighbourhood : OriginalNativePrecompactNeighbourhood.Neighbourhood (B)
    (liftedCompact Y K hK hSing a C) (goodOpen Y K hK hSing a ha) :=
  OriginalNativePrecompactNeighbourhood.neighbourhood (B) (liftedCompact Y K hK hSing a C)
    (liftedCompact_isCompact Y K hK hSing a C hC hImage)
    (goodOpen Y K hK hSing a ha) (lifted_in_good Y K hK hSing a ha C)

local notation "N" => neighbourhood Y K hK hSing a ha C hC hImage

def source : SourceReducedComplexSpace := (N).source

def toOld : source Y K hK hSing a ha C hC hImage ⟶ Y := (N).inclusion ≫ (J)

theorem toOld_isOpenImmersion :
    LocallyRingedSpace.IsOpenImmersion (toOld Y K hK hSing a ha C hC hImage).hom.left :=
  @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ _ (N).inclusion_isOpenImmersion _ (hJ)

private theorem range_in_overlap : range (toOld Y K hK hSing a ha C hC hImage).hom.left.base ⊆
    range a.hom.left.base := by
  rintro _ ⟨b,rfl⟩
  exact (N).closure_subset (subset_closure b.property)

/-- The FULL native overlap map is derived from whole-image control. -/
def toCommon : source Y K hK hSing a ha C hC hImage ⟶ Z :=
  (OriginalNativeSmoothOpenLocality.exists_native_open_lift a
    (toOld Y K hK hSing a ha C hC hImage) ha
    (toOld_isOpenImmersion Y K hK hSing a ha C hC hImage)
    (range_in_overlap Y K hK hSing a ha C hC hImage)).choose

theorem toCommon_isOpenImmersion :
    LocallyRingedSpace.IsOpenImmersion (toCommon Y K hK hSing a ha C hC hImage).hom.left :=
  (OriginalNativeSmoothOpenLocality.exists_native_open_lift a
    (toOld Y K hK hSing a ha C hC hImage) ha
    (toOld_isOpenImmersion Y K hK hSing a ha C hC hImage)
    (range_in_overlap Y K hK hSing a ha C hC hImage)).choose_spec.1

theorem toCommon_square : toCommon Y K hK hSing a ha C hC hImage ≫ a = (N).inclusion ≫ (J) :=
  (OriginalNativeSmoothOpenLocality.exists_native_open_lift a
    (toOld Y K hK hSing a ha C hC hImage) ha
    (toOld_isOpenImmersion Y K hK hSing a ha C hC hImage)
    (range_in_overlap Y K hK hSing a ha C hC hImage)).choose_spec.2

theorem toCommon_scalar : (toCommon Y K hK hSing a ha C hC hImage).hom.left ≫ Z.obj.hom=
    (source Y K hK hSing a ha C hC hImage).obj.hom :=
  Over.w (toCommon Y K hK hSing a ha C hC hImage).hom

/-- Every original common-fibre point survives the actual overlap cut. -/
theorem compact_retained : C ⊆ range (toCommon Y K hK hSing a ha C hC hImage).hom.left.base := by
  intro c hc
  obtain ⟨b,hb⟩ := image_in_base Y K hK hSing a C hImage ⟨c,hc,rfl⟩
  have hbc : b ∈ liftedCompact Y K hK hSing a C := ⟨c,hc,hb.symm⟩
  let z : (source Y K hK hSing a ha C hC hImage).obj.left := ⟨b,(N).contains hbc⟩
  refine ⟨z,ha.base_open.injective ?_⟩
  exact (congrArg (fun f : source Y K hK hSing a ha C hC hImage ⟶ Y => f.hom.left.base z)
    (toCommon_square Y K hK hSing a ha C hC hImage)).trans hb

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSFactoryOverlapCut
