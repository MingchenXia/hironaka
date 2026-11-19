import Hironaka.Analytic.Unibranch.OriginalNativePrecompactNeighbourhood
import Hironaka.Analytic.Unibranch.OriginalLocalStrictWindowRegularity
import Hironaka.Resolution.HironakaG10FlatProperShrinking

/-! # Actual native proper whole-fibre shrinking near a compact shadow

The actual current target is shrunk; the full earlier projection square is
retained without asserting properness of an open inclusion to a larger base.
Blueprint FIRST: original-native-proper-fibre-shrink.tex.
-/

set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology
namespace Hironaka.Analytic.Unibranch.OriginalNativeProperFibreShrink
noncomputable section
open Hironaka SourceReducedComplexSpace
  HironakaIntrinsicComplexAnalyticRegularLocus

variable {X Y : SourceReducedComplexSpace} (q : Y ⟶ X)
  (hq : IsProperMap q.hom.left.base) (O : Opens Y.obj.left)

/-- The literal complement of the closed image of the entire bad source locus. -/
def goodBase : Opens X.obj.left :=
  ⟨(q.hom.left.base '' (O : Set Y.obj.left)ᶜ)ᶜ,
    (HironakaG10FlatProperShrinking.isClosed_image_compl hq.isClosedMap O.isOpen).isOpen_compl⟩

/-- Every point of each retained whole fibre is actually good. -/
theorem goodBase_eq_fibres : (goodBase q hq O : Set X.obj.left) =
    {x | q.hom.left.base ⁻¹' {x} ⊆ (O : Set Y.obj.left)} :=
  (HironakaG10FlatProperShrinking.setOf_fibre_subset_eq_compl_image
    (f := q.hom.left.base) (O : Set Y.obj.left)).symm

/-- The whole given compact shadow is retained, including empty fibres. -/
theorem compact_subset_goodBase {K : Set X.obj.left}
    (hgood : q.hom.left.base ⁻¹' K ⊆ (O : Set Y.obj.left)) :
    K ⊆ goodBase q hq O := by
  rw [goodBase_eq_fibres]
  intro x hx y hy
  apply hgood
  change q.hom.left.base y ∈ K
  rw [show q.hom.left.base y = x from hy]
  exact hx

/-- The whole inverse image of the literal saturated good base is good. -/
theorem preimage_goodBase_subset :
    q.hom.left.base ⁻¹' (goodBase q hq O : Set X.obj.left) ⊆ (O : Set Y.obj.left) := by
  rw [goodBase_eq_fibres]
  exact HironakaG10FlatProperShrinking.preimage_setOf_fibre_subset_subset (O : Set Y.obj.left)

variable (K : Set X.obj.left) (hK : IsCompact K)
  (hgood : q.hom.left.base ⁻¹' K ⊆ (O : Set Y.obj.left))

/-- Internally chosen actual precompact target inside the saturated good base. -/
def neighbourhood :
    OriginalNativePrecompactNeighbourhood.Neighbourhood X K (goodBase q hq O) :=
  OriginalNativePrecompactNeighbourhood.neighbourhood X K hK (goodBase q hq O)
    (compact_subset_goodBase q hq O hgood)

/-- Every point over the derived actual target lies in the given good open. -/
theorem preimage_neighbourhood_subset :
    q.hom.left.base ⁻¹' ((neighbourhood q hq O K hK hgood).openSet : Set X.obj.left) ⊆
      (O : Set Y.obj.left) := by
  intro y hy
  apply preimage_goodBase_subset q hq O
  exact (neighbourhood q hq O K hK hgood).closure_subset (subset_closure hy)

/-- The SAME literal original inverse-open native source. -/
def source : SourceReducedComplexSpace :=
  OriginalRelativelyCompactRestriction.preimageRestriction
    (neighbourhood q hq O K hK hgood).openSet q
    (neighbourhood q hq O K hK hgood).compactClosure hq

/-- Its actual full native open inclusion into the original current source. -/
def sourceInclusion : source q hq O K hK hgood ⟶ Y :=
  OriginalRelativelyCompactRestriction.inclusion Y
    (OriginalRelativelyCompactRestriction.preimageOpen
      (neighbourhood q hq O K hK hgood).openSet q)
    (OriginalRelativelyCompactRestriction.isCompact_closure_preimage
      (neighbourhood q hq O K hK hgood).openSet q
      (neighbourhood q hq O K hK hgood).compactClosure hq)

instance sourceInclusion_isOpenImmersion :
    LocallyRingedSpace.IsOpenImmersion (sourceInclusion q hq O K hK hgood).hom.left :=
  OriginalRelativelyCompactRestriction.inclusion_isOpenImmersion _ _ _

/-- The actual full native projection is to the SAME derived native target. -/
def projection : source q hq O K hK hgood ⟶ (neighbourhood q hq O K hK hgood).source :=
  OriginalRelativelyCompactRestriction.restrictionProjection
    (neighbourhood q hq O K hK hgood).openSet q
    (neighbourhood q hq O K hK hgood).compactClosure hq

theorem projection_inclusion :
    projection q hq O K hK hgood ≫ (neighbourhood q hq O K hK hgood).inclusion =
      sourceInclusion q hq O K hK hgood ≫ q :=
  OriginalRelativelyCompactRestriction.restrictionProjection_inclusion _ _ _ _

theorem projection_base (y : (source q hq O K hK hgood).obj.left) :
    ((projection q hq O K hK hgood).hom.left.base y).val = q.hom.left.base y.val :=
  OriginalRelativelyCompactRestriction.restrictionProjection_base _ _ _ _ y

theorem projection_scalar :
    (projection q hq O K hK hgood).hom.left ≫
        (neighbourhood q hq O K hK hgood).source.obj.hom =
      (source q hq O K hK hgood).obj.hom :=
  Over.w (projection q hq O K hK hgood).hom

/-- Properness TO the actual shrunken target, not after its open inclusion. -/
theorem projection_isProperMap : IsProperMap (projection q hq O K hK hgood).hom.left.base :=
  OriginalRelativelyCompactRestriction.restrictionProjection_isProperMap _ _ _ _

theorem source_in_goodOpen :
    range (sourceInclusion q hq O K hK hgood).hom.left.base ⊆ (O : Set Y.obj.left) := by
  rintro _ ⟨y, rfl⟩
  exact preimage_neighbourhood_subset q hq O K hK hgood y.property

/-- Full original composition is preserved without asserting properness to an earlier base. -/
theorem projection_comp {Z : SourceReducedComplexSpace} (r : X ⟶ Z) :
    projection q hq O K hK hgood ≫ ((neighbourhood q hq O K hK hgood).inclusion ≫ r) =
      sourceInclusion q hq O K hK hgood ≫ (q ≫ r) := by
  rw [← Category.assoc, projection_inclusion, Category.assoc]

theorem source_preimage_regular :
    (sourceInclusion q hq O K hK hgood).hom.left.base ⁻¹' intrinsicRegularLocus Y.obj =
      intrinsicRegularLocus (source q hq O K hK hgood).obj :=
  OriginalRelativelyCompactRestriction.inclusion_preimage_intrinsicRegularLocus _ _ _

/-- The full regular inverse restricts along the internally derived actual saturated square. -/
theorem projection_isIsoOver_regular (hreg : IsIsoOver q (intrinsicRegularLocus X.obj)) :
    IsIsoOver (projection q hq O K hK hgood)
      (intrinsicRegularLocus (neighbourhood q hq O K hK hgood).source.obj) := by
  have hrange : range (sourceInclusion q hq O K hK hgood).hom.left.base =
      q.hom.left.base ⁻¹' range (neighbourhood q hq O K hK hgood).inclusion.hom.left.base := by
    rw [(neighbourhood q hq O K hK hgood).inclusion_range]
    exact Subtype.range_coe
  have h := OriginalLocalStrictWindowRegularity.isIsoOver_of_open_square q
    (projection q hq O K hK hgood) (sourceInclusion q hq O K hK hgood)
    (neighbourhood q hq O K hK hgood).inclusion
    (sourceInclusion_isOpenImmersion q hq O K hK hgood)
    (neighbourhood q hq O K hK hgood).inclusion_isOpenImmersion
    (projection_inclusion q hq O K hK hgood) hrange (intrinsicRegularLocus X.obj) hreg
  rw [(neighbourhood q hq O K hK hgood).preimage_regular] at h
  exact h

/-- The actual whole inverse compact shadow, on the SAME restricted source. -/
def shadow : Set (source q hq O K hK hgood).obj.left :=
  (sourceInclusion q hq O K hK hgood).hom.left.base ⁻¹' (q.hom.left.base ⁻¹' K)

theorem shadow_eq_projection_preimage : shadow q hq O K hK hgood =
    (projection q hq O K hK hgood).hom.left.base ⁻¹'
      (neighbourhood q hq O K hK hgood).shadow := by
  ext y
  exact iff_of_eq (congrArg (fun f => f.hom.left.base y ∈ K)
    (projection_inclusion q hq O K hK hgood)).symm

theorem shadow_compact : IsCompact (shadow q hq O K hK hgood) := by
  rw [shadow_eq_projection_preimage]
  exact (projection_isProperMap q hq O K hK hgood).isCompact_preimage
    ((neighbourhood q hq O K hK hgood).shadow_compact hK)

/-- No original point in the compact inverse fibre shadow is lost. -/
theorem shadow_image :
    (sourceInclusion q hq O K hK hgood).hom.left.base '' shadow q hq O K hK hgood =
      q.hom.left.base ⁻¹' K := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hz
  · intro hy
    exact ⟨⟨y, (neighbourhood q hq O K hK hgood).contains hy⟩, hy, rfl⟩

end
end Hironaka.Analytic.Unibranch.OriginalNativeProperFibreShrink
