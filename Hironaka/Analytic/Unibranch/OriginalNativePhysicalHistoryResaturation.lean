import Hironaka.Analytic.Unibranch.OriginalNativePhysicalHistoryRestriction
import Hironaka.Analytic.Unibranch.OriginalNativeProperFibreShrink
import Hironaka.Analytic.Unibranch.HironakaG1NativeModificationIsoTransport
import Hironaka.Resolution.HironakaEmbeddedNativeMorphismCommon

/-! A PRESENT actual finite phase over an open current-source neighbourhood
is resaturated to the earlier base and appended to the PRESENT real history.
An actual empty-centre iso step joins the two different native restrictions.
Blueprint FIRST: original-native-physical-history-resaturation.tex. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology
namespace Hironaka.Analytic.Unibranch.OriginalNativePhysicalHistoryResaturation
noncomputable section
open Hironaka HironakaEmbeddedNativeMorphism
  HironakaIntrinsicComplexAnalyticRegularLocus SourceReducedComplexSpace
  HironakaG11SingularCentreModification OriginalNativeHSOuterHistory
  OriginalRelativelyCompactRestriction

private def nativeIsoOfLRSIso {A B : SourceReducedComplexSpace}
    (e : A.obj.left ≅ B.obj.left) (hs : e.hom ≫ B.obj.hom = A.obj.hom) : A ≅ B where
  hom := ObjectProperty.homMk (Over.homMk e.hom hs)
  inv := ObjectProperty.homMk (Over.homMk e.inv (by
    rw [← hs, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]))
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact e.hom_inv_id
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact e.inv_hom_id

variable {X Y B Z : SourceReducedComplexSpace} (h : PhysicalHistory X Y)
  (j : B ⟶ Y) (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left)
  (K : Set X.obj.left) (hK : IsCompact K)
  (hCover : h.projection.hom.left.base ⁻¹' K ⊆ range j.hom.left.base)

private def goodOpen : Opens Y.obj.left :=
  ⟨range j.hom.left.base, hj.base_open.isOpen_range⟩

/-- Actual precompact earlier-base shrink retaining the ENTIRE inverse compact shadow. -/
def neighbourhood := OriginalNativeProperFibreShrink.neighbourhood h.projection
  h.singularModification.isProperMap (goodOpen j hj) K hK hCover

/-- The CLOSURE is retained in the whole good fibres, not only the open itself. -/
theorem closure_preimage_subset : h.projection.hom.left.base ⁻¹'
    closure ((neighbourhood h j hj K hK hCover).openSet : Set X.obj.left) ⊆
      range j.hom.left.base := by
  intro y hy
  apply OriginalNativeProperFibreShrink.preimage_goodBase_subset h.projection
    h.singularModification.isProperMap (goodOpen j hj)
  exact (neighbourhood h j hj K hK hCover).closure_subset hy

/-- Literal inverse open in the actual phase base, which may be a composite native OI. -/
def phaseOpen : Opens B.obj.left :=
  ⟨j.hom.left.base ⁻¹' (h.projection.hom.left.base ⁻¹'
      ((neighbourhood h j hj K hK hCover).openSet : Set X.obj.left)),
    (neighbourhood h j hj K hK hCover).openSet.isOpen.preimage
      (h.projection.hom.left.base.hom.continuous.comp j.hom.left.base.hom.continuous)⟩

theorem phaseOpen_compactClosure :
    IsCompact (closure (phaseOpen h j hj K hK hCover : Set B.obj.left)) := by
  have hT := h.singularModification.isProperMap.isCompact_preimage
    (neighbourhood h j hj K hK hCover).compactClosure
  have hJT := hj.base_open.isEmbedding.isInducing.isCompact_preimage' hT
    (closure_preimage_subset h j hj K hK hCover)
  apply hJT.of_isClosed_subset isClosed_closure
  apply closure_minimal
  · intro b hb
    exact subset_closure hb
  · exact isClosed_closure.preimage
      (h.projection.hom.left.base.hom.continuous.comp j.hom.left.base.hom.continuous)

/-- The SAME literal endpoint of the earlier history restricted to the derived base. -/
abbrev oldSource : SourceReducedComplexSpace :=
  preimageRestriction (neighbourhood h j hj K hK hCover).openSet h.projection
    (neighbourhood h j hj K hK hCover).compactClosure h.singularModification.isProperMap

/-- The SAME literal phase-base restriction, with compactness derived above. -/
abbrev phaseTarget : SourceReducedComplexSpace :=
  restriction B (phaseOpen h j hj K hK hCover)
    (phaseOpen_compactClosure h j hj K hK hCover)

/-- Full original inclusion of the earlier history's literal inverse open. -/
abbrev oldInclusion : oldSource h j hj K hK hCover ⟶ Y :=
  inclusion Y (preimageOpen (neighbourhood h j hj K hK hCover).openSet h.projection)
    (isCompact_closure_preimage _ _ (neighbourhood h j hj K hK hCover).compactClosure
      h.singularModification.isProperMap)

/-- Full original inclusion of the actual phase-base inverse open. -/
abbrev phaseInclusion : phaseTarget h j hj K hK hCover ⟶ B :=
  inclusion B (phaseOpen h j hj K hK hCover)
    (phaseOpen_compactClosure h j hj K hK hCover)

private theorem comparisonRange :
    range ((phaseInclusion h j hj K hK hCover).hom.left ≫ j.hom.left).base =
      range (oldInclusion h j hj K hK hCover).hom.left.base := by
  change range (fun b : phaseOpen h j hj K hK hCover => j.hom.left.base b.val) =
    range (Subtype.val : preimageOpen (neighbourhood h j hj K hK hCover).openSet h.projection → Y.obj.left)
  rw [Subtype.range_coe]
  ext y
  constructor
  · rintro ⟨b, rfl⟩
    exact b.property
  · intro hy
    have hIn : y ∈ range j.hom.left.base :=
      closure_preimage_subset h j hj K hK hCover (subset_closure hy)
    obtain ⟨b, rfl⟩ := hIn
    exact ⟨⟨b, hy⟩, rfl⟩

private def rawComparison : (phaseTarget h j hj K hK hCover).obj.left ≅
    (oldSource h j hj K hK hCover).obj.left := by
  let : LocallyRingedSpace.IsOpenImmersion j.hom.left := hj
  let : LocallyRingedSpace.IsOpenImmersion (phaseInclusion h j hj K hK hCover).hom.left :=
    inclusion_isOpenImmersion _ _ _
  let : LocallyRingedSpace.IsOpenImmersion (oldInclusion h j hj K hK hCover).hom.left :=
    inclusion_isOpenImmersion _ _ _
  exact openImmersionIsoOfRangeEq
    ((phaseInclusion h j hj K hK hCover).hom.left ≫ j.hom.left)
    (oldInclusion h j hj K hK hCover).hom.left (comparisonRange h j hj K hK hCover)

private theorem rawComparison_square : (rawComparison h j hj K hK hCover).hom ≫
    (oldInclusion h j hj K hK hCover).hom.left =
      (phaseInclusion h j hj K hK hCover).hom.left ≫ j.hom.left := by
  let : LocallyRingedSpace.IsOpenImmersion j.hom.left := hj
  let : LocallyRingedSpace.IsOpenImmersion (phaseInclusion h j hj K hK hCover).hom.left :=
    inclusion_isOpenImmersion _ _ _
  let : LocallyRingedSpace.IsOpenImmersion (oldInclusion h j hj K hK hCover).hom.left :=
    inclusion_isOpenImmersion _ _ _
  exact openImmersionIsoOfRangeEq_hom_fac _ _ (comparisonRange h j hj K hK hCover)

/-- Internally derived FULL native comparison of the two genuine intermediate opens. -/
def comparison : phaseTarget h j hj K hK hCover ≅ oldSource h j hj K hK hCover :=
  nativeIsoOfLRSIso (rawComparison h j hj K hK hCover) (by
    calc
      _ = (rawComparison h j hj K hK hCover).hom ≫
          ((oldInclusion h j hj K hK hCover).hom.left ≫ Y.obj.hom) := rfl
      _ = ((rawComparison h j hj K hK hCover).hom ≫
          (oldInclusion h j hj K hK hCover).hom.left) ≫ Y.obj.hom :=
        (Category.assoc _ _ _).symm
      _ = ((phaseInclusion h j hj K hK hCover).hom.left ≫ j.hom.left) ≫ Y.obj.hom :=
        congrArg (fun a => a ≫ Y.obj.hom) (rawComparison_square h j hj K hK hCover)
      _ = _ := by rw [Category.assoc, Over.w j.hom]; exact Over.w (phaseInclusion h j hj K hK hCover).hom)

theorem comparison_square : (comparison h j hj K hK hCover).hom ≫
    oldInclusion h j hj K hK hCover = phaseInclusion h j hj K hK hCover ≫ j := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact rawComparison_square h j hj K hK hCover

theorem comparison_scalar : (comparison h j hj K hK hCover).hom.hom.left ≫
    (oldSource h j hj K hK hCover).obj.hom = (phaseTarget h j hj K hK hCover).obj.hom :=
  Over.w (comparison h j hj K hK hCover).hom.hom

/-- The comparison is a REAL empty-centre singular step, never a literal-identity cast. -/
theorem comparison_singularStep : IsSingularCentreStep (comparison h j hj K hK hCover).hom := by
  refine ⟨HironakaG1NativeModificationIsoTransport.emptyCentre _,
    HironakaG1NativeModificationIsoTransport.emptyCentreInclusion _,
    HironakaG1NativeModificationIsoTransport.isSmoothCentreBlowup_iso
      (comparison h j hj K hK hCover), ?_⟩
  rw [HironakaG1NativeModificationIsoTransport.emptyCentreInclusion_range]
  exact empty_subset _

variable (k : PhysicalHistory B Z)

/-- Literal endpoint of the actual phase history restricted to the derived phase open. -/
abbrev source : SourceReducedComplexSpace :=
  preimageRestriction (phaseOpen h j hj K hK hCover) k.projection
    (phaseOpen_compactClosure h j hj K hK hCover) k.singularModification.isProperMap

def sourceInclusion : source h j hj K hK hCover k ⟶ Z :=
  inclusion Z (preimageOpen (phaseOpen h j hj K hK hCover) k.projection)
    (isCompact_closure_preimage _ _ (phaseOpen_compactClosure h j hj K hK hCover)
      k.singularModification.isProperMap)

/-- ONE actual physical history over the original-base shrink; all old/phase steps retained. -/
def history : PhysicalHistory
    (restriction X (neighbourhood h j hj K hK hCover).openSet
      (neighbourhood h j hj K hK hCover).compactClosure)
    (source h j hj K hK hCover k) :=
  ((OriginalNativePhysicalHistoryRestriction.restrict h
      (neighbourhood h j hj K hK hCover).openSet
      (neighbourhood h j hj K hK hCover).compactClosure).snoc
    (comparison h j hj K hK hCover).hom (comparison_singularStep h j hj K hK hCover)).append
      (OriginalNativePhysicalHistoryRestriction.restrict k (phaseOpen h j hj K hK hCover)
        (phaseOpen_compactClosure h j hj K hK hCover))

theorem history_length : (history h j hj K hK hCover k).length = h.length + 1 + k.length := by
  simp only [history, PhysicalHistory.length_append, PhysicalHistory.length,
    OriginalNativePhysicalHistoryRestriction.length_restrict]

theorem projection_formula : (history h j hj K hK hCover k).projection =
    restrictionProjection (phaseOpen h j hj K hK hCover) k.projection
      (phaseOpen_compactClosure h j hj K hK hCover) k.singularModification.isProperMap ≫
    (comparison h j hj K hK hCover).hom ≫
    restrictionProjection (neighbourhood h j hj K hK hCover).openSet h.projection
      (neighbourhood h j hj K hK hCover).compactClosure h.singularModification.isProperMap := by
  simp only [history, PhysicalHistory.projection_append, PhysicalHistory.projection,
    OriginalNativePhysicalHistoryRestriction.projection_restrict]

theorem projection_square : (history h j hj K hK hCover k).projection ≫
    inclusion X (neighbourhood h j hj K hK hCover).openSet
      (neighbourhood h j hj K hK hCover).compactClosure =
    sourceInclusion h j hj K hK hCover k ≫ k.projection ≫ j ≫ h.projection := by
  apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
  intro z
  let pW := restrictionProjection (phaseOpen h j hj K hK hCover) k.projection
    (phaseOpen_compactClosure h j hj K hK hCover) k.singularModification.isProperMap
  have hf := congrArg (fun a => a.hom.left.base z) (projection_formula h j hj K hK hCover k)
  have he := congrArg (fun a => a.hom.left.base (pW.hom.left.base z))
    (comparison_square h j hj K hK hCover)
  have hr := restrictionProjection_base (neighbourhood h j hj K hK hCover).openSet
    h.projection (neighbourhood h j hj K hK hCover).compactClosure
    h.singularModification.isProperMap ((comparison h j hj K hK hCover).hom.hom.left.base
      (pW.hom.left.base z))
  have hk := restrictionProjection_base (phaseOpen h j hj K hK hCover) k.projection
    (phaseOpen_compactClosure h j hj K hK hCover) k.singularModification.isProperMap z
  exact (congrArg Subtype.val hf).trans (hr.trans
    ((congrArg h.projection.hom.left.base he).trans
      (congrArg (fun b => h.projection.hom.left.base (j.hom.left.base b)) hk)))

theorem scalar : (history h j hj K hK hCover k).projection.hom.left ≫
    (restriction X (neighbourhood h j hj K hK hCover).openSet
      (neighbourhood h j hj K hK hCover).compactClosure).obj.hom =
    (source h j hj K hK hCover k).obj.hom :=
  Over.w (history h j hj K hK hCover k).projection.hom

theorem proper : IsProperMap (history h j hj K hK hCover k).projection.hom.left.base :=
  (history h j hj K hK hCover k).singularModification.isProperMap

theorem originalReg : IsIsoOver (history h j hj K hK hCover k).projection
    (intrinsicRegularLocus (restriction X (neighbourhood h j hj K hK hCover).openSet
      (neighbourhood h j hj K hK hCover).compactClosure).obj) :=
  (history h j hj K hK hCover k).singularModification.isIsoOver_intrinsicRegularLocus

theorem shadow_image : (sourceInclusion h j hj K hK hCover k).hom.left.base ''
    ((sourceInclusion h j hj K hK hCover k).hom.left.base ⁻¹'
      (k.projection.hom.left.base ⁻¹' (j.hom.left.base ⁻¹' (h.projection.hom.left.base ⁻¹' K)))) =
    k.projection.hom.left.base ⁻¹' (j.hom.left.base ⁻¹' (h.projection.hom.left.base ⁻¹' K)) := by
  ext z
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact hb
  · intro hz
    have hzW : k.projection.hom.left.base z ∈ phaseOpen h j hj K hK hCover :=
      (neighbourhood h j hj K hK hCover).contains hz
    exact ⟨⟨z, hzW⟩, hz, rfl⟩

end
end Hironaka.Analytic.Unibranch.OriginalNativePhysicalHistoryResaturation
