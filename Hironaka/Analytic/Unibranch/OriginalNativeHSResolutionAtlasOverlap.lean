import Hironaka.Analytic.Unibranch.OriginalNativeHSResolutionAtlasChoice
import Hironaka.Analytic.Unibranch.OriginalNativeSmoothOpenLocality

/-! Actual own finite overlap histories on ORIGINAL precompact opens, using
saved larger bases. Genuine source/target OIs, full ranges and native squares.
Blueprint FIRST: original-native-hs-resolution-atlas-overlap.tex. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSResolutionAtlasOverlap
noncomputable section
open Hironaka SourceReducedComplexSpace OriginalNativeHSOuterHistory
  HironakaIntrinsicComplexAnalyticRegularLocus

variable {X : SourceReducedComplexSpace} (i k : OriginalNativeHSResolutionAtlasChoice.Index X) (hki : OriginalNativeHSResolutionAtlasChoice.openSet k ≤ OriginalNativeHSResolutionAtlasChoice.openSet i)

include hki in
theorem closure_subset : OriginalNativeHSResolutionAtlasChoice.compact k ⊆ OriginalNativeHSResolutionAtlasChoice.compact i := closure_mono hki

include hki in
theorem closure_in_saved_base : OriginalNativeHSResolutionAtlasChoice.compact k ⊆ range (OriginalNativeHSResolutionAtlasChoice.initialState i).inclusion.hom.left.base :=
  (closure_subset i k hki).trans (OriginalNativeHSResolutionAtlasChoice.initialState i).contains

def baseMap : OriginalNativeHSResolutionAtlasChoice.base k ⟶ OriginalNativeHSResolutionAtlasChoice.base i :=
  (OriginalNativeSmoothOpenLocality.exists_native_open_lift (OriginalNativeHSResolutionAtlasChoice.baseInclusion i) (OriginalNativeHSResolutionAtlasChoice.baseInclusion k)
    (OriginalNativeHSResolutionAtlasChoice.baseInclusion_isOpenImmersion i) (OriginalNativeHSResolutionAtlasChoice.baseInclusion_isOpenImmersion k)
    (by rw [OriginalNativeHSResolutionAtlasChoice.baseInclusion_range,OriginalNativeHSResolutionAtlasChoice.baseInclusion_range];exact hki)).choose

theorem baseMap_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion (baseMap i k hki).hom.left :=
  (OriginalNativeSmoothOpenLocality.exists_native_open_lift (OriginalNativeHSResolutionAtlasChoice.baseInclusion i) (OriginalNativeHSResolutionAtlasChoice.baseInclusion k)
    (OriginalNativeHSResolutionAtlasChoice.baseInclusion_isOpenImmersion i) (OriginalNativeHSResolutionAtlasChoice.baseInclusion_isOpenImmersion k)
    (by rw [OriginalNativeHSResolutionAtlasChoice.baseInclusion_range,OriginalNativeHSResolutionAtlasChoice.baseInclusion_range];exact hki)).choose_spec.1

theorem baseMap_square : baseMap i k hki ≫ OriginalNativeHSResolutionAtlasChoice.baseInclusion i = OriginalNativeHSResolutionAtlasChoice.baseInclusion k :=
  (OriginalNativeSmoothOpenLocality.exists_native_open_lift (OriginalNativeHSResolutionAtlasChoice.baseInclusion i) (OriginalNativeHSResolutionAtlasChoice.baseInclusion k)
    (OriginalNativeHSResolutionAtlasChoice.baseInclusion_isOpenImmersion i) (OriginalNativeHSResolutionAtlasChoice.baseInclusion_isOpenImmersion k)
    (by rw [OriginalNativeHSResolutionAtlasChoice.baseInclusion_range,OriginalNativeHSResolutionAtlasChoice.baseInclusion_range];exact hki)).choose_spec.2

abbrev sourceOn : SourceReducedComplexSpace := OriginalNativePrescribedOpenHistory.source (OriginalNativeHSResolutionAtlasChoice.initialState i).inclusion
  (OriginalNativeHSResolutionAtlasChoice.initialState i).inclusion_isOpenImmersion (OriginalNativeHSResolutionAtlasChoice.openSet k) (OriginalNativeHSResolutionAtlasChoice.compact_isCompact k)
  (closure_in_saved_base i k hki) (OriginalNativeHSResolutionAtlasChoice.initialState i).history

def historyOn : PhysicalHistory (OriginalNativeHSResolutionAtlasChoice.base k) (sourceOn i k hki) := OriginalNativePrescribedOpenHistory.history (OriginalNativeHSResolutionAtlasChoice.initialState i).inclusion
  (OriginalNativeHSResolutionAtlasChoice.initialState i).inclusion_isOpenImmersion (OriginalNativeHSResolutionAtlasChoice.openSet k) (OriginalNativeHSResolutionAtlasChoice.compact_isCompact k)
  (closure_in_saved_base i k hki) (OriginalNativeHSResolutionAtlasChoice.initialState i).history

def projectionOn : sourceOn i k hki ⟶ OriginalNativeHSResolutionAtlasChoice.base k := (historyOn i k hki).projection

def savedInclusion : sourceOn i k hki ⟶ (OriginalNativeHSResolutionAtlasChoice.initialState i).source := OriginalNativePrescribedOpenHistory.sourceInclusion (OriginalNativeHSResolutionAtlasChoice.initialState i).inclusion
  (OriginalNativeHSResolutionAtlasChoice.initialState i).inclusion_isOpenImmersion (OriginalNativeHSResolutionAtlasChoice.openSet k) (OriginalNativeHSResolutionAtlasChoice.compact_isCompact k)
  (closure_in_saved_base i k hki) (OriginalNativeHSResolutionAtlasChoice.initialState i).history

theorem savedInclusion_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion (savedInclusion i k hki).hom.left :=
  OriginalNativePrescribedOpenHistory.sourceInclusion_isOpenImmersion (OriginalNativeHSResolutionAtlasChoice.initialState i).inclusion
    (OriginalNativeHSResolutionAtlasChoice.initialState i).inclusion_isOpenImmersion (OriginalNativeHSResolutionAtlasChoice.openSet k) (OriginalNativeHSResolutionAtlasChoice.compact_isCompact k)
    (closure_in_saved_base i k hki) (OriginalNativeHSResolutionAtlasChoice.initialState i).history

theorem savedInclusion_range : range (savedInclusion i k hki).hom.left.base =
    ((OriginalNativeHSResolutionAtlasChoice.initialState i).history.projection ≫ (OriginalNativeHSResolutionAtlasChoice.initialState i).inclusion).hom.left.base ⁻¹'
      (OriginalNativeHSResolutionAtlasChoice.openSet k : Set X.obj.left) := by
  change range (Subtype.val : {y : (OriginalNativeHSResolutionAtlasChoice.initialState i).source.obj.left //
    (OriginalNativeHSResolutionAtlasChoice.initialState i).inclusion.hom.left.base ((OriginalNativeHSResolutionAtlasChoice.initialState i).history.projection.hom.left.base y)
      ∈ OriginalNativeHSResolutionAtlasChoice.openSet k} → (OriginalNativeHSResolutionAtlasChoice.initialState i).source.obj.left) = _
  exact Subtype.range_coe

theorem original_square : projectionOn i k hki ≫ OriginalNativeHSResolutionAtlasChoice.baseInclusion k =
    savedInclusion i k hki ≫ (OriginalNativeHSResolutionAtlasChoice.initialState i).history.projection ≫ (OriginalNativeHSResolutionAtlasChoice.initialState i).inclusion :=
  OriginalNativePrescribedOpenHistory.projection_square (OriginalNativeHSResolutionAtlasChoice.initialState i).inclusion (OriginalNativeHSResolutionAtlasChoice.initialState i).inclusion_isOpenImmersion
    (OriginalNativeHSResolutionAtlasChoice.openSet k) (OriginalNativeHSResolutionAtlasChoice.compact_isCompact k) (closure_in_saved_base i k hki) (OriginalNativeHSResolutionAtlasChoice.initialState i).history

private theorem saved_range_subset : range (savedInclusion i k hki).hom.left.base ⊆
    range (OriginalNativeHSResolutionAtlasChoice.sourceInclusion i).hom.left.base := by
  rw [savedInclusion_range]
  change _ ⊆ range (Subtype.val : {y : (OriginalNativeHSResolutionAtlasChoice.initialState i).source.obj.left //
    (OriginalNativeHSResolutionAtlasChoice.initialState i).inclusion.hom.left.base ((OriginalNativeHSResolutionAtlasChoice.initialState i).history.projection.hom.left.base y)
      ∈ OriginalNativeHSResolutionAtlasChoice.openSet i} → (OriginalNativeHSResolutionAtlasChoice.initialState i).source.obj.left)
  intro y hy
  exact ⟨⟨y,hki hy⟩,rfl⟩

def sourceMap : sourceOn i k hki ⟶ OriginalNativeHSResolutionAtlasChoice.source i :=
  (OriginalNativeSmoothOpenLocality.exists_native_open_lift (OriginalNativeHSResolutionAtlasChoice.sourceInclusion i) (savedInclusion i k hki)
    (OriginalNativeHSResolutionAtlasChoice.sourceInclusion_isOpenImmersion i) (savedInclusion_isOpenImmersion i k hki)
    (saved_range_subset i k hki)).choose

theorem sourceMap_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion (sourceMap i k hki).hom.left :=
  (OriginalNativeSmoothOpenLocality.exists_native_open_lift (OriginalNativeHSResolutionAtlasChoice.sourceInclusion i) (savedInclusion i k hki)
    (OriginalNativeHSResolutionAtlasChoice.sourceInclusion_isOpenImmersion i) (savedInclusion_isOpenImmersion i k hki)
    (saved_range_subset i k hki)).choose_spec.1

theorem sourceMap_saved_square : sourceMap i k hki ≫ OriginalNativeHSResolutionAtlasChoice.sourceInclusion i = savedInclusion i k hki :=
  (OriginalNativeSmoothOpenLocality.exists_native_open_lift (OriginalNativeHSResolutionAtlasChoice.sourceInclusion i) (savedInclusion i k hki)
    (OriginalNativeHSResolutionAtlasChoice.sourceInclusion_isOpenImmersion i) (savedInclusion_isOpenImmersion i k hki)
    (saved_range_subset i k hki)).choose_spec.2

theorem projection_square : projectionOn i k hki ≫ baseMap i k hki = sourceMap i k hki ≫ OriginalNativeHSResolutionAtlasChoice.projection i := by
  have hfull : (projectionOn i k hki ≫ baseMap i k hki) ≫ OriginalNativeHSResolutionAtlasChoice.baseInclusion i =
      (sourceMap i k hki ≫ OriginalNativeHSResolutionAtlasChoice.projection i) ≫ OriginalNativeHSResolutionAtlasChoice.baseInclusion i := by
    calc
      _ = projectionOn i k hki ≫ OriginalNativeHSResolutionAtlasChoice.baseInclusion k := by rw [Category.assoc,baseMap_square]
      _ = savedInclusion i k hki ≫ (OriginalNativeHSResolutionAtlasChoice.initialState i).history.projection ≫ (OriginalNativeHSResolutionAtlasChoice.initialState i).inclusion :=
        original_square i k hki
      _ = (sourceMap i k hki ≫ OriginalNativeHSResolutionAtlasChoice.sourceInclusion i) ≫ (OriginalNativeHSResolutionAtlasChoice.initialState i).history.projection ≫
          (OriginalNativeHSResolutionAtlasChoice.initialState i).inclusion := by rw [sourceMap_saved_square]
      _ = _ := by rw [Category.assoc,Category.assoc,← OriginalNativeHSResolutionAtlasChoice.projection_square]
  let : LocallyRingedSpace.IsOpenImmersion (OriginalNativeHSResolutionAtlasChoice.baseInclusion i).hom.left := OriginalNativeHSResolutionAtlasChoice.baseInclusion_isOpenImmersion i
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply (cancel_mono (OriginalNativeHSResolutionAtlasChoice.baseInclusion i).hom.left).mp
  exact congrArg (fun f => f.hom.left) hfull

theorem sourceMap_range : range (sourceMap i k hki).hom.left.base =
    (OriginalNativeHSResolutionAtlasChoice.projection i ≫ OriginalNativeHSResolutionAtlasChoice.baseInclusion i).hom.left.base ⁻¹' (OriginalNativeHSResolutionAtlasChoice.openSet k : Set X.obj.left) := by
  ext y
  have hf := sourceMap_saved_square i k hki
  have ho := OriginalNativeHSResolutionAtlasChoice.projection_square i
  constructor
  · rintro ⟨z,rfl⟩
    have hs := congrArg (fun f : sourceOn i k hki ⟶ (OriginalNativeHSResolutionAtlasChoice.initialState i).source => f.hom.left.base z) hf
    have hy := (show (savedInclusion i k hki).hom.left.base z ∈
        range (savedInclusion i k hki).hom.left.base from ⟨z,rfl⟩)
    rw [savedInclusion_range] at hy
    change (OriginalNativeHSResolutionAtlasChoice.projection i ≫ OriginalNativeHSResolutionAtlasChoice.baseInclusion i).hom.left.base ((sourceMap i k hki).hom.left.base z) ∈ OriginalNativeHSResolutionAtlasChoice.openSet k
    rw [ho]
    change (OriginalNativeHSResolutionAtlasChoice.initialState i).inclusion.hom.left.base
      ((OriginalNativeHSResolutionAtlasChoice.initialState i).history.projection.hom.left.base
        ((OriginalNativeHSResolutionAtlasChoice.sourceInclusion i).hom.left.base ((sourceMap i k hki).hom.left.base z))) ∈ OriginalNativeHSResolutionAtlasChoice.openSet k
    change (OriginalNativeHSResolutionAtlasChoice.sourceInclusion i).hom.left.base
      ((sourceMap i k hki).hom.left.base z) = (savedInclusion i k hki).hom.left.base z at hs
    rw [hs]
    exact hy
  · intro hy
    have hy' : (OriginalNativeHSResolutionAtlasChoice.sourceInclusion i).hom.left.base y ∈ range (savedInclusion i k hki).hom.left.base := by
      rw [savedInclusion_range]
      change ((OriginalNativeHSResolutionAtlasChoice.sourceInclusion i ≫ (OriginalNativeHSResolutionAtlasChoice.initialState i).history.projection ≫
        (OriginalNativeHSResolutionAtlasChoice.initialState i).inclusion).hom.left.base y) ∈ OriginalNativeHSResolutionAtlasChoice.openSet k
      rw [← ho]
      exact hy
    obtain ⟨z,hz⟩ := hy'
    refine ⟨z,(OriginalNativeHSResolutionAtlasChoice.sourceInclusion_isOpenImmersion i).base_open.injective ?_⟩
    exact (congrArg (fun f : sourceOn i k hki ⟶ (OriginalNativeHSResolutionAtlasChoice.initialState i).source => f.hom.left.base z) hf).trans hz

theorem scalar : (projectionOn i k hki).hom.left ≫ (OriginalNativeHSResolutionAtlasChoice.base k).obj.hom = (sourceOn i k hki).obj.hom :=
  Over.w (projectionOn i k hki).hom

theorem source_smooth : (sourceOn i k hki).IsSmooth :=
  OriginalNativePrescribedOpenHistory.source_smooth (OriginalNativeHSResolutionAtlasChoice.initialState i).inclusion (OriginalNativeHSResolutionAtlasChoice.initialState i).inclusion_isOpenImmersion
    (OriginalNativeHSResolutionAtlasChoice.openSet k) (OriginalNativeHSResolutionAtlasChoice.compact_isCompact k) (closure_in_saved_base i k hki) (OriginalNativeHSResolutionAtlasChoice.initialState i).history
    (OriginalNativeHSShadowOuterRun.nearCompact_smooth X (OriginalNativeHSResolutionAtlasChoice.compact i) (OriginalNativeHSResolutionAtlasChoice.compact_isCompact i))

theorem resolution : IsResolution (projectionOn i k hki) :=
  (historyOn i k hki).singularModification.isResolution (source_smooth i k hki)

theorem finite : SmoothCentreModification.IsModification (projectionOn i k hki) :=
  (historyOn i k hki).singularModification.toIsModification

theorem proper : IsProperMap (projectionOn i k hki).hom.left.base :=
  (historyOn i k hki).singularModification.isProperMap

theorem originalReg : IsIsoOver (projectionOn i k hki) (intrinsicRegularLocus (OriginalNativeHSResolutionAtlasChoice.base k).obj) :=
  (historyOn i k hki).singularModification.isIsoOver_intrinsicRegularLocus

theorem history_length : (historyOn i k hki).length = (OriginalNativeHSResolutionAtlasChoice.initialState i).history.length + 1 :=
  OriginalNativePrescribedOpenHistory.history_length (OriginalNativeHSResolutionAtlasChoice.initialState i).inclusion (OriginalNativeHSResolutionAtlasChoice.initialState i).inclusion_isOpenImmersion
    (OriginalNativeHSResolutionAtlasChoice.openSet k) (OriginalNativeHSResolutionAtlasChoice.compact_isCompact k) (closure_in_saved_base i k hki) (OriginalNativeHSResolutionAtlasChoice.initialState i).history

def overlap (i j : OriginalNativeHSResolutionAtlasChoice.Index X) : OriginalNativeHSResolutionAtlasChoice.Index X :=
  ⟨OriginalNativeHSResolutionAtlasChoice.openSet i ⊓ OriginalNativeHSResolutionAtlasChoice.openSet j,(OriginalNativeHSResolutionAtlasChoice.compact_isCompact i).of_isClosed_subset isClosed_closure (closure_mono inter_subset_left)⟩

theorem overlap_openSet (i j : OriginalNativeHSResolutionAtlasChoice.Index X) : OriginalNativeHSResolutionAtlasChoice.openSet (overlap i j) = OriginalNativeHSResolutionAtlasChoice.openSet i ⊓ OriginalNativeHSResolutionAtlasChoice.openSet j := rfl

private theorem overlap_le_left (i j : OriginalNativeHSResolutionAtlasChoice.Index X) :
    OriginalNativeHSResolutionAtlasChoice.openSet (overlap i j) ≤ OriginalNativeHSResolutionAtlasChoice.openSet i :=
  fun _ hx => hx.1

private theorem overlap_le_right (i j : OriginalNativeHSResolutionAtlasChoice.Index X) :
    OriginalNativeHSResolutionAtlasChoice.openSet (overlap i j) ≤ OriginalNativeHSResolutionAtlasChoice.openSet j :=
  fun _ hx => hx.2

abbrev leftSource (i j : OriginalNativeHSResolutionAtlasChoice.Index X) := sourceOn i (overlap i j) (overlap_le_left i j)
abbrev rightSource (i j : OriginalNativeHSResolutionAtlasChoice.Index X) := sourceOn j (overlap i j) (overlap_le_right i j)

def leftHistory (i j : OriginalNativeHSResolutionAtlasChoice.Index X) : PhysicalHistory (OriginalNativeHSResolutionAtlasChoice.base (overlap i j)) (leftSource i j) :=
  historyOn i (overlap i j) (overlap_le_left i j)

def rightHistory (i j : OriginalNativeHSResolutionAtlasChoice.Index X) : PhysicalHistory (OriginalNativeHSResolutionAtlasChoice.base (overlap i j)) (rightSource i j) :=
  historyOn j (overlap i j) (overlap_le_right i j)

def leftMap (i j : OriginalNativeHSResolutionAtlasChoice.Index X) : leftSource i j ⟶ OriginalNativeHSResolutionAtlasChoice.source i := sourceMap i (overlap i j) (overlap_le_left i j)

def rightMap (i j : OriginalNativeHSResolutionAtlasChoice.Index X) : rightSource i j ⟶ OriginalNativeHSResolutionAtlasChoice.source j := sourceMap j (overlap i j) (overlap_le_right i j)

theorem leftMap_range (i j : OriginalNativeHSResolutionAtlasChoice.Index X) : range (leftMap i j).hom.left.base =
    (OriginalNativeHSResolutionAtlasChoice.projection i ≫ OriginalNativeHSResolutionAtlasChoice.baseInclusion i).hom.left.base ⁻¹' (OriginalNativeHSResolutionAtlasChoice.openSet j : Set X.obj.left) := by
  apply (sourceMap_range i (overlap i j) (overlap_le_left i j)).trans
  apply Set.ext
  intro y
  exact and_iff_right (OriginalNativeHSResolutionAtlasChoice.projection_mem_open i y)

theorem rightMap_range (i j : OriginalNativeHSResolutionAtlasChoice.Index X) : range (rightMap i j).hom.left.base =
    (OriginalNativeHSResolutionAtlasChoice.projection j ≫ OriginalNativeHSResolutionAtlasChoice.baseInclusion j).hom.left.base ⁻¹' (OriginalNativeHSResolutionAtlasChoice.openSet i : Set X.obj.left) := by
  apply (sourceMap_range j (overlap i j) (overlap_le_right i j)).trans
  apply Set.ext
  intro y
  exact and_iff_left (OriginalNativeHSResolutionAtlasChoice.projection_mem_open j y)

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSResolutionAtlasOverlap
