import Hironaka.Analytic.Unibranch.OriginalNativeHSResolutionAtlasOverlap
import Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentOverlap
import Hironaka.Analytic.Unibranch.OriginalNativeHSOuterRunComparison
import Hironaka.Analytic.Unibranch.HironakaG11LiftUniqueness
import Hironaka.Analytic.Unibranch.SourceMorphismExt
import Hironaka.Analytic.Unibranch.OriginalNativePrescribedHistoryRefinement

/-! Actual transitions from the SAME saved finite original construction runs.
Blueprint FIRST: original-native-hs-resolution-atlas-transition.tex.
No supplied future/transition/case packet. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSResolutionAtlasTransition
noncomputable section
open Hironaka HironakaEmbeddedNativeMorphism
  SourceReducedComplexSpace OriginalNativeHSShadowOuterState OriginalNativeHSCurrentOverlap

variable {X : SourceReducedComplexSpace}
  (i j : OriginalNativeHSResolutionAtlasChoice.Index X)

def commonCompact : Set X.obj.left :=
  OriginalNativeHSResolutionAtlasChoice.compact (OriginalNativeHSResolutionAtlasOverlap.overlap i j)

theorem commonCompact_isCompact : IsCompact (commonCompact i j) :=
  OriginalNativeHSResolutionAtlasChoice.compact_isCompact (OriginalNativeHSResolutionAtlasOverlap.overlap i j)

theorem commonCompact_subset_left : commonCompact i j ⊆ OriginalNativeHSResolutionAtlasChoice.compact i :=
  closure_mono (fun _ hx => And.left hx)

theorem commonCompact_subset_right : commonCompact i j ⊆ OriginalNativeHSResolutionAtlasChoice.compact j :=
  closure_mono (fun _ hx => And.right hx)

def initialNeighbourhood := OriginalNativePrecompactNeighbourhood.neighbourhood X (commonCompact i j)
  (commonCompact_isCompact i j) ⊤ (by simp)

def initialContext : Context (OriginalNativeHSShadowOuterState.initial X (OriginalNativeHSResolutionAtlasChoice.compact i))
    (OriginalNativeHSShadowOuterState.initial X (OriginalNativeHSResolutionAtlasChoice.compact j)) (commonCompact i j) :=
  OriginalNativeHSCurrentOverlap.initial (initialNeighbourhood i j).openSet
    (initialNeighbourhood i j).compactClosure (initialNeighbourhood i j).contains

theorem saved_final : (OriginalNativeHSResolutionAtlasChoice.constructionRun i).finalState =
    OriginalNativeHSResolutionAtlasChoice.initialState i := rfl

local notation "rj" => OriginalNativeHSResolutionAtlasOverlap.savedInclusion j
  (OriginalNativeHSResolutionAtlasOverlap.overlap i j) (fun _ hx => And.right hx)
local notation "lj" => OriginalNativeHSResolutionAtlasOverlap.savedInclusion j
  (OriginalNativeHSResolutionAtlasOverlap.overlap j i) (fun _ hx => And.left hx)

private theorem opposite_range : range (rj).hom.left.base = range (lj).hom.left.base := by
  rw [OriginalNativeHSResolutionAtlasOverlap.savedInclusion_range,
    OriginalNativeHSResolutionAtlasOverlap.savedInclusion_range]
  apply congrArg (fun C : Set X.obj.left =>
    ((OriginalNativeHSResolutionAtlasChoice.initialState j).history.projection ≫
      (OriginalNativeHSResolutionAtlasChoice.initialState j).inclusion).hom.left.base ⁻¹' C)
  exact inter_comm _ _

private def rawOpposite : (OriginalNativeHSResolutionAtlasOverlap.rightSource i j).obj.left ≅
    (OriginalNativeHSResolutionAtlasOverlap.leftSource j i).obj.left := by
  let : LocallyRingedSpace.IsOpenImmersion (rj).hom.left :=
    OriginalNativeHSResolutionAtlasOverlap.savedInclusion_isOpenImmersion j
      (OriginalNativeHSResolutionAtlasOverlap.overlap i j) (fun _ hx => And.right hx)
  let : LocallyRingedSpace.IsOpenImmersion (lj).hom.left :=
    OriginalNativeHSResolutionAtlasOverlap.savedInclusion_isOpenImmersion j
      (OriginalNativeHSResolutionAtlasOverlap.overlap j i) (fun _ hx => And.left hx)
  exact openImmersionIsoOfRangeEq (rj).hom.left (lj).hom.left (opposite_range i j)

private theorem rawOpposite_square : (rawOpposite i j).hom ≫ (lj).hom.left = (rj).hom.left := by
  let : LocallyRingedSpace.IsOpenImmersion (rj).hom.left :=
    OriginalNativeHSResolutionAtlasOverlap.savedInclusion_isOpenImmersion j
      (OriginalNativeHSResolutionAtlasOverlap.overlap i j) (fun _ hx => And.right hx)
  let : LocallyRingedSpace.IsOpenImmersion (lj).hom.left :=
    OriginalNativeHSResolutionAtlasOverlap.savedInclusion_isOpenImmersion j
      (OriginalNativeHSResolutionAtlasOverlap.overlap j i) (fun _ hx => And.left hx)
  exact openImmersionIsoOfRangeEq_hom_fac _ _ (opposite_range i j)

def opposite : OriginalNativeHSResolutionAtlasOverlap.rightSource i j ≅
    OriginalNativeHSResolutionAtlasOverlap.leftSource j i := by
  have hp : (rawOpposite i j).hom ≫ (OriginalNativeHSResolutionAtlasOverlap.leftSource j i).obj.hom =
      (OriginalNativeHSResolutionAtlasOverlap.rightSource i j).obj.hom := by
    calc
      _ = (rawOpposite i j).hom ≫ ((lj).hom.left ≫ (OriginalNativeHSResolutionAtlasChoice.initialState j).source.obj.hom) :=
        congrArg (fun a => (rawOpposite i j).hom ≫ a) (Over.w (lj).hom).symm
      _ = ((rawOpposite i j).hom ≫ (lj).hom.left) ≫ (OriginalNativeHSResolutionAtlasChoice.initialState j).source.obj.hom :=
        (Category.assoc _ _ _).symm
      _ = (rj).hom.left ≫ (OriginalNativeHSResolutionAtlasChoice.initialState j).source.obj.hom :=
        congrArg (fun a => a ≫ (OriginalNativeHSResolutionAtlasChoice.initialState j).source.obj.hom) (rawOpposite_square i j)
      _ = _ := Over.w (rj).hom
  exact ObjectProperty.isoMk sourceReducedComplexSpaceProperty (Over.isoMk (rawOpposite i j) hp)

theorem opposite_saved_square : (opposite i j).hom ≫ (lj) = (rj) := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact rawOpposite_square i j

theorem opposite_map : (opposite i j).hom ≫ OriginalNativeHSResolutionAtlasOverlap.leftMap j i =
    OriginalNativeHSResolutionAtlasOverlap.rightMap i j := by
  have hL : OriginalNativeHSResolutionAtlasOverlap.leftMap j i ≫
      OriginalNativeHSResolutionAtlasChoice.sourceInclusion j = (lj) :=
    OriginalNativeHSResolutionAtlasOverlap.sourceMap_saved_square j
      (OriginalNativeHSResolutionAtlasOverlap.overlap j i) (fun _ hx => And.left hx)
  have hR : OriginalNativeHSResolutionAtlasOverlap.rightMap i j ≫
      OriginalNativeHSResolutionAtlasChoice.sourceInclusion j = (rj) :=
    OriginalNativeHSResolutionAtlasOverlap.sourceMap_saved_square j
      (OriginalNativeHSResolutionAtlasOverlap.overlap i j) (fun _ hx => And.right hx)
  have hs : ((opposite i j).hom ≫ OriginalNativeHSResolutionAtlasOverlap.leftMap j i) ≫
      OriginalNativeHSResolutionAtlasChoice.sourceInclusion j =
      OriginalNativeHSResolutionAtlasOverlap.rightMap i j ≫ OriginalNativeHSResolutionAtlasChoice.sourceInclusion j := by
    rw [Category.assoc,hL,opposite_saved_square,hR]
  let : LocallyRingedSpace.IsOpenImmersion (OriginalNativeHSResolutionAtlasChoice.sourceInclusion j).hom.left :=
    OriginalNativeHSResolutionAtlasChoice.sourceInclusion_isOpenImmersion j
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply (cancel_mono (OriginalNativeHSResolutionAtlasChoice.sourceInclusion j).hom.left).mp
  exact congrArg (fun a => a.hom.left) hs


/-- Concrete ANY-map uniqueness on the SAME actual prescribed finite histories. -/
theorem prescribed_maps_eq (k : OriginalNativeHSResolutionAtlasChoice.Index X)
    (hki : OriginalNativeHSResolutionAtlasChoice.openSet k ≤ OriginalNativeHSResolutionAtlasChoice.openSet i)
    (hkj : OriginalNativeHSResolutionAtlasChoice.openSet k ≤ OriginalNativeHSResolutionAtlasChoice.openSet j)
    (a b : OriginalNativeHSResolutionAtlasOverlap.sourceOn i k hki ⟶
      OriginalNativeHSResolutionAtlasOverlap.sourceOn j k hkj)
    (ha : a ≫ (OriginalNativeHSResolutionAtlasOverlap.historyOn j k hkj).projection =
      (OriginalNativeHSResolutionAtlasOverlap.historyOn i k hki).projection)
    (hb : b ≫ (OriginalNativeHSResolutionAtlasOverlap.historyOn j k hkj).projection =
      (OriginalNativeHSResolutionAtlasOverlap.historyOn i k hki).projection) : a = b := by
  let q := (OriginalNativeHSResolutionAtlasOverlap.historyOn i k hki).projection
  let p := (OriginalNativeHSResolutionAtlasOverlap.historyOn j k hkj).projection
  have hbase : ∀ z, p.hom.left.base (a.hom.left.base z) = p.hom.left.base (b.hom.left.base z) := by
    intro z
    exact (congrArg (fun f => f.hom.left.base z) ha).trans (congrArg (fun f => f.hom.left.base z) hb).symm
  have hgood : ∀ z ∈ q.hom.left.base ⁻¹'
      Hironaka.HironakaIntrinsicComplexAnalyticRegularLocus.intrinsicRegularLocus
        (OriginalNativeHSResolutionAtlasChoice.base k).obj,
      p.hom.left.base (a.hom.left.base z) ∈
        Hironaka.HironakaIntrinsicComplexAnalyticRegularLocus.intrinsicRegularLocus
          (OriginalNativeHSResolutionAtlasChoice.base k).obj := by
    intro z hz
    exact (congrArg (fun f => f.hom.left.base z) ha).symm ▸ hz
  apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
  intro z
  exact congrFun (HironakaG11LiftUniqueness.eq_of_comp_eq_of_dense
    (OriginalNativeHSResolutionAtlasOverlap.historyOn j k hkj).singularModification.isIsoOver_intrinsicRegularLocus
    a.hom.left.base.hom.continuous b.hom.left.base.hom.continuous hbase
    (OriginalNativeHSResolutionAtlasOverlap.historyOn i k hki).singularModification.dense_preimage_intrinsicRegularLocus hgood) z

theorem overlap_maps_eq (a b : OriginalNativeHSResolutionAtlasOverlap.leftSource i j ⟶
      OriginalNativeHSResolutionAtlasOverlap.rightSource i j)
    (ha : a ≫ (OriginalNativeHSResolutionAtlasOverlap.rightHistory i j).projection =
      (OriginalNativeHSResolutionAtlasOverlap.leftHistory i j).projection)
    (hb : b ≫ (OriginalNativeHSResolutionAtlasOverlap.rightHistory i j).projection =
      (OriginalNativeHSResolutionAtlasOverlap.leftHistory i j).projection) : a = b :=
  prescribed_maps_eq i j (OriginalNativeHSResolutionAtlasOverlap.overlap i j)
    (fun _ hx => hx.1) (fun _ hx => hx.2) a b ha hb

/-- The comparison is derived from the TWO actual saved runs, never supplied. -/
def finalContext : Context (OriginalNativeHSResolutionAtlasChoice.initialState i)
    (OriginalNativeHSResolutionAtlasChoice.initialState j) (commonCompact i j) :=
  (OriginalNativeHSOuterRunComparison.exists_context
    (OriginalNativeHSResolutionAtlasChoice.compact_isCompact i)
    (OriginalNativeHSResolutionAtlasChoice.compact_isCompact j)
    (commonCompact_isCompact i j) (commonCompact_subset_left i j) (commonCompact_subset_right i j)
    (OriginalNativeHSResolutionAtlasChoice.constructionRun i)
    (OriginalNativeHSResolutionAtlasChoice.constructionRun j) (initialContext i j)).choose

theorem finalContext_open_subset : (finalContext i j).openSet ≤ (initialContext i j).openSet :=
  (OriginalNativeHSOuterRunComparison.exists_context
    (OriginalNativeHSResolutionAtlasChoice.compact_isCompact i)
    (OriginalNativeHSResolutionAtlasChoice.compact_isCompact j)
    (commonCompact_isCompact i j) (commonCompact_subset_left i j) (commonCompact_subset_right i j)
    (OriginalNativeHSResolutionAtlasChoice.constructionRun i)
    (OriginalNativeHSResolutionAtlasChoice.constructionRun j) (initialContext i j)).choose_spec

theorem overlap_subset_context : OriginalNativeHSResolutionAtlasChoice.openSet
    (OriginalNativeHSResolutionAtlasOverlap.overlap i j) ≤ (finalContext i j).openSet :=
  fun _ hx => (finalContext i j).contains (subset_closure hx)

def transition : OriginalNativeHSResolutionAtlasOverlap.leftSource i j ≅
    OriginalNativeHSResolutionAtlasOverlap.rightSource i j :=
  OriginalNativePrescribedHistoryRefinement.restrictedIso
    (OriginalNativeHSResolutionAtlasChoice.initialState i).inclusion
    (OriginalNativeHSResolutionAtlasChoice.initialState i).inclusion_isOpenImmersion
    (finalContext i j).openSet (finalContext i j).compactClosure (finalContext i j).leftRange
    (OriginalNativeHSResolutionAtlasChoice.initialState i).history
    (OriginalNativeHSResolutionAtlasChoice.openSet (OriginalNativeHSResolutionAtlasOverlap.overlap i j))
    (OriginalNativeHSResolutionAtlasChoice.compact_isCompact (OriginalNativeHSResolutionAtlasOverlap.overlap i j))
    (overlap_subset_context i j)
    (OriginalNativeHSResolutionAtlasChoice.initialState j).inclusion
    (OriginalNativeHSResolutionAtlasChoice.initialState j).inclusion_isOpenImmersion (finalContext i j).rightRange
    (OriginalNativeHSResolutionAtlasChoice.initialState j).history
    (finalContext i j).comparison (finalContext i j).square

theorem transition_projection : (transition i j).hom ≫ (OriginalNativeHSResolutionAtlasOverlap.rightHistory i j).projection =
    (OriginalNativeHSResolutionAtlasOverlap.leftHistory i j).projection :=
  OriginalNativePrescribedHistoryRefinement.restrictedIso_projection
    (OriginalNativeHSResolutionAtlasChoice.initialState i).inclusion
    (OriginalNativeHSResolutionAtlasChoice.initialState i).inclusion_isOpenImmersion
    (finalContext i j).openSet (finalContext i j).compactClosure (finalContext i j).leftRange
    (OriginalNativeHSResolutionAtlasChoice.initialState i).history
    (OriginalNativeHSResolutionAtlasChoice.openSet (OriginalNativeHSResolutionAtlasOverlap.overlap i j))
    (OriginalNativeHSResolutionAtlasChoice.compact_isCompact (OriginalNativeHSResolutionAtlasOverlap.overlap i j))
    (overlap_subset_context i j)
    (OriginalNativeHSResolutionAtlasChoice.initialState j).inclusion
    (OriginalNativeHSResolutionAtlasChoice.initialState j).inclusion_isOpenImmersion (finalContext i j).rightRange
    (OriginalNativeHSResolutionAtlasChoice.initialState j).history
    (finalContext i j).comparison (finalContext i j).square

theorem transition_scalar : (transition i j).hom.hom.left ≫
    (OriginalNativeHSResolutionAtlasOverlap.rightSource i j).obj.hom =
    (OriginalNativeHSResolutionAtlasOverlap.leftSource i j).obj.hom := Over.w (transition i j).hom.hom

private theorem subopen_original_square (a b : OriginalNativeHSResolutionAtlasChoice.Index X)
    (hab : OriginalNativeHSResolutionAtlasChoice.openSet b ≤ OriginalNativeHSResolutionAtlasChoice.openSet a) :
    OriginalNativeHSResolutionAtlasOverlap.projectionOn a b hab ≫ OriginalNativeHSResolutionAtlasChoice.baseInclusion b =
      OriginalNativeHSResolutionAtlasOverlap.sourceMap a b hab ≫ OriginalNativeHSResolutionAtlasChoice.projection a ≫
        OriginalNativeHSResolutionAtlasChoice.baseInclusion a := by
  calc
    _ = OriginalNativeHSResolutionAtlasOverlap.projectionOn a b hab ≫
        (OriginalNativeHSResolutionAtlasOverlap.baseMap a b hab ≫ OriginalNativeHSResolutionAtlasChoice.baseInclusion a) :=
      congrArg (fun f => OriginalNativeHSResolutionAtlasOverlap.projectionOn a b hab ≫ f)
        (OriginalNativeHSResolutionAtlasOverlap.baseMap_square a b hab).symm
    _ = (OriginalNativeHSResolutionAtlasOverlap.projectionOn a b hab ≫
        OriginalNativeHSResolutionAtlasOverlap.baseMap a b hab) ≫ OriginalNativeHSResolutionAtlasChoice.baseInclusion a :=
      (Category.assoc _ _ _).symm
    _ = (OriginalNativeHSResolutionAtlasOverlap.sourceMap a b hab ≫ OriginalNativeHSResolutionAtlasChoice.projection a) ≫
        OriginalNativeHSResolutionAtlasChoice.baseInclusion a :=
      congrArg (fun f => f ≫ OriginalNativeHSResolutionAtlasChoice.baseInclusion a)
        (OriginalNativeHSResolutionAtlasOverlap.projection_square a b hab)
    _ = _ := Category.assoc _ _ _

theorem transition_original_square : (transition i j).hom ≫ OriginalNativeHSResolutionAtlasOverlap.rightMap i j ≫
      OriginalNativeHSResolutionAtlasChoice.projection j ≫ OriginalNativeHSResolutionAtlasChoice.baseInclusion j =
    OriginalNativeHSResolutionAtlasOverlap.leftMap i j ≫ OriginalNativeHSResolutionAtlasChoice.projection i ≫
      OriginalNativeHSResolutionAtlasChoice.baseInclusion i := by
  have hl := subopen_original_square i (OriginalNativeHSResolutionAtlasOverlap.overlap i j) (fun _ hx => hx.1)
  have hr := subopen_original_square j (OriginalNativeHSResolutionAtlasOverlap.overlap i j) (fun _ hx => hx.2)
  calc
    _ = (transition i j).hom ≫ ((OriginalNativeHSResolutionAtlasOverlap.rightHistory i j).projection ≫
        OriginalNativeHSResolutionAtlasChoice.baseInclusion (OriginalNativeHSResolutionAtlasOverlap.overlap i j)) :=
      congrArg (fun f => (transition i j).hom ≫ f) hr.symm
    _ = ((transition i j).hom ≫ (OriginalNativeHSResolutionAtlasOverlap.rightHistory i j).projection) ≫
        OriginalNativeHSResolutionAtlasChoice.baseInclusion (OriginalNativeHSResolutionAtlasOverlap.overlap i j) :=
      (Category.assoc _ _ _).symm
    _ = (OriginalNativeHSResolutionAtlasOverlap.leftHistory i j).projection ≫
        OriginalNativeHSResolutionAtlasChoice.baseInclusion (OriginalNativeHSResolutionAtlasOverlap.overlap i j) :=
      congrArg (fun f => f ≫ OriginalNativeHSResolutionAtlasChoice.baseInclusion
        (OriginalNativeHSResolutionAtlasOverlap.overlap i j)) (transition_projection i j)
    _ = _ := hl

def orderedIso : OriginalNativeHSResolutionAtlasOverlap.leftSource i j ≅
    OriginalNativeHSResolutionAtlasOverlap.leftSource j i := (transition i j).trans (opposite i j)

theorem ordered_original_square : (orderedIso i j).hom ≫ OriginalNativeHSResolutionAtlasOverlap.leftMap j i ≫
      OriginalNativeHSResolutionAtlasChoice.projection j ≫ OriginalNativeHSResolutionAtlasChoice.baseInclusion j =
    OriginalNativeHSResolutionAtlasOverlap.leftMap i j ≫ OriginalNativeHSResolutionAtlasChoice.projection i ≫
      OriginalNativeHSResolutionAtlasChoice.baseInclusion i := by
  rw [orderedIso,Iso.trans_hom,Category.assoc,← Category.assoc (opposite i j).hom,
    opposite_map]
  exact transition_original_square i j

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSResolutionAtlasTransition
