import Hironaka.Analytic.Unibranch.OriginalNativeHSShadowOuterState
import Hironaka.Analytic.Unibranch.OriginalNativePrescribedHistoryRefinement

/-! Actual STOP-to-old prescribed endpoints, then the STOP--STOP base case.
Both stops and the smaller original neighbourhood are computed internally.
Blueprint FIRST: original-native-hs-stopped-endpoints.tex. No arbitrary smooth
resolution comparison, future endpoint packet, or common physical clock. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSStoppedEndpointComparison
noncomputable section
open SourceReducedComplexSpace OriginalNativeHSShadowOuterState
  OriginalNativeHSOuterHistory OriginalRelativelyCompactRestriction

private theorem native_cancel {A B C : SourceReducedComplexSpace} (a b : A ⟶ B) (f : B ⟶ C)
    (hf : LocallyRingedSpace.IsOpenImmersion f.hom.left) (h : a ≫ f = b ≫ f) : a=b := by
  let : LocallyRingedSpace.IsOpenImmersion f.hom.left := hf
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply (cancel_mono f.hom.left).mp
  exact congrArg (fun k => k.hom.left) h

section OneStop
variable {X : SourceReducedComplexSpace} {K : Set X.obj.left}
  (S : State X K) (hK : IsCompact K) (he : singularShadow S = ∅)
  (V : Opens X.obj.left) (hV : IsCompact (closure (V : Set X.obj.left)))
  (hOld : closure (V : Set X.obj.left) ⊆ range S.inclusion.hom.left.base)
  (hStop : closure (V : Set X.obj.left) ⊆ range (stopped S hK he).inclusion.hom.left.base)

local notation "S₀" => stopped S hK he

abbrev oldSource : SourceReducedComplexSpace := OriginalNativePrescribedHistoryRefinement.source
  S.inclusion S.inclusion_isOpenImmersion V hV hOld S.history
abbrev stoppedSource : SourceReducedComplexSpace := OriginalNativePrescribedHistoryRefinement.source
  (S₀).inclusion (S₀).inclusion_isOpenImmersion V hV hStop (S₀).history

abbrev oldProjection : oldSource S V hV hOld ⟶ restriction X V hV :=
  OriginalNativePrescribedHistoryRefinement.projection S.inclusion S.inclusion_isOpenImmersion V hV hOld S.history

abbrev stoppedProjection : stoppedSource S hK he V hV hStop ⟶ restriction X V hV :=
  OriginalNativePrescribedHistoryRefinement.projection (S₀).inclusion (S₀).inclusion_isOpenImmersion V hV hStop (S₀).history

private abbrev oldMap : oldSource S V hV hOld ⟶ S.source :=
  OriginalNativePrescribedHistoryRefinement.inclusion S.inclusion S.inclusion_isOpenImmersion V hV hOld S.history
private abbrev newMap : stoppedSource S hK he V hV hStop ⟶ (S₀).source :=
  OriginalNativePrescribedHistoryRefinement.inclusion (S₀).inclusion (S₀).inclusion_isOpenImmersion V hV hStop (S₀).history
private abbrev stopInclusion : (S₀).source ⟶ S.source :=
  OriginalNativeHSOuterEmptyStop.sourceInclusion S.history (baseShadow S) (baseShadow_compact S hK) he
private def combinedMap : stoppedSource S hK he V hV hStop ⟶ S.source :=
  newMap S hK he V hV hStop ≫ stopInclusion S hK he

private theorem combinedMap_open : LocallyRingedSpace.IsOpenImmersion (combinedMap S hK he V hV hStop).hom.left :=
  @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ (newMap S hK he V hV hStop).hom.left
    (OriginalNativePrescribedHistoryRefinement.inclusion_isOpenImmersion _ _ _ _ _ _)
    (stopInclusion S hK he).hom.left
    (OriginalNativeHSOuterEmptyStop.sourceInclusion_isOpenImmersion _ _ _ _)

private theorem combinedRange : range (combinedMap S hK he V hV hStop).hom.left.base =
    (S.history.projection ≫ S.inclusion).hom.left.base ⁻¹' (V : Set X.obj.left) := by
  ext y
  constructor
  · rintro ⟨z,rfl⟩
    have hz : (newMap S hK he V hV hStop).hom.left.base z ∈
        range (newMap S hK he V hV hStop).hom.left.base := ⟨z,rfl⟩
    rw [OriginalNativePrescribedHistoryRefinement.inclusion_range] at hz
    have ep := congrArg (fun f : (S₀).source ⟶ X => f.hom.left.base
      ((newMap S hK he V hV hStop).hom.left.base z)) (stopped_projection_square S hK he)
    change (S₀).inclusion.hom.left.base ((S₀).history.projection.hom.left.base
      ((newMap S hK he V hV hStop).hom.left.base z)) ∈ V at hz
    change S.inclusion.hom.left.base (S.history.projection.hom.left.base
      ((stopInclusion S hK he).hom.left.base ((newMap S hK he V hV hStop).hom.left.base z))) ∈ V
    exact ep ▸ hz
  · intro hy
    obtain ⟨u,hu⟩ := hStop (subset_closure hy)
    let N := OriginalNativeHSOuterEmptyStop.neighbourhood S.history (baseShadow S) (baseShadow_compact S hK) he
    have hbase : N.inclusion.hom.left.base u = S.history.projection.hom.left.base y :=
      S.inclusion_isOpenImmersion.base_open.injective hu
    have hyGood : S.history.projection.hom.left.base y ∈ N.openSet := hbase ▸ u.property
    let z₀ : (S₀).source.obj.left := ⟨y,hyGood⟩
    have ep := congrArg (fun f : (S₀).source ⟶ X => f.hom.left.base z₀) (stopped_projection_square S hK he)
    have hzOrig : (S₀).inclusion.hom.left.base ((S₀).history.projection.hom.left.base z₀) ∈ V := ep.symm ▸ hy
    have hzRange : z₀ ∈ range (newMap S hK he V hV hStop).hom.left.base :=
      (Set.ext_iff.mp (OriginalNativePrescribedHistoryRefinement.inclusion_range
        (S₀).inclusion (S₀).inclusion_isOpenImmersion V hV hStop (S₀).history) z₀).mpr hzOrig
    obtain ⟨z,hz⟩ := hzRange
    exact ⟨z,congrArg (stopInclusion S hK he).hom.left.base hz⟩

private theorem range_eq : range (combinedMap S hK he V hV hStop).hom.left.base =
    range (oldMap S V hV hOld).hom.left.base :=
  (combinedRange S hK he V hV hStop).trans
    (OriginalNativePrescribedHistoryRefinement.inclusion_range S.inclusion S.inclusion_isOpenImmersion V hV hOld S.history).symm

private def forward : stoppedSource S hK he V hV hStop ⟶ oldSource S V hV hOld :=
  (OriginalNativeSmoothOpenLocality.exists_native_open_lift (oldMap S V hV hOld)
    (combinedMap S hK he V hV hStop)
    (OriginalNativePrescribedHistoryRefinement.inclusion_isOpenImmersion _ _ _ _ _ _)
    (combinedMap_open S hK he V hV hStop) (range_eq S hK he V hV hOld hStop).subset).choose
private def backward : oldSource S V hV hOld ⟶ stoppedSource S hK he V hV hStop :=
  (OriginalNativeSmoothOpenLocality.exists_native_open_lift (combinedMap S hK he V hV hStop)
    (oldMap S V hV hOld) (combinedMap_open S hK he V hV hStop)
    (OriginalNativePrescribedHistoryRefinement.inclusion_isOpenImmersion _ _ _ _ _ _)
    (range_eq S hK he V hV hOld hStop).symm.subset).choose

private theorem forward_square : forward S hK he V hV hOld hStop ≫ oldMap S V hV hOld =
    combinedMap S hK he V hV hStop :=
  (OriginalNativeSmoothOpenLocality.exists_native_open_lift (oldMap S V hV hOld)
    (combinedMap S hK he V hV hStop)
    (OriginalNativePrescribedHistoryRefinement.inclusion_isOpenImmersion _ _ _ _ _ _)
    (combinedMap_open S hK he V hV hStop) (range_eq S hK he V hV hOld hStop).subset).choose_spec.2
private theorem backward_square : backward S hK he V hV hOld hStop ≫ combinedMap S hK he V hV hStop =
    oldMap S V hV hOld :=
  (OriginalNativeSmoothOpenLocality.exists_native_open_lift (combinedMap S hK he V hV hStop)
    (oldMap S V hV hOld) (combinedMap_open S hK he V hV hStop)
    (OriginalNativePrescribedHistoryRefinement.inclusion_isOpenImmersion _ _ _ _ _ _)
    (range_eq S hK he V hV hOld hStop).symm.subset).choose_spec.2

/-- The ACTUAL computed stop and SAME old history over the SAME prescribed V. -/
def stoppedComparison : stoppedSource S hK he V hV hStop ≅ oldSource S V hV hOld where
  hom := forward S hK he V hV hOld hStop
  inv := backward S hK he V hV hOld hStop
  hom_inv_id := by
    apply native_cancel _ _ (combinedMap S hK he V hV hStop) (combinedMap_open S hK he V hV hStop)
    rw [Category.assoc,backward_square,forward_square,Category.id_comp]
  inv_hom_id := by
    apply native_cancel _ _ (oldMap S V hV hOld)
      (OriginalNativePrescribedHistoryRefinement.inclusion_isOpenImmersion _ _ _ _ _ _)
    rw [Category.assoc,forward_square,backward_square,Category.id_comp]

theorem stoppedComparison_saved_source : (stoppedComparison S hK he V hV hOld hStop).hom ≫
    oldMap S V hV hOld = newMap S hK he V hV hStop ≫ stopInclusion S hK he :=
  forward_square S hK he V hV hOld hStop

theorem stoppedComparison_projection : (stoppedComparison S hK he V hV hOld hStop).hom ≫
    oldProjection S V hV hOld = stoppedProjection S hK he V hV hStop := by
  apply native_cancel _ _ (inclusion X V hV) (inclusion_isOpenImmersion X V hV)
  calc
    _ = (stoppedComparison S hK he V hV hOld hStop).hom ≫
        (oldMap S V hV hOld ≫ S.history.projection ≫ S.inclusion) := by
      rw [Category.assoc]
      exact congrArg (fun f => (stoppedComparison S hK he V hV hOld hStop).hom ≫ f)
        (OriginalNativePrescribedHistoryRefinement.original_square S.inclusion S.inclusion_isOpenImmersion V hV hOld S.history)
    _ = combinedMap S hK he V hV hStop ≫ S.history.projection ≫ S.inclusion := by
      rw [← Category.assoc,← Category.assoc,stoppedComparison_saved_source]
      exact Category.assoc _ _ _
    _ = newMap S hK he V hV hStop ≫ ((stopInclusion S hK he) ≫ S.history.projection ≫ S.inclusion) := by
      simp only [combinedMap,Category.assoc]
    _ = newMap S hK he V hV hStop ≫ ((S₀).history.projection ≫ (S₀).inclusion) :=
      congrArg (fun f => newMap S hK he V hV hStop ≫ f) (stopped_projection_square S hK he).symm
    _ = stoppedProjection S hK he V hV hStop ≫ inclusion X V hV :=
      (OriginalNativePrescribedHistoryRefinement.original_square (S₀).inclusion
        (S₀).inclusion_isOpenImmersion V hV hStop (S₀).history).symm

theorem stoppedComparison_inverse_projection : (stoppedComparison S hK he V hV hOld hStop).inv ≫
    stoppedProjection S hK he V hV hStop = oldProjection S V hV hOld := by
  rw [← stoppedComparison_projection,← Category.assoc,Iso.inv_hom_id,Category.id_comp]

theorem stoppedComparison_scalar : (stoppedComparison S hK he V hV hOld hStop).hom.hom.left ≫
    (oldSource S V hV hOld).obj.hom = (stoppedSource S hK he V hV hStop).obj.hom :=
  Over.w (stoppedComparison S hK he V hV hOld hStop).hom.hom

end OneStop

section TwoStops
variable {X : SourceReducedComplexSpace} {K₁ K₂ : Set X.obj.left}
  (S : State X K₁) (T : State X K₂) (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
  (heS : singularShadow S = ∅) (heT : singularShadow T = ∅)
  (W : Opens X.obj.left) (hW : IsCompact (closure (W : Set X.obj.left)))
  (hRS : closure (W : Set X.obj.left) ⊆ range S.inclusion.hom.left.base)
  (hRT : closure (W : Set X.obj.left) ⊆ range T.inclusion.hom.left.base)
  (α : oldSource S W hW hRS ≅ oldSource T W hW hRT)
  (hα : α.hom ≫ oldProjection T W hW hRT = oldProjection S W hW hRS)
  (L : Set X.obj.left) (hL : IsCompact L) (hLW : L ⊆ (W : Set X.obj.left))
  (hLK₁ : L ⊆ K₁) (hLK₂ : L ⊆ K₂)

private def goodOpen : Opens X.obj.left :=
  ⟨(W : Set X.obj.left) ∩ range (stopped S hK₁ heS).inclusion.hom.left.base ∩
      range (stopped T hK₂ heT).inclusion.hom.left.base,
    (W.isOpen.inter (stopped S hK₁ heS).inclusion_isOpenImmersion.base_open.isOpen_range).inter
      (stopped T hK₂ heT).inclusion_isOpenImmersion.base_open.isOpen_range⟩

include hLW hLK₁ hLK₂ in
private theorem compact_good : L ⊆ goodOpen S T hK₁ hK₂ heS heT W := by
  intro x hx
  exact ⟨⟨hLW hx,(stopped S hK₁ heS).contains (hLK₁ hx)⟩,(stopped T hK₂ heT).contains (hLK₂ hx)⟩

def neighbourhood := OriginalNativePrecompactNeighbourhood.neighbourhood X L hL
  (goodOpen S T hK₁ hK₂ heS heT W) (compact_good S T hK₁ hK₂ heS heT W L hLW hLK₁ hLK₂)

local notation "N" => neighbourhood S T hK₁ hK₂ heS heT W L hL hLW hLK₁ hLK₂

/-- The chosen ORIGINAL V retains ALL L, with closure genuinely in the old W. -/
theorem closure_subset_old : closure ((N).openSet : Set X.obj.left) ⊆ (W : Set X.obj.left) :=
  fun _ hx => ((N).closure_subset hx).1.1

theorem closure_subset_stop_left : closure ((N).openSet : Set X.obj.left) ⊆
    range (stopped S hK₁ heS).inclusion.hom.left.base := fun _ hx => ((N).closure_subset hx).1.2

theorem closure_subset_stop_right : closure ((N).openSet : Set X.obj.left) ⊆
    range (stopped T hK₂ heT).inclusion.hom.left.base := fun _ hx => ((N).closure_subset hx).2

theorem compact_retained : L ⊆ (N).openSet := (N).contains

theorem open_le_old : (N).openSet ≤ W := fun _ hx => closure_subset_old S T hK₁ hK₂ heS heT W L hL hLW hLK₁ hLK₂ (subset_closure hx)

include hRS in
private theorem range_old_left : closure ((N).openSet : Set X.obj.left) ⊆ range S.inclusion.hom.left.base :=
  OriginalNativePrescribedHistoryRefinement.smallerRange S.inclusion W hRS (N).openSet
    (open_le_old S T hK₁ hK₂ heS heT W L hL hLW hLK₁ hLK₂)
include hRT in
private theorem range_old_right : closure ((N).openSet : Set X.obj.left) ⊆ range T.inclusion.hom.left.base :=
  OriginalNativePrescribedHistoryRefinement.smallerRange T.inclusion W hRT (N).openSet
    (open_le_old S T hK₁ hK₂ heS heT W L hL hLW hLK₁ hLK₂)

/-- Full actual STOP--STOP endpoint comparison, through the genuinely restricted PAST iso. -/
def comparison : stoppedSource S hK₁ heS (N).openSet (N).compactClosure
      (closure_subset_stop_left S T hK₁ hK₂ heS heT W L hL hLW hLK₁ hLK₂) ≅
    stoppedSource T hK₂ heT (N).openSet (N).compactClosure
      (closure_subset_stop_right S T hK₁ hK₂ heS heT W L hL hLW hLK₁ hLK₂) :=
  stoppedComparison S hK₁ heS (N).openSet (N).compactClosure
      (range_old_left S T hK₁ hK₂ heS heT W hRS L hL hLW hLK₁ hLK₂)
      (closure_subset_stop_left S T hK₁ hK₂ heS heT W L hL hLW hLK₁ hLK₂) ≪≫
    OriginalNativePrescribedHistoryRefinement.restrictedIso S.inclusion S.inclusion_isOpenImmersion W hW hRS S.history
      (N).openSet (N).compactClosure (open_le_old S T hK₁ hK₂ heS heT W L hL hLW hLK₁ hLK₂)
      T.inclusion T.inclusion_isOpenImmersion hRT T.history α hα ≪≫
    (stoppedComparison T hK₂ heT (N).openSet (N).compactClosure
      (range_old_right S T hK₁ hK₂ heS heT W hRT L hL hLW hLK₁ hLK₂)
      (closure_subset_stop_right S T hK₁ hK₂ heS heT W L hL hLW hLK₁ hLK₂)).symm

theorem comparison_projection : (comparison S T hK₁ hK₂ heS heT W hW hRS hRT α hα L hL hLW hLK₁ hLK₂).hom ≫
    stoppedProjection T hK₂ heT (N).openSet (N).compactClosure
      (closure_subset_stop_right S T hK₁ hK₂ heS heT W L hL hLW hLK₁ hLK₂) =
    stoppedProjection S hK₁ heS (N).openSet (N).compactClosure
      (closure_subset_stop_left S T hK₁ hK₂ heS heT W L hL hLW hLK₁ hLK₂) := by
  simp only [comparison,Iso.trans_hom,Iso.symm_hom,Category.assoc]
  rw [stoppedComparison_inverse_projection]
  rw [OriginalNativePrescribedHistoryRefinement.restrictedIso_projection]
  exact stoppedComparison_projection _ _ _ _ _ _ _

theorem comparison_original_square : (comparison S T hK₁ hK₂ heS heT W hW hRS hRT α hα L hL hLW hLK₁ hLK₂).hom ≫
    stoppedProjection T hK₂ heT (N).openSet (N).compactClosure
      (closure_subset_stop_right S T hK₁ hK₂ heS heT W L hL hLW hLK₁ hLK₂) ≫ (N).inclusion =
    stoppedProjection S hK₁ heS (N).openSet (N).compactClosure
      (closure_subset_stop_left S T hK₁ hK₂ heS heT W L hL hLW hLK₁ hLK₂) ≫ (N).inclusion := by
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun f => f ≫ inclusion X (N).openSet (N).compactClosure)
      (comparison_projection S T hK₁ hK₂ heS heT W hW hRS hRT α hα L hL hLW hLK₁ hLK₂))

theorem comparison_scalar : (comparison S T hK₁ hK₂ heS heT W hW hRS hRT α hα L hL hLW hLK₁ hLK₂).hom.hom.left ≫
    (stoppedSource T hK₂ heT (N).openSet (N).compactClosure
      (closure_subset_stop_right S T hK₁ hK₂ heS heT W L hL hLW hLK₁ hLK₂)).obj.hom =
    (stoppedSource S hK₁ heS (N).openSet (N).compactClosure
      (closure_subset_stop_left S T hK₁ hK₂ heS heT W L hL hLW hLK₁ hLK₂)).obj.hom :=
  Over.w (comparison S T hK₁ hK₂ heS heT W hW hRS hRT α hα L hL hLW hLK₁ hLK₂).hom.hom

end TwoStops
end
end Hironaka.Analytic.Unibranch.OriginalNativeHSStoppedEndpointComparison
