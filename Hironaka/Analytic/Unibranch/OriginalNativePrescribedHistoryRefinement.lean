import Hironaka.Analytic.Unibranch.OriginalNativePrescribedOpenHistory
import Hironaka.Analytic.Unibranch.OriginalNativeSmoothOpenLocality

/-! Actual smaller-ORIGINAL-open restriction of a PRESENT finite history and
of an ACTUAL old native comparison. No future-case/comparison packet.
Blueprint FIRST: original-native-prescribed-history-refinement.tex. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativePrescribedHistoryRefinement
noncomputable section
open SourceReducedComplexSpace OriginalNativeHSOuterHistory OriginalRelativelyCompactRestriction

variable {X B Y : SourceReducedComplexSpace} (j : B ⟶ X)
  (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left)
  (W : Opens X.obj.left) (hW : IsCompact (closure (W : Set X.obj.left)))
  (hRange : closure (W : Set X.obj.left) ⊆ range j.hom.left.base)
  (h : PhysicalHistory B Y)

abbrev source := OriginalNativePrescribedOpenHistory.source j hj W hW hRange h

def history : PhysicalHistory (restriction X W hW) (source j hj W hW hRange h) :=
  OriginalNativePrescribedOpenHistory.history j hj W hW hRange h

def projection : source j hj W hW hRange h ⟶ restriction X W hW := (history j hj W hW hRange h).projection

def inclusion : source j hj W hW hRange h ⟶ Y :=
  OriginalNativePrescribedOpenHistory.sourceInclusion j hj W hW hRange h

theorem inclusion_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion (inclusion j hj W hW hRange h).hom.left :=
  OriginalNativePrescribedOpenHistory.sourceInclusion_isOpenImmersion j hj W hW hRange h

theorem inclusion_range : range (inclusion j hj W hW hRange h).hom.left.base =
    (h.projection ≫ j).hom.left.base ⁻¹' (W : Set X.obj.left) := by
  change range (Subtype.val : {y : Y.obj.left // j.hom.left.base (h.projection.hom.left.base y) ∈ W} → Y.obj.left) = _
  exact Subtype.range_coe

theorem original_square : projection j hj W hW hRange h ≫ OriginalRelativelyCompactRestriction.inclusion X W hW =
    inclusion j hj W hW hRange h ≫ h.projection ≫ j :=
  OriginalNativePrescribedOpenHistory.projection_square j hj W hW hRange h

variable (V : Opens X.obj.left) (hV : IsCompact (closure (V : Set X.obj.left))) (hVW : V ≤ W)

include hRange hVW in
theorem smallerRange : closure (V : Set X.obj.left) ⊆ range j.hom.left.base :=
  (closure_mono hVW).trans hRange

def targetMap : restriction X V hV ⟶ restriction X W hW :=
  (OriginalNativeSmoothOpenLocality.exists_native_open_lift
    (OriginalRelativelyCompactRestriction.inclusion X W hW) (OriginalRelativelyCompactRestriction.inclusion X V hV)
    (OriginalRelativelyCompactRestriction.inclusion_isOpenImmersion X W hW)
    (OriginalRelativelyCompactRestriction.inclusion_isOpenImmersion X V hV)
    (by rw [OriginalRelativelyCompactRestriction.inclusion_range,OriginalRelativelyCompactRestriction.inclusion_range];exact hVW)).choose

theorem targetMap_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion (targetMap W hW V hV hVW).hom.left :=
  (OriginalNativeSmoothOpenLocality.exists_native_open_lift
    (OriginalRelativelyCompactRestriction.inclusion X W hW) (OriginalRelativelyCompactRestriction.inclusion X V hV)
    (OriginalRelativelyCompactRestriction.inclusion_isOpenImmersion X W hW)
    (OriginalRelativelyCompactRestriction.inclusion_isOpenImmersion X V hV)
    (by rw [OriginalRelativelyCompactRestriction.inclusion_range,OriginalRelativelyCompactRestriction.inclusion_range];exact hVW)).choose_spec.1

theorem targetMap_square : targetMap W hW V hV hVW ≫ OriginalRelativelyCompactRestriction.inclusion X W hW =
    OriginalRelativelyCompactRestriction.inclusion X V hV :=
  (OriginalNativeSmoothOpenLocality.exists_native_open_lift
    (OriginalRelativelyCompactRestriction.inclusion X W hW) (OriginalRelativelyCompactRestriction.inclusion X V hV)
    (OriginalRelativelyCompactRestriction.inclusion_isOpenImmersion X W hW)
    (OriginalRelativelyCompactRestriction.inclusion_isOpenImmersion X V hV)
    (by rw [OriginalRelativelyCompactRestriction.inclusion_range,OriginalRelativelyCompactRestriction.inclusion_range];exact hVW)).choose_spec.2

private theorem smaller_range_subset :
    range (inclusion j hj V hV (smallerRange j W hRange V hVW) h).hom.left.base ⊆
      range (inclusion j hj W hW hRange h).hom.left.base := by
  rw [inclusion_range,inclusion_range]
  exact fun _ hy => hVW hy

def sourceMap : source j hj V hV (smallerRange j W hRange V hVW) h ⟶ source j hj W hW hRange h :=
  (OriginalNativeSmoothOpenLocality.exists_native_open_lift (inclusion j hj W hW hRange h)
    (inclusion j hj V hV (smallerRange j W hRange V hVW) h) (inclusion_isOpenImmersion j hj W hW hRange h)
    (inclusion_isOpenImmersion j hj V hV (smallerRange j W hRange V hVW) h)
    (smaller_range_subset j hj W hW hRange h V hV hVW)).choose

theorem sourceMap_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion (sourceMap j hj W hW hRange h V hV hVW).hom.left :=
  (OriginalNativeSmoothOpenLocality.exists_native_open_lift (inclusion j hj W hW hRange h)
    (inclusion j hj V hV (smallerRange j W hRange V hVW) h) (inclusion_isOpenImmersion j hj W hW hRange h)
    (inclusion_isOpenImmersion j hj V hV (smallerRange j W hRange V hVW) h)
    (smaller_range_subset j hj W hW hRange h V hV hVW)).choose_spec.1

theorem sourceMap_inclusion : sourceMap j hj W hW hRange h V hV hVW ≫ inclusion j hj W hW hRange h =
    inclusion j hj V hV (smallerRange j W hRange V hVW) h :=
  (OriginalNativeSmoothOpenLocality.exists_native_open_lift (inclusion j hj W hW hRange h)
    (inclusion j hj V hV (smallerRange j W hRange V hVW) h) (inclusion_isOpenImmersion j hj W hW hRange h)
    (inclusion_isOpenImmersion j hj V hV (smallerRange j W hRange V hVW) h)
    (smaller_range_subset j hj W hW hRange h V hV hVW)).choose_spec.2

theorem sourceMap_projection : sourceMap j hj W hW hRange h V hV hVW ≫ projection j hj W hW hRange h =
    projection j hj V hV (smallerRange j W hRange V hVW) h ≫ targetMap W hW V hV hVW := by
  have hs : (sourceMap j hj W hW hRange h V hV hVW ≫ projection j hj W hW hRange h) ≫
      OriginalRelativelyCompactRestriction.inclusion X W hW =
      (projection j hj V hV (smallerRange j W hRange V hVW) h ≫ targetMap W hW V hV hVW) ≫
        OriginalRelativelyCompactRestriction.inclusion X W hW := by
    calc
      _ = sourceMap j hj W hW hRange h V hV hVW ≫
          (inclusion j hj W hW hRange h ≫ h.projection ≫ j) := by rw [Category.assoc,original_square]
      _ = inclusion j hj V hV (smallerRange j W hRange V hVW) h ≫ h.projection ≫ j := by
        rw [← Category.assoc,← Category.assoc,sourceMap_inclusion]
        exact Category.assoc _ _ _
      _ = projection j hj V hV (smallerRange j W hRange V hVW) h ≫
          OriginalRelativelyCompactRestriction.inclusion X V hV := (original_square j hj V hV _ h).symm
      _ = _ := by rw [Category.assoc,targetMap_square]
  let : LocallyRingedSpace.IsOpenImmersion (OriginalRelativelyCompactRestriction.inclusion X W hW).hom.left :=
    OriginalRelativelyCompactRestriction.inclusion_isOpenImmersion X W hW
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply (cancel_mono (OriginalRelativelyCompactRestriction.inclusion X W hW).hom.left).mp
  exact congrArg (fun f => f.hom.left) hs

theorem sourceMap_range : range (sourceMap j hj W hW hRange h V hV hVW).hom.left.base =
    (projection j hj W hW hRange h ≫ OriginalRelativelyCompactRestriction.inclusion X W hW).hom.left.base ⁻¹'
      (V : Set X.obj.left) := by
  ext y
  constructor
  · rintro ⟨z,rfl⟩
    have hs := congrArg (fun f => f.hom.left.base z) (sourceMap_inclusion j hj W hW hRange h V hV hVW)
    have hz : (inclusion j hj V hV (smallerRange j W hRange V hVW) h).hom.left.base z ∈
        range (inclusion j hj V hV (smallerRange j W hRange V hVW) h).hom.left.base := ⟨z,rfl⟩
    rw [inclusion_range] at hz
    rw [original_square]
    change j.hom.left.base (h.projection.hom.left.base ((inclusion j hj W hW hRange h).hom.left.base
      ((sourceMap j hj W hW hRange h V hV hVW).hom.left.base z))) ∈ V
    change (inclusion j hj W hW hRange h).hom.left.base ((sourceMap j hj W hW hRange h V hV hVW).hom.left.base z) =
      (inclusion j hj V hV (smallerRange j W hRange V hVW) h).hom.left.base z at hs
    rw [hs]
    exact hz
  · intro hy
    have hy' : (inclusion j hj W hW hRange h).hom.left.base y ∈
        range (inclusion j hj V hV (smallerRange j W hRange V hVW) h).hom.left.base := by
      rw [inclusion_range]
      change ((inclusion j hj W hW hRange h ≫ h.projection ≫ j).hom.left.base y) ∈ V
      rw [← original_square]
      exact hy
    obtain ⟨z,hz⟩ := hy'
    refine ⟨z,(inclusion_isOpenImmersion j hj W hW hRange h).base_open.injective ?_⟩
    exact (congrArg (fun f => f.hom.left.base z) (sourceMap_inclusion j hj W hW hRange h V hV hVW)).trans hz

theorem sourceMap_scalar : (sourceMap j hj W hW hRange h V hV hVW).hom.left ≫
    (source j hj W hW hRange h).obj.hom = (source j hj V hV (smallerRange j W hRange V hVW) h).obj.hom :=
  Over.w (sourceMap j hj W hW hRange h V hV hVW).hom


private theorem native_cancel {A C D : SourceReducedComplexSpace} (a b : A ⟶ C) (f : C ⟶ D)
    (hf : LocallyRingedSpace.IsOpenImmersion f.hom.left) (hab : a ≫ f = b ≫ f) : a = b := by
  let : LocallyRingedSpace.IsOpenImmersion f.hom.left := hf
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply (cancel_mono f.hom.left).mp
  exact congrArg (fun k => k.hom.left) hab

variable {B' Y' : SourceReducedComplexSpace} (j' : B' ⟶ X)
  (hj' : LocallyRingedSpace.IsOpenImmersion j'.hom.left)
  (hRange' : closure (W : Set X.obj.left) ⊆ range j'.hom.left.base)
  (h' : PhysicalHistory B' Y')
  (α : source j hj W hW hRange h ≅ source j' hj' W hW hRange' h')
  (hα : α.hom ≫ projection j' hj' W hW hRange' h' = projection j hj W hW hRange h)

private theorem iso_open {A C : SourceReducedComplexSpace} (e : A ≅ C) :
    LocallyRingedSpace.IsOpenImmersion e.hom.hom.left := by
  change LocallyRingedSpace.IsOpenImmersion (isoLeft e).hom
  infer_instance

include hα in
private theorem mapped_range :
    range (sourceMap j hj W hW hRange h V hV hVW ≫ α.hom).hom.left.base ⊆
      range (sourceMap j' hj' W hW hRange' h' V hV hVW).hom.left.base := by
  rintro y ⟨z,rfl⟩
  rw [sourceMap_range]
  have hs := congrArg (fun f => f.hom.left.base ((sourceMap j hj W hW hRange h V hV hVW).hom.left.base z)) hα
  change (projection j' hj' W hW hRange' h').hom.left.base
      (α.hom.hom.left.base ((sourceMap j hj W hW hRange h V hV hVW).hom.left.base z)) =
    (projection j hj W hW hRange h).hom.left.base ((sourceMap j hj W hW hRange h V hV hVW).hom.left.base z) at hs
  change (OriginalRelativelyCompactRestriction.inclusion X W hW).hom.left.base
    ((projection j' hj' W hW hRange' h').hom.left.base
      (α.hom.hom.left.base ((sourceMap j hj W hW hRange h V hV hVW).hom.left.base z))) ∈ V
  rw [hs]
  have hm : (sourceMap j hj W hW hRange h V hV hVW).hom.left.base z ∈
      range (sourceMap j hj W hW hRange h V hV hVW).hom.left.base := ⟨z,rfl⟩
  rw [sourceMap_range] at hm
  exact hm

private def forward : source j hj V hV (smallerRange j W hRange V hVW) h ⟶
    source j' hj' V hV (smallerRange j' W hRange' V hVW) h' :=
  (OriginalNativeSmoothOpenLocality.exists_native_open_lift (sourceMap j' hj' W hW hRange' h' V hV hVW)
    (sourceMap j hj W hW hRange h V hV hVW ≫ α.hom)
    (sourceMap_isOpenImmersion j' hj' W hW hRange' h' V hV hVW)
    (@LocallyRingedSpace.IsOpenImmersion.comp _ _ _ (sourceMap j hj W hW hRange h V hV hVW).hom.left
      (sourceMap_isOpenImmersion j hj W hW hRange h V hV hVW) α.hom.hom.left (iso_open α))
    (mapped_range j hj W hW hRange h V hV hVW j' hj' hRange' h' α hα)).choose

private theorem forward_square : forward j hj W hW hRange h V hV hVW j' hj' hRange' h' α hα ≫
    sourceMap j' hj' W hW hRange' h' V hV hVW = sourceMap j hj W hW hRange h V hV hVW ≫ α.hom :=
  (OriginalNativeSmoothOpenLocality.exists_native_open_lift (sourceMap j' hj' W hW hRange' h' V hV hVW)
    (sourceMap j hj W hW hRange h V hV hVW ≫ α.hom)
    (sourceMap_isOpenImmersion j' hj' W hW hRange' h' V hV hVW)
    (@LocallyRingedSpace.IsOpenImmersion.comp _ _ _ (sourceMap j hj W hW hRange h V hV hVW).hom.left
      (sourceMap_isOpenImmersion j hj W hW hRange h V hV hVW) α.hom.hom.left (iso_open α))
    (mapped_range j hj W hW hRange h V hV hVW j' hj' hRange' h' α hα)).choose_spec.2

include hα in
private theorem inverse_projection : α.inv ≫ projection j hj W hW hRange h =
    projection j' hj' W hW hRange' h' := by
  rw [← hα,← Category.assoc,α.inv_hom_id,Category.id_comp]

/-- Restrict the ACTUAL old comparison through genuine smaller-source OIs. -/
def restrictedIso : source j hj V hV (smallerRange j W hRange V hVW) h ≅
    source j' hj' V hV (smallerRange j' W hRange' V hVW) h' := by
  let a := forward j hj W hW hRange h V hV hVW j' hj' hRange' h' α hα
  let b := forward j' hj' W hW hRange' h' V hV hVW j hj hRange h α.symm
    (inverse_projection j hj W hW hRange h j' hj' hRange' h' α hα)
  have ha : a ≫ sourceMap j' hj' W hW hRange' h' V hV hVW =
      sourceMap j hj W hW hRange h V hV hVW ≫ α.hom :=
    forward_square j hj W hW hRange h V hV hVW j' hj' hRange' h' α hα
  have hb : b ≫ sourceMap j hj W hW hRange h V hV hVW =
      sourceMap j' hj' W hW hRange' h' V hV hVW ≫ α.inv :=
    forward_square j' hj' W hW hRange' h' V hV hVW j hj hRange h α.symm
      (inverse_projection j hj W hW hRange h j' hj' hRange' h' α hα)
  refine ⟨a,b,?_,?_⟩
  · apply native_cancel _ _ (sourceMap j hj W hW hRange h V hV hVW)
      (sourceMap_isOpenImmersion j hj W hW hRange h V hV hVW)
    rw [Category.assoc,hb,← Category.assoc,ha,Category.assoc,α.hom_inv_id,Category.comp_id,Category.id_comp]
  · apply native_cancel _ _ (sourceMap j' hj' W hW hRange' h' V hV hVW)
      (sourceMap_isOpenImmersion j' hj' W hW hRange' h' V hV hVW)
    rw [Category.assoc,ha,← Category.assoc,hb,Category.assoc,α.inv_hom_id,Category.comp_id,Category.id_comp]

theorem restrictedIso_source_square :
    (restrictedIso j hj W hW hRange h V hV hVW j' hj' hRange' h' α hα).hom ≫
      sourceMap j' hj' W hW hRange' h' V hV hVW = sourceMap j hj W hW hRange h V hV hVW ≫ α.hom :=
  forward_square j hj W hW hRange h V hV hVW j' hj' hRange' h' α hα

theorem restrictedIso_projection :
    (restrictedIso j hj W hW hRange h V hV hVW j' hj' hRange' h' α hα).hom ≫
      projection j' hj' V hV (smallerRange j' W hRange' V hVW) h' =
      projection j hj V hV (smallerRange j W hRange V hVW) h := by
  apply native_cancel _ _ (targetMap W hW V hV hVW) (targetMap_isOpenImmersion W hW V hV hVW)
  calc
    _ = (restrictedIso j hj W hW hRange h V hV hVW j' hj' hRange' h' α hα).hom ≫
        (sourceMap j' hj' W hW hRange' h' V hV hVW ≫ projection j' hj' W hW hRange' h') := by
      rw [Category.assoc,← sourceMap_projection]
    _ = sourceMap j hj W hW hRange h V hV hVW ≫ α.hom ≫ projection j' hj' W hW hRange' h' := by
      rw [← Category.assoc,restrictedIso_source_square,Category.assoc]
    _ = sourceMap j hj W hW hRange h V hV hVW ≫ projection j hj W hW hRange h := by rw [hα]
    _ = _ := sourceMap_projection j hj W hW hRange h V hV hVW

theorem restrictedIso_scalar :
    (restrictedIso j hj W hW hRange h V hV hVW j' hj' hRange' h' α hα).hom.hom.left ≫
      (source j' hj' V hV (smallerRange j' W hRange' V hVW) h').obj.hom =
      (source j hj V hV (smallerRange j W hRange V hVW) h).obj.hom :=
  Over.w (restrictedIso j hj W hW hRange h V hV hVW j' hj' hRange' h' α hα).hom.hom

end
end Hironaka.Analytic.Unibranch.OriginalNativePrescribedHistoryRefinement
