import Hironaka.Analytic.Unibranch.OriginalNativeHSShadowOuterState
import Hironaka.Analytic.Unibranch.OriginalNativePrescribedOpenHistory

/-! Honest PAST overlap for actual current outer states. Blueprint FIRST:
original-native-hs-current-overlap.tex. No next/future case supplier. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentOverlap
noncomputable section
open SourceReducedComplexSpace OriginalNativeHSOuterHistory OriginalNativeHSShadowOuterState
  OriginalRelativelyCompactRestriction

variable {X : SourceReducedComplexSpace} {K : Set X.obj.left}

def endpoint (S : State X K) (W : Opens X.obj.left)
    (hW : IsCompact (closure (W : Set X.obj.left)))
    (hRange : closure (W : Set X.obj.left) ⊆ range S.inclusion.hom.left.base) : SourceReducedComplexSpace :=
  OriginalNativePrescribedOpenHistory.source S.inclusion S.inclusion_isOpenImmersion W hW hRange S.history

def history (S : State X K) (W : Opens X.obj.left)
    (hW : IsCompact (closure (W : Set X.obj.left)))
    (hRange : closure (W : Set X.obj.left) ⊆ range S.inclusion.hom.left.base) :
    PhysicalHistory (restriction X W hW) (endpoint S W hW hRange) :=
  OriginalNativePrescribedOpenHistory.history S.inclusion S.inclusion_isOpenImmersion W hW hRange S.history

def inclusion (S : State X K) (W : Opens X.obj.left)
    (hW : IsCompact (closure (W : Set X.obj.left)))
    (hRange : closure (W : Set X.obj.left) ⊆ range S.inclusion.hom.left.base) : endpoint S W hW hRange ⟶ S.source :=
  OriginalNativePrescribedOpenHistory.sourceInclusion S.inclusion S.inclusion_isOpenImmersion W hW hRange S.history

/-- ONLY present W, its real current prescribed objects, and an actual PAST iso. -/
structure Context {K₁ K₂ : Set X.obj.left} (S : State X K₁) (T : State X K₂) (L : Set X.obj.left) where
  openSet : Opens X.obj.left
  compactClosure : IsCompact (closure (openSet : Set X.obj.left))
  contains : L ⊆ openSet
  leftRange : closure (openSet : Set X.obj.left) ⊆ range S.inclusion.hom.left.base
  rightRange : closure (openSet : Set X.obj.left) ⊆ range T.inclusion.hom.left.base
  comparison : endpoint S openSet compactClosure leftRange ≅ endpoint T openSet compactClosure rightRange
  square : comparison.hom ≫ (history T openSet compactClosure rightRange).projection=
    (history S openSet compactClosure leftRange).projection

namespace Context
variable {K₁ K₂ L : Set X.obj.left} {S : State X K₁} {T : State X K₂} (c : Context S T L)

def leftMap : endpoint S c.openSet c.compactClosure c.leftRange ⟶ S.source :=
  inclusion S c.openSet c.compactClosure c.leftRange

def rightMap : endpoint S c.openSet c.compactClosure c.leftRange ⟶ T.source :=
  c.comparison.hom ≫ inclusion T c.openSet c.compactClosure c.rightRange

def commonHistory : PhysicalHistory (restriction X c.openSet c.compactClosure)
    (endpoint S c.openSet c.compactClosure c.leftRange) := history S c.openSet c.compactClosure c.leftRange

def baseInclusion : restriction X c.openSet c.compactClosure ⟶ X :=
  OriginalRelativelyCompactRestriction.inclusion X c.openSet c.compactClosure

theorem leftMap_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion (leftMap c).hom.left :=
  OriginalNativePrescribedOpenHistory.sourceInclusion_isOpenImmersion S.inclusion S.inclusion_isOpenImmersion
    c.openSet c.compactClosure c.leftRange S.history

theorem rightMap_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion (rightMap c).hom.left := by
  have hα : LocallyRingedSpace.IsOpenImmersion c.comparison.hom.hom.left := by
    change LocallyRingedSpace.IsOpenImmersion (isoLeft c.comparison).hom
    infer_instance
  exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ _ hα _
    (OriginalNativePrescribedOpenHistory.sourceInclusion_isOpenImmersion T.inclusion T.inclusion_isOpenImmersion
      c.openSet c.compactClosure c.rightRange T.history)

theorem left_square : (commonHistory c).projection ≫ baseInclusion c=
    leftMap c ≫ S.history.projection ≫ S.inclusion :=
  OriginalNativePrescribedOpenHistory.projection_square S.inclusion S.inclusion_isOpenImmersion
    c.openSet c.compactClosure c.leftRange S.history

theorem right_square : (commonHistory c).projection ≫ baseInclusion c=
    rightMap c ≫ T.history.projection ≫ T.inclusion := by
  calc
    _ = (c.comparison.hom ≫ (history T c.openSet c.compactClosure c.rightRange).projection) ≫ baseInclusion c :=
      congrArg (fun p => p ≫ baseInclusion c) c.square.symm
    _ = c.comparison.hom ≫ ((history T c.openSet c.compactClosure c.rightRange).projection ≫ baseInclusion c) :=
      Category.assoc _ _ _
    _ = c.comparison.hom ≫ (inclusion T c.openSet c.compactClosure c.rightRange ≫ T.history.projection ≫ T.inclusion) :=
      congrArg (fun p => c.comparison.hom ≫ p)
        (OriginalNativePrescribedOpenHistory.projection_square T.inclusion T.inclusion_isOpenImmersion
          c.openSet c.compactClosure c.rightRange T.history)
    _ = _ := by simp only [rightMap,Category.assoc]

theorem left_range : range (leftMap c).hom.left.base =
    S.history.projection.hom.left.base ⁻¹' (S.inclusion.hom.left.base ⁻¹' (c.openSet : Set X.obj.left)) := by
  change range (Subtype.val : preimageOpen (OriginalNativePrescribedOpenHistory.pullbackOpen S.inclusion c.openSet)
    S.history.projection → S.source.obj.left) = _
  rw [Subtype.range_coe]
  rfl

theorem right_range : range (rightMap c).hom.left.base =
    T.history.projection.hom.left.base ⁻¹' (T.inclusion.hom.left.base ⁻¹' (c.openSet : Set X.obj.left)) := by
  have hr : range (rightMap c).hom.left.base = range (inclusion T c.openSet c.compactClosure c.rightRange).hom.left.base := by
    ext y
    constructor
    · rintro ⟨z,rfl⟩
      exact ⟨c.comparison.hom.hom.left.base z,rfl⟩
    · rintro ⟨z,hz⟩
      refine ⟨c.comparison.inv.hom.left.base z,?_⟩
      exact (congrArg (inclusion T c.openSet c.compactClosure c.rightRange).hom.left.base
        (congrArg (fun f => f.hom.left.base z) c.comparison.inv_hom_id)).trans hz
  rw [hr]
  change range (Subtype.val : preimageOpen (OriginalNativePrescribedOpenHistory.pullbackOpen T.inclusion c.openSet)
    T.history.projection → T.source.obj.left) = _
  rw [Subtype.range_coe]
  rfl

theorem left_fibre_covered : S.history.projection.hom.left.base ⁻¹'
    (S.inclusion.hom.left.base ⁻¹' L) ⊆ range (leftMap c).hom.left.base := by
  intro y hy
  rw [left_range]
  exact c.contains hy

theorem right_fibre_covered : T.history.projection.hom.left.base ⁻¹'
    (T.inclusion.hom.left.base ⁻¹' L) ⊆ range (rightMap c).hom.left.base := by
  intro y hy
  rw [right_range]
  exact c.contains hy

/-- ENTIRE inverse original compact fibre in the actual proper common history. -/
def commonCompact : Set (endpoint S c.openSet c.compactClosure c.leftRange).obj.left :=
  (commonHistory c).projection.hom.left.base ⁻¹' ((baseInclusion c).hom.left.base ⁻¹' L)

theorem commonCompact_isCompact (hL : IsCompact L) : IsCompact (commonCompact c) := by
  have hb : IsCompact ((baseInclusion c).hom.left.base ⁻¹' L) :=
    (inclusion_isOpenImmersion X c.openSet c.compactClosure).base_open.isEmbedding.isInducing.isCompact_preimage' hL
      (fun x hx => ⟨⟨x,c.contains hx⟩,rfl⟩)
  exact (commonHistory c).singularModification.isProperMap.isCompact_preimage hb

theorem left_image_in_shadow (hL : L ⊆ K₁) : (leftMap c).hom.left.base '' commonCompact c ⊆ shadow S := by
  rintro _ ⟨z,hz,rfl⟩
  have hs := congrArg (fun f => f.hom.left.base z) (left_square c)
  exact (congrArg (fun x : X.obj.left => x ∈ K₁) hs).mp (hL hz)

theorem right_image_in_shadow (hL : L ⊆ K₂) : (rightMap c).hom.left.base '' commonCompact c ⊆ shadow T := by
  rintro _ ⟨z,hz,rfl⟩
  have hs := congrArg (fun f => f.hom.left.base z) (right_square c)
  exact (congrArg (fun x : X.obj.left => x ∈ K₂) hs).mp (hL hz)

end Context

/-- Genuine initial identity on two ACTUAL nil-history states. -/
def initial {K₁ K₂ L : Set X.obj.left} (W : Opens X.obj.left)
    (hW : IsCompact (closure (W : Set X.obj.left))) (hL : L ⊆ W) :
    Context (OriginalNativeHSShadowOuterState.initial X K₁) (OriginalNativeHSShadowOuterState.initial X K₂) L where
  openSet := W
  compactClosure := hW
  contains := hL
  leftRange x _ := ⟨x,rfl⟩
  rightRange x _ := ⟨x,rfl⟩
  comparison := Iso.refl _
  square := Category.id_comp _

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentOverlap
