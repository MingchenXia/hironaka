import Hironaka.Analytic.Unibranch.OriginalNativeHSOuterPhaseCoupling
import Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentOverlap
import Hironaka.Analytic.Unibranch.OriginalNativeHSShadowOuterRun

/-! ONE actual original common base for the two computed next histories.
Blueprint FIRST: original-native-hs-next-common-base.tex.
Ordinary present states + actual PAST prescribed-history iso only;
properness is TO the literal current common base, never after its open inclusion. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSNextCommonBase
noncomputable section
open SourceReducedComplexSpace OriginalNativeHSOuterHistory OriginalNativeHSShadowOuterState
  OriginalNativeHSCurrentOverlap OriginalRelativelyCompactRestriction
  Hironaka.HironakaIntrinsicComplexAnalyticRegularLocus

variable {X : SourceReducedComplexSpace} {K₁ K₂ L : Set X.obj.left}
  {S : State X K₁} {T : State X K₂} (c : Context S T L)
  (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂) (hL : IsCompact L)
  (hL₁ : L ⊆ K₁) (hL₂ : L ⊆ K₂)
  (hneS : (singularShadow S).Nonempty) (hneT : (singularShadow T).Nonempty)

include hneS in
private theorem singularLeft : (shadow S ∩ intrinsicSingularLocus S.source.obj).Nonempty := by
  simpa only [singularShadow, inter_comm] using hneS
include hneT in
private theorem singularRight : (shadow T ∩ intrinsicSingularLocus T.source.obj).Nonempty := by
  simpa only [singularShadow, inter_comm] using hneT

local notation "aS" => Context.leftMap c
local notation "aT" => Context.rightMap c
local notation "haS" => Context.leftMap_isOpenImmersion c
local notation "haT" => Context.rightMap_isOpenImmersion c
local notation "C" => Context.commonCompact c
local notation "hC" => Context.commonCompact_isCompact c hL
local notation "hIS" => Context.left_image_in_shadow c hL₁
local notation "hIT" => Context.right_image_in_shadow c hL₂
local notation "Ω" => OriginalNativeHSOuterPhaseCoupling.overlapOpen S.history T.history
  (baseShadow S) (baseShadow T) (baseShadow_compact S hK₁) (baseShadow_compact T hK₂) hneS hneT (aS) (aT)
local notation "hΩ" => OriginalNativeHSOuterPhaseCoupling.compact_subset_overlap S.history T.history
  (baseShadow S) (baseShadow T) (baseShadow_compact S hK₁) (baseShadow_compact T hK₂) hneS hneT (aS) (aT) (C) (hIS) (hIT)

/-- SAME computed coupled phase neighbourhood; no new phase or endpoint choice. -/
def phaseNeighbourhood := OriginalNativeHSEqualProfilePhaseComparison.neighbourhood S.source T.source
  (shadow S) (shadow T) (shadow_compact S hK₁) (shadow_compact T hK₂)
  (singularLeft hneS) (singularRight hneT) (aS) (aT) (haS) (haT) (C) (hC) (hIS) (hIT) (Ω) (hΩ)

private abbrev nextS := OriginalNativeHSShadowOuterRun.next S hK₁ hneS
private abbrev nextT := OriginalNativeHSShadowOuterRun.next T hK₂ hneT
private abbrev base := restriction X c.openSet c.compactClosure
private abbrev commonSource := endpoint S c.openSet c.compactClosure c.leftRange
private abbrev r : commonSource c ⟶ base c := (Context.commonHistory c).projection
private abbrev iW : base c ⟶ X := Context.baseInclusion c
private abbrev O := (phaseNeighbourhood c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).openSet
private def goodBase : Opens (base c).obj.left :=
  OriginalNativeProperFibreShrink.goodBase (r c) (Context.commonHistory c).singularModification.isProperMap
    (O c hK₁ hK₂ hL hL₁ hL₂ hneS hneT)

private theorem compact_in_goodBase : (iW c).hom.left.base ⁻¹' L ⊆
    (goodBase c hK₁ hK₂ hL hL₁ hL₂ hneS hneT : Set (base c).obj.left) :=
  OriginalNativeProperFibreShrink.compact_subset_goodBase (r c)
    (Context.commonHistory c).singularModification.isProperMap
    (O c hK₁ hK₂ hL hL₁ hL₂ hneS hneT)
    (phaseNeighbourhood c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).contains

private def originalGood : Opens X.obj.left :=
  ⟨((iW c).hom.left.base '' (goodBase c hK₁ hK₂ hL hL₁ hL₂ hneS hneT : Set (base c).obj.left)) ∩
      range (nextS hK₁ hneS).inclusion.hom.left.base ∩ range (nextT hK₂ hneT).inclusion.hom.left.base,
    (((inclusion_isOpenImmersion X c.openSet c.compactClosure).base_open.isOpenMap _
      (goodBase c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).isOpen).inter
        (nextS hK₁ hneS).inclusion_isOpenImmersion.base_open.isOpen_range).inter
          (nextT hK₂ hneT).inclusion_isOpenImmersion.base_open.isOpen_range⟩

private theorem compact_in_originalGood : L ⊆ originalGood c hK₁ hK₂ hL hL₁ hL₂ hneS hneT := by
  intro x hx
  let b : (restriction X c.openSet c.compactClosure).obj.left := ⟨x, c.contains hx⟩
  have hb : b ∈ goodBase c hK₁ hK₂ hL hL₁ hL₂ hneS hneT :=
    compact_in_goodBase c hK₁ hK₂ hL hL₁ hL₂ hneS hneT hx
  exact ⟨⟨⟨b,hb,rfl⟩,(nextS hK₁ hneS).contains (hL₁ hx)⟩,(nextT hK₂ hneT).contains (hL₂ hx)⟩

private def neighbourhood := OriginalNativePrecompactNeighbourhood.neighbourhood X L hL
  (originalGood c hK₁ hK₂ hL hL₁ hL₂ hneS hneT)
  (compact_in_originalGood c hK₁ hK₂ hL hL₁ hL₂ hneS hneT)

/-- ONE actual ORIGINAL open, internally retaining ALL compact L. -/
def openSet : Opens X.obj.left := (neighbourhood c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).openSet

theorem compactClosure : IsCompact (closure (openSet c hK₁ hK₂ hL hL₁ hL₂ hneS hneT : Set X.obj.left)) :=
  (neighbourhood c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).compactClosure

theorem contains : L ⊆ openSet c hK₁ hK₂ hL hL₁ hL₂ hneS hneT :=
  (neighbourhood c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).contains

theorem closure_subset_old : closure (openSet c hK₁ hK₂ hL hL₁ hL₂ hneS hneT : Set X.obj.left) ⊆ c.openSet := by
  intro x hx
  obtain ⟨b,_hb,hbx⟩ := ((neighbourhood c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).closure_subset hx).1.1
  exact hbx ▸ b.property

theorem closure_leftRange : closure (openSet c hK₁ hK₂ hL hL₁ hL₂ hneS hneT : Set X.obj.left) ⊆
    range (OriginalNativeHSShadowOuterRun.next S hK₁ hneS).inclusion.hom.left.base :=
  fun _ hx => ((neighbourhood c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).closure_subset hx).1.2

theorem closure_rightRange : closure (openSet c hK₁ hK₂ hL hL₁ hL₂ hneS hneT : Set X.obj.left) ⊆
    range (OriginalNativeHSShadowOuterRun.next T hK₂ hneT).inclusion.hom.left.base :=
  fun _ hx => ((neighbourhood c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).closure_subset hx).2

/-- EVERY point over the ENTIRE original closure lies in the SAME coupled phase open. -/
theorem whole_fibre (z : (endpoint S c.openSet c.compactClosure c.leftRange).obj.left)
    (hz : ((Context.commonHistory c).projection ≫ Context.baseInclusion c).hom.left.base z ∈
      closure (openSet c hK₁ hK₂ hL hL₁ hL₂ hneS hneT : Set X.obj.left)) :
    z ∈ (phaseNeighbourhood c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).openSet := by
  obtain ⟨b,hb,hbz⟩ := ((neighbourhood c hK₁ hK₂ hL hL₁ hL₂ hneS hneT).closure_subset hz).1.1
  have he : b = (r c).hom.left.base z :=
    (inclusion_isOpenImmersion X c.openSet c.compactClosure).base_open.injective hbz
  have hgood : (r c).hom.left.base z ∈ goodBase c hK₁ hK₂ hL hL₁ hL₂ hneS hneT := he ▸ hb
  exact OriginalNativeProperFibreShrink.preimage_goodBase_subset (r c)
    (Context.commonHistory c).singularModification.isProperMap (O c hK₁ hK₂ hL hL₁ hL₂ hneS hneT) hgood

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSNextCommonBase
