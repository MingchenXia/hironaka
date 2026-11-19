import Hironaka.Analytic.Unibranch.OriginalNativeHSShadowOuterRun
import Hironaka.Analytic.Unibranch.OriginalNativeHSAbsentOuterSuccessor
import Hironaka.Analytic.Unibranch.OriginalNativePrescribedOpenHistory

/-! TWO actual next heads with unequal true leading profiles: a genuine
PAST prescribed-old-endpoint iso derives ENTIRE higher-threshold absence
and the actual skipped-successor coupling. No future comparison/bound packet.
Blueprint FIRST: original-native-hs-unequal-successor.tex. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSUnequalSuccessor
noncomputable section
open Hironaka SourceReducedComplexSpace
  HironakaIntrinsicComplexAnalyticRegularLocus OriginalNativeHSShadowOuterState
  OriginalIntrinsicHSSuperlevels OriginalNativeHSThresholdIsomorphism

variable {X : SourceReducedComplexSpace} {K₁ K₂ : Set X.obj.left}
  (S : State X K₁) (T : State X K₂) (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
  (hn₁ : (singularShadow S).Nonempty) (hn₂ : (singularShadow T).Nonempty)
  (U : Opens X.obj.left) (hU : IsCompact (closure (U : Set X.obj.left)))
  (hRS : closure (U : Set X.obj.left) ⊆ range S.inclusion.hom.left.base)
  (hRT : closure (U : Set X.obj.left) ⊆ range T.inclusion.hom.left.base)
  (α : OriginalNativePrescribedOpenHistory.source S.inclusion S.inclusion_isOpenImmersion U hU hRS S.history ≅
    OriginalNativePrescribedOpenHistory.source T.inclusion T.inclusion_isOpenImmersion U hU hRT T.history)
  (hPast : α.hom ≫ (OriginalNativePrescribedOpenHistory.history T.inclusion T.inclusion_isOpenImmersion
    U hU hRT T.history).projection = (OriginalNativePrescribedOpenHistory.history S.inclusion
      S.inclusion_isOpenImmersion U hU hRS S.history).projection)
  (L : Set X.obj.left) (hL : IsCompact L) (hLU : L ⊆ (U : Set X.obj.left))
  (hLK₁ : L ⊆ K₁) (hLK₂ : L ⊆ K₂)

def nextCompact : Set (OriginalNativeHSShadowOuterRun.next S hK₁ hn₁).base.obj.left :=
  (OriginalNativeHSShadowOuterRun.next S hK₁ hn₁).inclusion.hom.left.base ⁻¹' L

include hL hLK₁ in
theorem nextCompact_isCompact : IsCompact (nextCompact S hK₁ hn₁ L) :=
  (OriginalNativeHSShadowOuterRun.next S hK₁ hn₁).inclusion_isOpenImmersion.base_open.isEmbedding.isInducing.isCompact_preimage'
    hL (fun _ hx => (OriginalNativeHSShadowOuterRun.next S hK₁ hn₁).contains (hLK₁ hx))

include hLK₁ in
theorem nextCompact_image : (OriginalNativeHSShadowOuterRun.next S hK₁ hn₁).inclusion.hom.left.base ''
    nextCompact S hK₁ hn₁ L = L := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact hy
  · intro hx
    obtain ⟨y,hy⟩ := (OriginalNativeHSShadowOuterRun.next S hK₁ hn₁).contains (hLK₁ hx)
    have hyL : (OriginalNativeHSShadowOuterRun.next S hK₁ hn₁).inclusion.hom.left.base y ∈ L :=
      hy.symm ▸ hx
    exact ⟨y,hyL,hy⟩

private abbrev commonSource := OriginalNativePrescribedOpenHistory.source S.inclusion
  S.inclusion_isOpenImmersion U hU hRS S.history
private abbrev leftMap : commonSource S U hU hRS ⟶ S.source :=
  OriginalNativePrescribedOpenHistory.sourceInclusion S.inclusion S.inclusion_isOpenImmersion U hU hRS S.history
private def rightMap : commonSource S U hU hRS ⟶ T.source :=
  α.hom ≫ OriginalNativePrescribedOpenHistory.sourceInclusion T.inclusion T.inclusion_isOpenImmersion U hU hRT T.history

private theorem leftMap_open : LocallyRingedSpace.IsOpenImmersion (leftMap S U hU hRS).hom.left :=
  OriginalNativePrescribedOpenHistory.sourceInclusion_isOpenImmersion _ _ _ _ _ _
private theorem rightMap_open : LocallyRingedSpace.IsOpenImmersion (rightMap S T U hU hRS hRT α).hom.left := by
  have hα : LocallyRingedSpace.IsOpenImmersion α.hom.hom.left := by
    change LocallyRingedSpace.IsOpenImmersion (isoLeft α).hom
    infer_instance
  exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ α.hom.hom.left hα
    (OriginalNativePrescribedOpenHistory.sourceInclusion T.inclusion T.inclusion_isOpenImmersion U hU hRT T.history).hom.left
    (OriginalNativePrescribedOpenHistory.sourceInclusion_isOpenImmersion _ _ _ _ _ _)

include hPast in
private theorem past_original_square : leftMap S U hU hRS ≫ S.history.projection ≫ S.inclusion =
    rightMap S T U hU hRS hRT α ≫ T.history.projection ≫ T.inclusion := by
  calc
    _ = (OriginalNativePrescribedOpenHistory.history S.inclusion S.inclusion_isOpenImmersion U hU hRS S.history).projection ≫
        OriginalRelativelyCompactRestriction.inclusion X U hU :=
      (OriginalNativePrescribedOpenHistory.projection_square _ _ _ _ _ _).symm
    _ = (α.hom ≫ (OriginalNativePrescribedOpenHistory.history T.inclusion T.inclusion_isOpenImmersion U hU hRT T.history).projection) ≫
        OriginalRelativelyCompactRestriction.inclusion X U hU :=
      congrArg (fun f => f ≫ OriginalRelativelyCompactRestriction.inclusion X U hU) hPast.symm
    _ = α.hom ≫ ((OriginalNativePrescribedOpenHistory.history T.inclusion T.inclusion_isOpenImmersion U hU hRT T.history).projection ≫
        OriginalRelativelyCompactRestriction.inclusion X U hU) := Category.assoc _ _ _
    _ = α.hom ≫ (OriginalNativePrescribedOpenHistory.sourceInclusion T.inclusion T.inclusion_isOpenImmersion
        U hU hRT T.history ≫ T.history.projection ≫ T.inclusion) :=
      congrArg (fun f => α.hom ≫ f) (OriginalNativePrescribedOpenHistory.projection_square _ _ _ _ _ _)
    _ = _ := by simp only [rightMap,Category.assoc]

local notation "A" => OriginalNativeHSOuterSuccessor.oldSource S.history (baseShadow S) (baseShadow_compact S hK₁) hn₁
local notation "N₀" => OriginalNativeHSOuterSuccessor.neighbourhood S.history (baseShadow S) (baseShadow_compact S hK₁) hn₁
local notation "Q" => OriginalNativeHSAbsentOuterSuccessor.oldPrefix S.history (baseShadow S) (baseShadow_compact S hK₁) hn₁
local notation "H₁" => OriginalNativeHSOuterInitialBound.profile S.history (baseShadow S) (baseShadow_compact S hK₁) hn₁
local notation "H₂" => OriginalNativeHSOuterInitialBound.profile T.history (baseShadow T) (baseShadow_compact T hK₂) hn₂

private theorem old_point_in_L (y : (A).obj.left)
    (hy : (Q).projection.hom.left.base y ∈ nextCompact S hK₁ hn₁ L) :
    S.inclusion.hom.left.base (S.history.projection.hom.left.base
      ((OriginalNativeHSOuterSuccessor.oldInclusion S.history (baseShadow S)
        (baseShadow_compact S hK₁) hn₁).hom.left.base y)) ∈ L := by
  have ep := congrArg (fun f : (A) ⟶ S.base => f.hom.left.base y)
    (OriginalNativePhysicalHistoryRestriction.projection_square S.history (N₀).openSet (N₀).compactClosure)
  exact (congrArg S.inclusion.hom.left.base ep) ▸ hy

variable (higher : toLex (OriginalNativeHSOuterInitialBound.profile T.history (baseShadow T)
    (baseShadow_compact T hK₂) hn₂) < toLex (OriginalNativeHSOuterInitialBound.profile S.history
      (baseShadow S) (baseShadow_compact S hK₁) hn₁))

include hPast hLU hLK₂ higher in
/-- Actual PAST data derives the ENTIRE higher old-prefix threshold absence. -/
theorem higher_threshold_empty :
    OriginalNativeHSAbsentOuterSuccessor.oldFibre S.history (baseShadow S)
      (baseShadow_compact S hK₁) hn₁ (nextCompact S hK₁ hn₁ L) ∩
        originalSingularHSThreshold (A) (H₁) = ∅ := by
  apply Set.eq_empty_of_subset_empty
  rintro y ⟨hyL,hyH⟩
  have hOrig := old_point_in_L S hK₁ hn₁ L y hyL
  let z : (commonSource S U hU hRS).obj.left :=
    ⟨(OriginalNativeHSOuterSuccessor.oldInclusion S.history (baseShadow S)
      (baseShadow_compact S hK₁) hn₁).hom.left.base y,hLU hOrig⟩
  have hO : LocallyRingedSpace.IsOpenImmersion (OriginalNativeHSOuterSuccessor.oldInclusion
      S.history (baseShadow S) (baseShadow_compact S hK₁) hn₁).hom.left :=
    OriginalRelativelyCompactRestriction.inclusion_isOpenImmersion _ _ _
  have hzH : (leftMap S U hU hRS).hom.left.base z ∈ originalSingularHSThreshold S.source (H₁) :=
    (Set.ext_iff.mp (threshold_preimage_openImmersion (H₁)
      (OriginalNativeHSOuterSuccessor.oldInclusion S.history (baseShadow S)
        (baseShadow_compact S hK₁) hn₁) hO) y).mpr hyH
  have ep := congrArg (fun f : commonSource S U hU hRS ⟶ X => f.hom.left.base z)
    (past_original_square (S := S) (T := T) (U := U) (hU := hU) (hRS := hRS) (hRT := hRT)
      (α := α) (hPast := hPast))
  have hOrigLeft : S.inclusion.hom.left.base (S.history.projection.hom.left.base
      ((leftMap S U hU hRS).hom.left.base z)) ∈ L := hOrig
  have hOrigRight : T.inclusion.hom.left.base (T.history.projection.hom.left.base
      ((rightMap S T U hU hRS hRT α).hom.left.base z)) ∈ L := ep ▸ hOrigLeft
  have hBound : z ∈ OriginalNativeHSOuterInitialBound.boundRegion T.history (baseShadow T)
      (baseShadow_compact T hK₂) hn₂ (rightMap S T U hU hRS hRT α) := by
    change T.history.projection.hom.left.base ((rightMap S T U hU hRS hRT α).hom.left.base z) ∈
      (OriginalNativeHSOuterSuccessor.neighbourhood T.history (baseShadow T)
        (baseShadow_compact T hK₂) hn₂).openSet
    exact (OriginalNativeHSOuterSuccessor.neighbourhood T.history (baseShadow T)
      (baseShadow_compact T hK₂) hn₂).contains (hLK₂ hOrigRight)
  have hle := OriginalNativeHSOuterInitialBound.threshold_profile_le S.history (baseShadow S)
    (baseShadow_compact S hK₁) hn₁ T.history (baseShadow T) (baseShadow_compact T hK₂) hn₂
    (leftMap S U hU hRS) (leftMap_open S U hU hRS) (rightMap S T U hU hRS hRT α)
    (rightMap_open S T U hU hRS hRT α) z hzH hBound
  exact (not_le_of_gt higher) hle

local notation "he" => higher_threshold_empty (S := S) (T := T) (hK₁ := hK₁) (hK₂ := hK₂)
  (hn₁ := hn₁) (hn₂ := hn₂) (U := U) (hU := hU) (hRS := hRS) (hRT := hRT) (α := α)
  (hPast := hPast) (L := L) (hLU := hLU) (hLK₂ := hLK₂) (higher := higher)
local notation "hc" => nextCompact_isCompact (S := S) (hK₁ := hK₁) (hn₁ := hn₁)
  (L := L) (hL := hL) (hLK₁ := hLK₁)

include hPast hLU hLK₁ hLK₂ higher in
/-- Raw ACTUAL higher-successor coupling; the two next states/Run data are not changed. -/
theorem exists_higher_successor_coupling :
    let N := OriginalNativeHSAbsentOuterSuccessor.neighbourhood S.history (baseShadow S)
      (baseShadow_compact S hK₁) hn₁ (nextCompact S hK₁ hn₁ L) (hc) (he)
    let old := OriginalNativeHSAbsentOuterSuccessor.oldHistory S.history (baseShadow S)
      (baseShadow_compact S hK₁) hn₁ (nextCompact S hK₁ hn₁ L) (hc) (he)
    let next := OriginalNativeHSAbsentOuterSuccessor.nextHistory S.history (baseShadow S)
      (baseShadow_compact S hK₁) hn₁ (nextCompact S hK₁ hn₁ L) (hc) (he)
    ∃ E : OriginalNativeHSAbsentOuterSuccessor.nextSource S.history (baseShadow S)
        (baseShadow_compact S hK₁) hn₁ (nextCompact S hK₁ hn₁ L) (hc) (he) ≅
      OriginalNativeHSAbsentOuterSuccessor.oldSource S.history (baseShadow S)
        (baseShadow_compact S hK₁) hn₁ (nextCompact S hK₁ hn₁ L) (hc) (he),
      L ⊆ range (N.inclusion ≫ (OriginalNativeHSShadowOuterRun.next S hK₁ hn₁).inclusion).hom.left.base ∧
      E.hom ≫ old.projection = next.projection ∧
      E.hom ≫ old.projection ≫ N.inclusion ≫ (N₀).inclusion ≫ S.inclusion =
        next.projection ≫ N.inclusion ≫ (N₀).inclusion ≫ S.inclusion ∧
      old.length = S.history.length ∧ next.length = (OriginalNativeHSShadowOuterRun.next S hK₁ hn₁).history.length ∧
      E.hom.hom.left ≫ (OriginalNativeHSAbsentOuterSuccessor.oldSource S.history (baseShadow S)
        (baseShadow_compact S hK₁) hn₁ (nextCompact S hK₁ hn₁ L) (hc) (he)).obj.hom =
        (OriginalNativeHSAbsentOuterSuccessor.nextSource S.history (baseShadow S)
          (baseShadow_compact S hK₁) hn₁ (nextCompact S hK₁ hn₁ L) (hc) (he)).obj.hom := by
  dsimp only
  refine ⟨OriginalNativeHSAbsentOuterSuccessor.comparison S.history (baseShadow S)
      (baseShadow_compact S hK₁) hn₁ (nextCompact S hK₁ hn₁ L) (hc) (he),?_,
    OriginalNativeHSAbsentOuterSuccessor.comparison_projection S.history (baseShadow S)
      (baseShadow_compact S hK₁) hn₁ (nextCompact S hK₁ hn₁ L) (hc) (he),?_,
    OriginalNativeHSAbsentOuterSuccessor.old_length S.history (baseShadow S)
      (baseShadow_compact S hK₁) hn₁ (nextCompact S hK₁ hn₁ L) (hc) (he),
    OriginalNativeHSAbsentOuterSuccessor.next_length S.history (baseShadow S)
      (baseShadow_compact S hK₁) hn₁ (nextCompact S hK₁ hn₁ L) (hc) (he),
    OriginalNativeHSAbsentOuterSuccessor.comparison_scalar S.history (baseShadow S)
      (baseShadow_compact S hK₁) hn₁ (nextCompact S hK₁ hn₁ L) (hc) (he)⟩
  · intro x hx
    obtain ⟨y,hy⟩ := (OriginalNativeHSShadowOuterRun.next S hK₁ hn₁).contains (hLK₁ hx)
    have hyC : y ∈ nextCompact S hK₁ hn₁ L := by
      change (OriginalNativeHSShadowOuterRun.next S hK₁ hn₁).inclusion.hom.left.base y ∈ L
      exact hy.symm ▸ hx
    obtain ⟨z,hz⟩ := OriginalNativeHSAbsentOuterSuccessor.compact_retained S.history (baseShadow S)
      (baseShadow_compact S hK₁) hn₁ (nextCompact S hK₁ hn₁ L) (hc) (he) hyC
    exact ⟨z,(congrArg (OriginalNativeHSShadowOuterRun.next S hK₁ hn₁).inclusion.hom.left.base hz).trans hy⟩
  · have hp := congrArg (fun f => f ≫ S.inclusion)
      (OriginalNativeHSAbsentOuterSuccessor.comparison_original_base_square S.history (baseShadow S)
        (baseShadow_compact S hK₁) hn₁ (nextCompact S hK₁ hn₁ L) (hc) (he))
    simpa only [Category.assoc] using hp

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSUnequalSuccessor
