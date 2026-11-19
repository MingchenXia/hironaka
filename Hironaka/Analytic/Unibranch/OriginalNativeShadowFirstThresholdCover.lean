import Hironaka.Analytic.Unibranch.OriginalNativeShadowRestrictedState

/-! ACTUAL first-current threshold coverage on the literal compact inverse shadow.
Blueprint FIRST: original-native-shadow-first-threshold-cover.tex. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeShadowFirstThresholdCover
noncomputable section
open Hironaka Hironaka
  SourceReducedComplexSpace OriginalLocalEmbeddingStalkHS OriginalIntrinsicHSSuperlevels
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaG11HSPhaseInduction
  HironakaG11CompatibleAnalyticCover OriginalNativeHSCompactShadowWindows

variable {X : SourceReducedComplexSpace} {K : Set X.obj.left}
  (M : Maximum X K) (hK : IsCompact K)
  (s : OriginalNativeShadowFirstBlowup.Step M hK)
local notation "H" => originalStalkHS X M.point
local notation "N" => OriginalNativeShadowFirstBlowup.target M hK
local notation "F" => OriginalNativeShadowFirstBlowup.centres M hK
local notation "F₀" => OriginalNativeShadowInvariantCentre.centres M hK

/-- The literal original singular all-order HS threshold on the ACTUAL first source. -/
def currentThreshold : Set s.source.obj.left := originalSingularHSThreshold s.source H

/-- The SAME proper inverse of the original compact shadow. -/
def currentShadow : Set s.source.obj.left :=
  s.projection.hom.left.base ⁻¹' ((N).inclusion.hom.left.base ⁻¹' K)

theorem currentThreshold_closed : IsClosed (currentThreshold M hK s) :=
  (original_hs_threshold_dictionary s.source H).2.1.isClosed

theorem currentShadow_compact : IsCompact (currentShadow M hK s) := s.shadow_compact

theorem threshold_shadow_compact :
    IsCompact (currentShadow M hK s ∩ currentThreshold M hK s) :=
  (currentShadow_compact M hK s).inter_right (currentThreshold_closed M hK s)

/-- ENTIRE native threshold iff the literal first transformed original record cosupport. -/
theorem nativeWindow_threshold_iff (i : (M.windows hK).ι)
    (c : (OriginalNativeShadowFirstPrefix.strictSource M hK i).obj.left) :
    (OriginalNativeShadowFirstPrefix.nativeWindow M hK s i).hom.left.base c ∈
      currentThreshold M hK s ↔
    c.val∈(OriginalNativeShadowFirstPrefix.transformedRecord M hK i).cosupp := by
  constructor
  · intro hc
    apply (OriginalNativeShadowRestrictedState.native_cosupp_iff M hK s i c).mpr
    funext l
    exact le_antisymm (OriginalNativeShadowRestrictedState.native_hs_bound M hK s i c l)
      (hc.2 l)
  · intro hc
    refine ⟨OriginalNativeShadowRestrictedState.native_cosupp_singular M hK s i c hc,?_⟩
    intro l
    exact (congrFun
      ((OriginalNativeShadowRestrictedState.native_cosupp_iff M hK s i c).mp hc) l).ge

theorem nativeWindow_threshold_trace (i : (M.windows hK).ι) :
    (OriginalNativeShadowFirstPrefix.nativeWindow M hK s i).hom.left.base ⁻¹'
      currentThreshold M hK s =
    (Subtype.val : (OriginalNativeShadowFirstPrefix.strictSource M hK i).obj.left →
      OriginalNativeShadowFirstPrefix.ambient M hK i) ⁻¹'
        (OriginalNativeShadowFirstPrefix.transformedRecord M hK i).cosupp := by
  ext c
  exact nativeWindow_threshold_iff M hK s i c

/-- Concrete cover on ONLY the actual current threshold over the literal compact shadow. -/
theorem threshold_shadow_covered :
    currentShadow M hK s ∩ currentThreshold M hK s ⊆
      ⋃ i,range (OriginalNativeShadowFirstPrefix.nativeWindow M hK s i).hom.left.base := by
  rintro y ⟨hyK,hyC⟩
  have hxWindow : ∃ i, s.projection.hom.left.base y∈range ((F).windowMap i).hom.left.base := by
    by_cases hx : s.projection.hom.left.base y∈(F).support
    · obtain ⟨i,c,_,hc⟩:=(F).mem_support.mp hx
      exact ⟨i,c,hc⟩
    · have hyOff : s.projection.hom.left.base y∈(F).supportᶜ := hx
      have hxSing : s.projection.hom.left.base y∈intrinsicSingularLocus (N).source.obj := by
        intro hxReg
        exact hyC.1 ((s.isoOver.mem_intrinsicRegularLocus_iff hyOff).mpr hxReg)
      have hHS:=originalStalkHS_isIsoOver s.isoOver hyOff
      have hxC : s.projection.hom.left.base y∈originalSingularHSThreshold (N).source H := by
        refine ⟨hxSing,?_⟩
        intro l
        exact (hyC.2 l).trans_eq (congrFun hHS l)
      have hxOriginal : (N).inclusion.hom.left.base (s.projection.hom.left.base y)∈M.threshold :=
        (Set.ext_iff.mp ((N).preimage_threshold H) (s.projection.hom.left.base y)).mpr hxC
      have hOld:=OriginalNativeShadowInvariantCentre.shadow_covered M hK ⟨hyK,hxOriginal⟩
      obtain ⟨i,hi⟩:=mem_iUnion.mp hOld
      refine ⟨i,?_⟩
      exact (Set.ext_iff.mp (OriginalNativeCentreOpenPullback.window_range F₀
        (N).inclusion (N).inclusion_isOpenImmersion i) (s.projection.hom.left.base y)).mp hi
  obtain ⟨i,hi⟩:=hxWindow
  apply mem_iUnion.mpr
  refine ⟨i,?_⟩
  exact (Set.ext_iff.mp (OriginalNativeShadowFirstPrefix.nativeWindow_range M hK s i) y).mpr hi

end
end Hironaka.Analytic.Unibranch.OriginalNativeShadowFirstThresholdCover
