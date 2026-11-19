import Hironaka.Analytic.Unibranch.OriginalNativeShadowRestrictedState

/-! ENTIRE original-stalk HS nonincrease at EVERY actual first-step point,
and full native isomorphism outside the literal old target HS threshold.
Blueprint FIRST: original-native-shadow-first-hs-nonincrease.tex. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeShadowFirstHSNonincrease
noncomputable section
open Hironaka Hironaka SourceReducedComplexSpace
  OriginalLocalEmbeddingStalkHS OriginalIntrinsicHSSuperlevels
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaG11HSPhaseInduction
  HironakaG11CompatibleAnalyticCover OriginalNativeHSCompactShadowWindows

variable {X : SourceReducedComplexSpace} {K : Set X.obj.left}
  (M : Maximum X K) (hK : IsCompact K)
local notation "H" => originalStalkHS X M.point
local notation "N" => OriginalNativeShadowFirstBlowup.target M hK
local notation "F" => OriginalNativeShadowFirstBlowup.centres M hK
local notation "F₀" => OriginalNativeShadowInvariantCentre.centres M hK

/-- Exact old-centre HS, even OUTSIDE K; no global-maximum inference. -/
theorem centre_profile (x : (N).source.obj.left) (hx : x∈(F).support) :
    originalStalkHS (N).source x=H := by
  have hsupport:=OriginalNativeCentreOpenPullback.support_eq_preimage F₀
    (N).inclusion (N).inclusion_isOpenImmersion
  have hxOld : (N).inclusion.hom.left.base x∈(F₀).support :=
    (Set.ext_iff.mp hsupport x).mp hx
  obtain ⟨i,c,hc,hcx⟩:=(F₀).mem_support.mp hxOld
  have hProfile:=
    (OriginalNativeShadowInvariantCentre.cosupp_mem_iff M hK i ⟨c.val.val,c.property⟩).mp hc.1
  have hPoint : ((M.windows hK).window i).toLocalEmbedding.toPoint
      ⟨c.val.val,c.property⟩=(N).inclusion.hom.left.base x := hcx
  rw [hPoint] at hProfile
  exact ((N).hs x).symm.trans hProfile

theorem centre_in_threshold :
    (F).support⊆originalSingularHSThreshold (N).source H := by
  intro x hx
  refine ⟨OriginalNativeShadowFirstBlowup.centres_singular M hK hx,?_⟩
  intro l
  exact (congrFun (centre_profile M hK x hx) l).ge

variable (s : OriginalNativeShadowFirstBlowup.Step M hK)

/-- ENTIRE actual global pointwise decrease from the raw native-state bound. -/
theorem hs_nonincrease (y : s.source.obj.left) :
    originalStalkHS s.source y≤originalStalkHS (N).source (s.projection.hom.left.base y) := by
  by_cases hx : s.projection.hom.left.base y∈(F).support
  · obtain ⟨i,c,_,hc⟩:=(F).mem_support.mp hx
    have hyRange : y∈range
        (OriginalNativeShadowFirstPrefix.nativeWindow M hK s i).hom.left.base :=
      (Set.ext_iff.mp (OriginalNativeShadowFirstPrefix.nativeWindow_range M hK s i) y).mpr ⟨c,hc⟩
    obtain ⟨z,hz⟩:=hyRange
    have hBound:=OriginalNativeShadowRestrictedState.native_hs_bound M hK s i z
    rw [hz] at hBound
    rw [centre_profile M hK (s.projection.hom.left.base y) hx]
    exact hBound
  · have hEq:=originalStalkHS_isIsoOver s.isoOver hx
    exact fun l=>(congrFun hEq l).le

/-- The SAME literal full composite to the original space retains the inequality. -/
theorem hs_nonincrease_original (y : s.source.obj.left) :
    originalStalkHS s.source y≤originalStalkHS X
      ((s.projection ≫ (N).inclusion).hom.left.base y) := by
  intro l
  exact (hs_nonincrease M hK s y l).trans_eq
    (congrFun ((N).hs (s.projection.hom.left.base y)) l).symm

/-- FULL native isomorphism-over witness on the actual old threshold complement. -/
theorem isIsoOver_threshold_compl :
    IsIsoOver s.projection (originalSingularHSThreshold (N).source H)ᶜ :=
  s.isoOver.of_isOpen_subset
    (original_hs_threshold_dictionary (N).source H).2.1.isClosed.isOpen_compl
    (compl_subset_compl.mpr (centre_in_threshold M hK))

theorem hs_eq_off_threshold (y : s.source.obj.left)
    (hy : s.projection.hom.left.base y∉originalSingularHSThreshold (N).source H) :
    originalStalkHS s.source y=originalStalkHS (N).source (s.projection.hom.left.base y) :=
  originalStalkHS_isIsoOver (isIsoOver_threshold_compl M hK s) hy

end
end Hironaka.Analytic.Unibranch.OriginalNativeShadowFirstHSNonincrease
