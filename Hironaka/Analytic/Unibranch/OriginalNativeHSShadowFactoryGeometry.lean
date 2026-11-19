import Hironaka.Analytic.Unibranch.OriginalNativeHSShadowPhaseFactory
import Hironaka.Analytic.Unibranch.OriginalNativeHSShadowRunGeometry

/-! Ordinary ORIGINAL X/K inputs derive WHOLE HS and full off-original-H
geometry on the SAME actual factory finite-history projection. Both genuine
first-empty and surviving actual-run branches are used without re-choice.
Blueprint FIRST: original-native-hs-shadow-factory-geometry.tex. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSShadowFactoryGeometry
noncomputable section
open Hironaka SourceReducedComplexSpace OriginalLocalEmbeddingStalkHS
  OriginalIntrinsicHSSuperlevels HironakaIntrinsicComplexAnalyticRegularLocus
  HironakaG11HSPhaseInduction OriginalNativeHSShadowPhaseFactory

private theorem branch_hs_nonincrease {X : SourceReducedComplexSpace} {K : Set X.obj.left}
    {M : OriginalNativeHSCompactShadowWindows.Maximum X K} {hK : IsCompact K}
    {s : OriginalNativeShadowFirstBlowup.Step M hK} (b : Branch M hK s)
    (y : (OriginalNativeHSEmptyStop.nativeStage (Branch.finalInput b)).Y.obj.left) :
    originalStalkHS (OriginalNativeHSEmptyStop.nativeStage (Branch.finalInput b)).Y y ≤
      originalStalkHS (OriginalNativeHSEmptyStop.neighbourhood (Branch.finalInput b)).source
        ((OriginalNativeHSEmptyStop.nativeStage (Branch.finalInput b)).q.hom.left.base y) := by
  let : Nonempty (CanonicalCentres.ValTy (originalStalkHS X M.point 1 - 1)) :=
    ⟨OriginalNativeShadowInvariantCentre.level M hK⟩
  cases b with
  | empty he =>
    exact OriginalNativeHSShadowRunGeometry.empty_stop_hs_nonincrease
      (firstEmptyInput M hK s he) (OriginalNativeShadowFirstHSNonincrease.hs_nonincrease M hK s) y
  | surviving hne r =>
    exact OriginalNativeHSShadowRunGeometry.original_final_hs_nonincrease M hK s hne r y

private theorem branch_off_threshold {X : SourceReducedComplexSpace} {K : Set X.obj.left}
    {M : OriginalNativeHSCompactShadowWindows.Maximum X K} {hK : IsCompact K}
    {s : OriginalNativeShadowFirstBlowup.Step M hK} (b : Branch M hK s) :
    IsIsoOver (OriginalNativeHSEmptyStop.nativeStage (Branch.finalInput b)).q
      (originalSingularHSThreshold (OriginalNativeHSEmptyStop.neighbourhood (Branch.finalInput b)).source
        (originalStalkHS X M.point))ᶜ := by
  let : Nonempty (CanonicalCentres.ValTy (originalStalkHS X M.point 1 - 1)) :=
    ⟨OriginalNativeShadowInvariantCentre.level M hK⟩
  cases b with
  | empty he =>
    exact OriginalNativeHSShadowRunGeometry.empty_stop_off_threshold
      (firstEmptyInput M hK s he) (OriginalNativeShadowFirstHSNonincrease.isIsoOver_threshold_compl M hK s)
  | surviving hne r =>
    exact OriginalNativeHSShadowRunGeometry.original_final_off_threshold M hK s hne r

variable (X : SourceReducedComplexSpace) (K : Set X.obj.left) (hK : IsCompact K)
  (hSing : (K ∩ intrinsicSingularLocus X.obj).Nonempty)

/-- ONLY ordinary ORIGINAL X/K inputs; no caller maximum/phase/nonincrease packet. -/
theorem hs_nonincrease (y : (source X K hK hSing).obj.left) :
    originalStalkHS (source X K hK hSing) y ≤
      originalStalkHS (base X K hK hSing) ((history X K hK hSing).projection.hom.left.base y) :=
  branch_hs_nonincrease (selectedBranch X K hK hSing) y

/-- FULL inverse on the SAME literal final history map and ORIGINAL selected maximum profile. -/
theorem isIsoOver_threshold_compl : IsIsoOver (history X K hK hSing).projection
    (originalSingularHSThreshold (base X K hK hSing)
      (originalStalkHS X (maximum X K hK hSing).point))ᶜ := by
  have he := (Branch.profile_eq (selectedBranch X K hK hSing)).symm.trans (profile_eq X K hK hSing)
  exact (congrArg (fun H => IsIsoOver (history X K hK hSing).projection
    (originalSingularHSThreshold (base X K hK hSing) H)ᶜ) he).mp
      (branch_off_threshold (selectedBranch X K hK hSing))

theorem hs_eq_off_threshold (y : (source X K hK hSing).obj.left)
    (hy : (history X K hK hSing).projection.hom.left.base y ∉
      originalSingularHSThreshold (base X K hK hSing) (originalStalkHS X (maximum X K hK hSing).point)) :
    originalStalkHS (source X K hK hSing) y =
      originalStalkHS (base X K hK hSing) ((history X K hK hSing).projection.hom.left.base y) :=
  originalStalkHS_isIsoOver (isIsoOver_threshold_compl X K hK hSing) hy

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSShadowFactoryGeometry
