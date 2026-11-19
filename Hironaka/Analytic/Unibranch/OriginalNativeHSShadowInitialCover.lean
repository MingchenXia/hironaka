import Hironaka.Analytic.Unibranch.OriginalNativeHSShadowPhaseFactory
import Hironaka.Analytic.Unibranch.OriginalNativeHSInitialThresholdCover

/-! The INITIAL threshold cover follows the SAME actual finite Run and
its actual base-open initial windows, including the final EStop restriction.
Blueprint FIRST: original-native-hs-shadow-initial-cover.tex.
No new Input field or final-current-empty-cover substitution. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSShadowInitialCover
noncomputable section
open Hironaka SourceReducedComplexSpace
  OriginalLocalEmbeddingStalkHS OriginalIntrinsicHSSuperlevels
  OriginalNativeHSUniformRestrictedStage OriginalNativeHSShadowFiniteRun
  OriginalNativeHSCompactShadowWindows CanonicalCentres

variable {n : ℕ} {Λ : Type} [LinearOrder Λ] [Nonempty Λ]

theorem run_initial_threshold_covered : {P : Input n Λ} → (r : Run P) →
    (originalSingularHSThreshold P.base P.profile ⊆
      ⋃ i, range (P.window i).toLocalEmbedding.toPoint) →
    originalSingularHSThreshold (OriginalNativeHSShadowFinitePhase.Run.finalBase r) P.profile ⊆
      ⋃ i, range (OriginalNativeHSShadowFinitePhase.Run.finalWindow r i).toLocalEmbedding.toPoint
  | P, .stop _ hempty, hCover =>
    OriginalNativeHSInitialThresholdCover.pullback_threshold_covered
      (OriginalNativeHSUniformRestrictedStage.window P) P.profile
      (OriginalNativeHSInitialThresholdCover.pullback_threshold_covered P.window P.profile hCover
        (neighbourhood P).inclusion (neighbourhood P).inclusion_isOpenImmersion)
      (OriginalNativeHSEmptyStop.neighbourhood
        (OriginalNativeHSShadowFinitePhase.Run.finalInput (.stop P hempty))).inclusion
      (OriginalNativeHSEmptyStop.neighbourhood
        (OriginalNativeHSShadowFinitePhase.Run.finalInput (.stop P hempty))).inclusion_isOpenImmersion
  | P, .next _ _hne tail, hCover =>
    run_initial_threshold_covered tail
      (OriginalNativeHSInitialThresholdCover.pullback_threshold_covered P.window P.profile hCover
        (neighbourhood P).inclusion (neighbourhood P).inclusion_isOpenImmersion)

variable {X : SourceReducedComplexSpace} {K : Set X.obj.left}
  {M : Maximum X K} {hK : IsCompact K}
  {s : OriginalNativeShadowFirstBlowup.Step M hK}

theorem branch_initial_threshold_covered (b : OriginalNativeHSShadowPhaseFactory.Branch M hK s) :
    originalSingularHSThreshold (OriginalNativeHSEmptyStop.neighbourhood b.finalInput).source
      (originalStalkHS X M.point) ⊆
        ⋃ i, range (OriginalNativeHSEmptyStop.window b.finalInput i).toLocalEmbedding.toPoint := by
  let : Nonempty (ValTy (originalStalkHS X M.point 1 - 1)) :=
    ⟨OriginalNativeShadowInvariantCentre.level M hK⟩
  cases b with
  | empty he =>
    exact OriginalNativeHSInitialThresholdCover.pullback_threshold_covered
      (OriginalNativeShadowFlatWindows.window M hK) (originalStalkHS X M.point)
      (OriginalNativeHSInitialThresholdCover.seed_threshold_covered M hK)
      (OriginalNativeHSEmptyStop.neighbourhood
        (OriginalNativeHSShadowPhaseFactory.Branch.finalInput (.empty he))).inclusion
      (OriginalNativeHSEmptyStop.neighbourhood
        (OriginalNativeHSShadowPhaseFactory.Branch.finalInput (.empty he))).inclusion_isOpenImmersion
  | surviving hne r =>
    exact run_initial_threshold_covered r (OriginalNativeHSInitialThresholdCover.seed_threshold_covered M hK)

theorem factory_initial_threshold_covered (X : SourceReducedComplexSpace) (K : Set X.obj.left)
    (hK : IsCompact K) (hSing : (K ∩ HironakaIntrinsicComplexAnalyticRegularLocus.intrinsicSingularLocus X.obj).Nonempty) :
    originalSingularHSThreshold (OriginalNativeHSShadowPhaseFactory.base X K hK hSing)
      (originalStalkHS X (OriginalNativeHSShadowPhaseFactory.maximum X K hK hSing).point) ⊆
        ⋃ i, range (OriginalNativeHSEmptyStop.window
          (OriginalNativeHSShadowPhaseFactory.finalInput X K hK hSing) i).toLocalEmbedding.toPoint := by
  have h := branch_initial_threshold_covered (OriginalNativeHSShadowPhaseFactory.selectedBranch X K hK hSing)
  exact OriginalNativeHSCompactShadowBarrier.nativePoint_hs
    (OriginalNativeHSShadowPhaseFactory.maximum X K hK hSing) hK ▸ h

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSShadowInitialCover
