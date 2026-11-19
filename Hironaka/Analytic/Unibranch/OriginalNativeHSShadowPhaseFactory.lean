import Hironaka.Analytic.Unibranch.OriginalNativeHSShadowFinitePhase

/-! Ordinary original X/compact K/singular shadow -> an ACTUAL finite phase.
Both FIRST-empty and genuinely surviving branches retain the SAME first p.
Blueprint FIRST: original-native-hs-shadow-phase-factory.tex.
No phaseSupplier, terminal packet, family re-choice or completed outer factory. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSShadowPhaseFactory
noncomputable section
open Hironaka Hironaka.BlowupSequences
  Hironaka SourceReducedComplexSpace OriginalLocalEmbeddingStalkHS
  OriginalNativeHSCompactShadowWindows OriginalIntrinsicHSSuperlevels
  HironakaG11PresReduction HironakaG11VanishingWindows HironakaG11VanishingPrincipalization
  HironakaG11StrictTransformTowers HironakaG11CompatibleCanonicalTowers
  OriginalNativeHSOuterHistory HironakaIntrinsicComplexAnalyticRegularLocus
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal CanonicalCentres

variable {X : SourceReducedComplexSpace} {K : Set X.obj.left}

private abbrev dimension (M : Maximum X K) := originalStalkHS X M.point 1 - 1

def firstShadow (M : Maximum X K) (hK : IsCompact K)
    (s : OriginalNativeShadowFirstBlowup.Step M hK) : Set s.source.obj.left :=
  originalSingularHSThreshold s.source (originalStalkHS X M.point) ∩
    s.projection.hom.left.base ⁻¹' OriginalNativeHSFirstStageInput.compact M hK

/-- The SAME first actual step, when its threshold shadow already is empty. -/
def firstEmptyInput (M : Maximum X K) (hK : IsCompact K)
    (s : OriginalNativeShadowFirstBlowup.Step M hK) (he : firstShadow M hK s = ∅) :
    OriginalNativeHSEmptyStop.Input (dimension M) (ValTy (dimension M)) where
  base := (OriginalNativeShadowFirstBlowup.target M hK).source
  ι := (M.windows hK).ι
  window := OriginalNativeShadowFlatWindows.window M hK
  rawRecord := OriginalNativeShadowFlatWindows.rawRecord M hK
  profile := originalStalkHS X M.point
  native := OriginalNativeShadowFlatWindows.native_record M hK
  exponent := OriginalNativeShadowInvariantCentre.exponent M hK
  positive := OriginalNativeShadowInvariantCentre.exponent_pos M hK
  invariant := (OriginalNativeShadowInvariantCentre.invariant M).toResolutionInvariant
  clock := 1
  stage := OriginalNativeShadowFirstStage.ambientStage M hK
  nativeStage := OriginalNativeShadowFirstStage.nativeStage M hK s
  history := OriginalNativeHSFirstStageInput.physicalHistory M hK s
  history_projection := OriginalNativeHSFirstStageInput.history_projection M hK s
  compact := OriginalNativeHSFirstStageInput.compact M hK
  compact_isCompact := OriginalNativeHSFirstStageInput.compact_isCompact M hK
  shadowEmpty := he

/-- The actual decision and, when needed, the ACTUAL original-invariant finite run. -/
inductive Branch (M : Maximum X K) (hK : IsCompact K)
    (s : OriginalNativeShadowFirstBlowup.Step M hK) : Type 1
  | empty (he : firstShadow M hK s = ∅)
  | surviving (hne : (firstShadow M hK s).Nonempty)
      (r : letI : Nonempty (ValTy (dimension M)) := ⟨OriginalNativeShadowInvariantCentre.level M hK⟩
        OriginalNativeHSShadowFiniteRun.Run (OriginalNativeHSFirstStageInput.phaseInput M hK s hne))

def branch (M : Maximum X K) (hK : IsCompact K)
    (s : OriginalNativeShadowFirstBlowup.Step M hK) : Branch M hK s := by
  classical
  letI : Nonempty (ValTy (dimension M)) := ⟨OriginalNativeShadowInvariantCentre.level M hK⟩
  by_cases he : firstShadow M hK s = ∅
  · exact .empty he
  · have hne : (firstShadow M hK s).Nonempty := Set.nonempty_iff_ne_empty.mpr he
    exact .surviving hne (OriginalNativeHSShadowFiniteRun.run
      (OriginalNativeHSFirstStageInput.phaseInput M hK s hne))

namespace Branch
variable {M : Maximum X K} {hK : IsCompact K}
  {s : OriginalNativeShadowFirstBlowup.Step M hK}

def finalInput (b : Branch M hK s) : OriginalNativeHSEmptyStop.Input (dimension M) (ValTy (dimension M)) := by
  letI : Nonempty (ValTy (dimension M)) := ⟨OriginalNativeShadowInvariantCentre.level M hK⟩
  exact match b with
  | .empty he => firstEmptyInput M hK s he
  | .surviving _ r => OriginalNativeHSShadowFinitePhase.Run.finalInput r

theorem profile_eq (b : Branch M hK s) : (finalInput b).profile = originalStalkHS X M.point := by
  let : Nonempty (ValTy (dimension M)) := ⟨OriginalNativeShadowInvariantCentre.level M hK⟩
  cases b with
  | empty he => rfl
  | surviving hne r => exact r.profile_eq

theorem invariant_eq (b : Branch M hK s) : (finalInput b).invariant =
    (OriginalNativeShadowInvariantCentre.invariant M).toResolutionInvariant := by
  let : Nonempty (ValTy (dimension M)) := ⟨OriginalNativeShadowInvariantCentre.level M hK⟩
  cases b with
  | empty he => rfl
  | surviving hne r => exact OriginalNativeHSShadowFinitePhase.Run.final_invariant_eq r

def targetInclusion (b : Branch M hK s) :
    (OriginalNativeHSEmptyStop.neighbourhood (finalInput b)).source ⟶
      (OriginalNativeShadowFirstBlowup.target M hK).source := by
  letI : Nonempty (ValTy (dimension M)) := ⟨OriginalNativeShadowInvariantCentre.level M hK⟩
  exact match b with
  | .empty he => (OriginalNativeHSEmptyStop.neighbourhood (finalInput (.empty he))).inclusion
  | .surviving _ r => OriginalNativeHSShadowFinitePhase.Run.baseInclusion r

theorem targetInclusion_isOpenImmersion (b : Branch M hK s) :
    LocallyRingedSpace.IsOpenImmersion (targetInclusion b).hom.left := by
  let : Nonempty (ValTy (dimension M)) := ⟨OriginalNativeShadowInvariantCentre.level M hK⟩
  cases b with
  | empty he => exact (OriginalNativeHSEmptyStop.neighbourhood (finalInput (.empty he))).inclusion_isOpenImmersion
  | surviving hne r => exact OriginalNativeHSShadowFinitePhase.Run.baseInclusion_isOpenImmersion r

theorem compact_retained (b : Branch M hK s) : OriginalNativeHSFirstStageInput.compact M hK ⊆
    range (targetInclusion b).hom.left.base := by
  let : Nonempty (ValTy (dimension M)) := ⟨OriginalNativeShadowInvariantCentre.level M hK⟩
  cases b with
  | empty he =>
    intro x hx
    exact ⟨⟨x, (OriginalNativeHSEmptyStop.neighbourhood (finalInput (.empty he))).contains hx⟩, rfl⟩
  | surviving hne r => exact OriginalNativeHSShadowFinitePhase.Run.compact_retained r

def phaseProjection (b : Branch M hK s) : (OriginalNativeHSEmptyStop.nativeStage (finalInput b)).Y ⟶ s.source := by
  letI : Nonempty (ValTy (dimension M)) := ⟨OriginalNativeShadowInvariantCentre.level M hK⟩
  exact match b with
  | .empty he => OriginalNativeHSEmptyStop.sourceInclusion (finalInput (.empty he))
  | .surviving _ r => OriginalNativeHSShadowFinitePhase.Run.phaseProjection r

theorem projection_square (b : Branch M hK s) :
    (OriginalNativeHSEmptyStop.nativeStage (finalInput b)).q ≫ targetInclusion b =
      phaseProjection b ≫ s.projection := by
  let : Nonempty (ValTy (dimension M)) := ⟨OriginalNativeShadowInvariantCentre.level M hK⟩
  cases b with
  | empty he => exact OriginalNativeHSEmptyStop.projection_square (finalInput (.empty he))
  | surviving hne r => exact OriginalNativeHSShadowFinitePhase.Run.projection_square r

end Branch

variable (X : SourceReducedComplexSpace) (K : Set X.obj.left) (hK : IsCompact K)
  (hSing : (K ∩ intrinsicSingularLocus X.obj).Nonempty)

/-- Actual maximum selected by finite native HS image on compact K. -/
def maximum : Maximum X K := OriginalNativeHSCompactShadowWindows.maximum X K hK hSing

/-- Actual derived barrier maximum, retaining the same attained original HS profile. -/
def selectedMaximum := OriginalNativeShadowFirstBlowup.barrierMaximum (maximum X K hK hSing) hK

private theorem selectedCompact : IsCompact
    (OriginalNativeShadowFirstBlowup.barrierShadow (maximum X K hK hSing) hK) :=
  OriginalNativeShadowFirstBlowup.barrierShadow_compact (maximum X K hK hSing) hK

def selectedStep := OriginalNativeShadowFirstBlowup.step (selectedMaximum X K hK hSing)
  (selectedCompact X K hK hSing)

def selectedBranch := branch (selectedMaximum X K hK hSing) (selectedCompact X K hK hSing)
  (selectedStep X K hK hSing)

def finalInput := Branch.finalInput (selectedBranch X K hK hSing)

theorem profile_eq : (finalInput X K hK hSing).profile =
    originalStalkHS X (maximum X K hK hSing).point :=
  (Branch.profile_eq (selectedBranch X K hK hSing)).trans
    (OriginalNativeHSCompactShadowBarrier.nativePoint_hs (maximum X K hK hSing) hK)

def base : SourceReducedComplexSpace := (OriginalNativeHSEmptyStop.neighbourhood (finalInput X K hK hSing)).source

def source : SourceReducedComplexSpace := (OriginalNativeHSEmptyStop.nativeStage (finalInput X K hK hSing)).Y

def history : PhysicalHistory (base X K hK hSing) (source X K hK hSing) :=
  OriginalNativeHSEmptyStop.physicalHistory (finalInput X K hK hSing)

def baseInclusion : base X K hK hSing ⟶ X :=
  Branch.targetInclusion (selectedBranch X K hK hSing) ≫
    OriginalNativeShadowFirstBlowup.originalTargetInclusion (maximum X K hK hSing) hK

theorem baseInclusion_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion (baseInclusion X K hK hSing).hom.left :=
  @LocallyRingedSpace.IsOpenImmersion.comp _ _ _
    (Branch.targetInclusion (selectedBranch X K hK hSing)).hom.left
    (Branch.targetInclusion_isOpenImmersion (selectedBranch X K hK hSing))
    (OriginalNativeShadowFirstBlowup.originalTargetInclusion (maximum X K hK hSing) hK).hom.left
    (OriginalNativeShadowFirstBlowup.originalTarget_isOpenImmersion (maximum X K hK hSing) hK)

theorem compact_retained : K ⊆ range (baseInclusion X K hK hSing).hom.left.base := by
  intro x hx
  obtain ⟨y, hy⟩ := OriginalNativeShadowFirstBlowup.originalTarget_contains_shadow (maximum X K hK hSing) hK hx
  have hyK : y ∈ OriginalNativeHSFirstStageInput.compact (selectedMaximum X K hK hSing)
      (selectedCompact X K hK hSing) := by
    change (OriginalNativeShadowFirstBlowup.originalTargetInclusion (maximum X K hK hSing) hK).hom.left.base y ∈ K
    exact hy ▸ hx
  obtain ⟨z, hz⟩ := Branch.compact_retained (selectedBranch X K hK hSing) hyK
  exact ⟨z, (congrArg
    (OriginalNativeShadowFirstBlowup.originalTargetInclusion (maximum X K hK hSing) hK).hom.left.base hz).trans hy⟩

def originalProjection : source X K hK hSing ⟶ X :=
  (history X K hK hSing).projection ≫ baseInclusion X K hK hSing

theorem projection_square : originalProjection X K hK hSing =
    Branch.phaseProjection (selectedBranch X K hK hSing) ≫
      (selectedStep X K hK hSing).projection ≫
        OriginalNativeShadowFirstBlowup.originalTargetInclusion (maximum X K hK hSing) hK := by
  have h := congrArg (fun q => q ≫
    OriginalNativeShadowFirstBlowup.originalTargetInclusion (maximum X K hK hSing) hK)
    (Branch.projection_square (selectedBranch X K hK hSing))
  exact (Category.assoc _ _ _).symm.trans (h.trans (Category.assoc _ _ _))

theorem threshold_empty : originalSingularHSThreshold (source X K hK hSing)
    (originalStalkHS X (maximum X K hK hSing).point) = ∅ := by
  have h := OriginalNativeHSEmptyStop.threshold_empty (finalInput X K hK hSing)
  exact profile_eq X K hK hSing ▸ h

theorem resolution (i : (finalInput X K hK hSing).ι) :
    IsGeoResolution (OriginalNativeHSEmptyStop.record (finalInput X K hK hSing) i)
      ((OriginalNativeHSEmptyStop.stage (finalInput X K hK hSing)).T i).2 :=
  OriginalNativeHSEmptyStop.resolution (finalInput X K hK hSing) i

theorem canonical (i : (finalInput X K hK hSing).ι) : ResolutionInvariantSpec.IsCanonical
    (OriginalNativeHSEmptyStop.record (finalInput X K hK hSing) i)
    ((OriginalNativeShadowInvariantCentre.invariant (selectedMaximum X K hK hSing)).toResolutionInvariant.inv
      (OriginalNativeHSEmptyStop.record (finalInput X K hK hSing) i))
    ((OriginalNativeHSEmptyStop.stage (finalInput X K hK hSing)).T i).2 := by
  have h := OriginalNativeHSEmptyStop.canonical (finalInput X K hK hSing) i
  exact Branch.invariant_eq (selectedBranch X K hK hSing) ▸ h

theorem proper : IsProperMap (history X K hK hSing).projection.hom.left.base :=
  OriginalNativeHSEmptyStop.proper (finalInput X K hK hSing)

theorem originalReg : IsIsoOver (history X K hK hSing).projection
    (intrinsicRegularLocus (base X K hK hSing).obj) :=
  OriginalNativeHSEmptyStop.originalReg (finalInput X K hK hSing)

theorem scalar : (originalProjection X K hK hSing).hom.left ≫ X.obj.hom =
    (source X K hK hSing).obj.hom := Over.w (originalProjection X K hK hSing).hom

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSShadowPhaseFactory
