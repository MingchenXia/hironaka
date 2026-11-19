import Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentEqualPhaseContext
import Hironaka.Analytic.Unibranch.OriginalNativeCurrentTerminalSmoothPhaseMap

/-! The actual terminal phase arrow for the two computed equal-profile phases. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentEqualPhaseMap
noncomputable section
open Hironaka SourceReducedComplexSpace
  HironakaIntrinsicComplexAnalyticRegularLocus OriginalIntrinsicHSSuperlevels OriginalNativeHSShadowOuterState
  OriginalNativeProductWindow OriginalNativeSmoothLocalProduct OriginalNativeHSCurrentSmoothContext
  OriginalNativeHSCurrentEqualPhaseContext OriginalNativeCurrentTerminalSmoothPhaseMap
  HironakaG11VanishingWindows HironakaG11PresReduction HironakaG11CompatibleCanonicalTowers
  HironakaActualPowerBoundaryExponents HironakaG1NativeFiniteProductState

variable {X Y : SourceReducedComplexSpace} {f : X ⟶ Y} {e0 : LocalEmbedding Y} {r : ℕ}
  {O : Opens (productAmbient e0 r)} {a : windowSpace e0 r O ⟶ X}
  {ha : LocallyRingedSpace.IsOpenImmersion a.hom.left} {hChart : a ≫ f = windowFirst e0 r O}
  {KS : Set X.obj.left} {KT : Set Y.obj.left} {S : State X KS} {T : State Y KT}
  (c : Context f e0 r O a ha hChart S T) (hKS : IsCompact KS) (hKT : IsCompact KT)
  (hnS : (singularShadow S).Nonempty) (hnT : (singularShadow T).Nonempty)

private theorem sourceSing (hne : (singularShadow S).Nonempty) : (shadow S ∩ intrinsicSingularLocus S.source.obj).Nonempty := by
  simpa only [singularShadow,inter_comm] using hne
private theorem targetSing (hne : (singularShadow T).Nonempty) : (shadow T ∩ intrinsicSingularLocus T.source.obj).Nonempty := by
  simpa only [singularShadow,inter_comm] using hne
private theorem targetExtra : KT ⊆ (⊤ : Opens Y.obj.left) := by simp
private theorem sourceExtraContains : KS ⊆ sourceExtra c hKT hnT := by
  intro z hz
  exact OriginalNativeHSCurrentPhaseRestriction.contains T c.targetOpen c.targetCompactClosure c.targetRange
    c.targetContains hKT hnT ⊤ targetExtra (c.compactImage ⟨z,hz,rfl⟩)

local notation "ES" => sourceExtra c hKT hnT
local notation "hES" => sourceExtraContains c hKT hnT
local notation "HT" => OriginalNativeHSFactoryTerminalFrame.profile T.source (shadow T) (shadow_compact T hKT) (targetSing hnT)
local notation "HS" => OriginalNativeHSFactoryTerminalFrame.profile S.source (shadow S) (shadow_compact S hKS) (sourceSing hnS)
local notation "wS" => OriginalNativeHSCurrentPhaseRestriction.phaseWindow S c.sourceOpen c.sourceCompactClosure c.sourceRange c.sourceContains hKS hnS ES hES
local notation "wT" => OriginalNativeHSCurrentPhaseRestriction.phaseWindow T c.targetOpen c.targetCompactClosure c.targetRange c.targetContains hKT hnT ⊤ targetExtra
local notation "rS" => OriginalNativeHSCurrentPhaseRestriction.phaseRawRecord S c.sourceOpen c.sourceCompactClosure c.sourceRange c.sourceContains hKS hnS ES hES
local notation "rT" => OriginalNativeHSCurrentPhaseRestriction.phaseRawRecord T c.targetOpen c.targetCompactClosure c.targetRange c.targetContains hKT hnT ⊤ targetExtra
local notation "tS" => OriginalNativeHSCurrentPhaseRestriction.phaseStage S c.sourceOpen c.sourceCompactClosure c.sourceRange c.sourceContains hKS hnS ES hES
local notation "tT" => OriginalNativeHSCurrentPhaseRestriction.phaseStage T c.targetOpen c.targetCompactClosure c.targetRange c.targetContains hKT hnT ⊤ targetExtra
local notation "xS" => OriginalNativeHSCurrentPhaseRestriction.phaseNativeStage S c.sourceOpen c.sourceCompactClosure c.sourceRange c.sourceContains hKS hnS ES hES
local notation "xT" => OriginalNativeHSCurrentPhaseRestriction.phaseNativeStage T c.targetOpen c.targetCompactClosure c.targetRange c.targetContains hKT hnT ⊤ targetExtra
local notation "eS" => OriginalNativeHSFactoryTerminalFrame.exponent S.source (shadow S) (shadow_compact S hKS) (sourceSing hnS)
local notation "eT" => OriginalNativeHSFactoryTerminalFrame.exponent T.source (shadow T) (shadow_compact T hKT) (targetSing hnT)
local notation "dS" => OriginalNativeHSFactoryTerminalFrame.dimension S.source (shadow S) (shadow_compact S hKS) (sourceSing hnS)
local notation "dT" => OriginalNativeHSFactoryTerminalFrame.dimension T.source (shadow T) (shadow_compact T hKT) (targetSing hnT)

/-- The actual computed terminal phase endpoints admit the unique smooth
arrow when their actual factory profiles match under the product transform. -/
theorem exists_unique_equal_phase_map (hProfile : HS = finiteProductHS r HT) :
    ∃! g : (xS).Y ⟶ (xT).Y, IsSmoothMorphism g ∧
      g ≫ (xT).q = (xS).q ≫ (pastContext c hKS hKT hnS hnT).map := by
  have hrecS : ∀ i, IsNativeWindowRecord (wS i) (rS i) (finiteProductHS r HT) := by
    intro i
    rw [←hProfile]
    exact OriginalNativeHSCurrentPhaseRestriction.phase_native_record S c.sourceOpen c.sourceCompactClosure
      c.sourceRange c.sourceContains hKS hnS ES hES i
  have hrecT : ∀ i, IsNativeWindowRecord (wT i) (rT i) HT :=
    OriginalNativeHSCurrentPhaseRestriction.phase_native_record T c.targetOpen c.targetCompactClosure
      c.targetRange c.targetContains hKT hnT ⊤ targetExtra
  have hdS : dS = (finiteProductHS r HT) 1 - 1 := by
    rw [OriginalNativeHSFactoryTerminalFrame.dimension_eq, hProfile]
  have hdT : dT = HT 1 - 1 := OriginalNativeHSFactoryTerminalFrame.dimension_eq _ _ _ _
  have hpS : ∀ i, 1 ≤ eS i := OriginalNativeHSFactoryTerminalFrame.positive _ _ _ _
  have hpT : ∀ i, 1 ≤ eT i := OriginalNativeHSFactoryTerminalFrame.positive _ _ _ _
  have hrS := OriginalNativeHSCurrentPhaseRestriction.phase_terminal S c.sourceOpen c.sourceCompactClosure
    c.sourceRange c.sourceContains hKS hnS ES hES
  have hrT := OriginalNativeHSCurrentPhaseRestriction.phase_terminal T c.targetOpen c.targetCompactClosure
    c.targetRange c.targetContains hKT hnT ⊤ targetExtra
  have hCoverS := OriginalNativeHSCurrentPhaseRestriction.phase_threshold_covered S c.sourceOpen c.sourceCompactClosure
    c.sourceRange c.sourceContains hKS hnS ES hES
  have hCoverT := OriginalNativeHSCurrentPhaseRestriction.phase_threshold_covered T c.targetOpen c.targetCompactClosure
    c.targetRange c.targetContains hKT hnT ⊤ targetExtra
  have hOffS := OriginalNativeHSCurrentPhaseRestriction.phase_off_threshold S c.sourceOpen c.sourceCompactClosure
    c.sourceRange c.sourceContains hKS hnS ES hES
  have hOffT := OriginalNativeHSCurrentPhaseRestriction.phase_off_threshold T c.targetOpen c.targetCompactClosure
    c.targetRange c.targetContains hKT hnT ⊤ targetExtra
  rw [hProfile] at hCoverS
  have hOffS' := (congrArg (fun U => IsIsoOver (xS).q Uᶜ)
    (congrArg (originalSingularHSThreshold _) hProfile)).mp hOffS
  exact exists_unique_phase_map (pastContext c hKS hKT hnS hnT) HT wS wT rS rT hrecS hrecT hdS hdT eS eT hpS hpT
    (tS).T (tT).T xS xT (tS).canonical (tT).canonical hrS hrT hCoverS hCoverT hOffS' hOffT
end
end Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentEqualPhaseMap
