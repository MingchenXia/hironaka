import Hironaka.Analytic.Unibranch.OriginalNativeShadowFirstStage
import Hironaka.Analytic.Unibranch.OriginalNativeShadowFirstThresholdCover
import Hironaka.Analytic.Unibranch.OriginalNativeHSUniformRestrictedStage

/-! The SAME actual first blowup initializes the EXISTING compact-shadow phase input.
The missing threshold cover is DERIVED across the actual strict-window choices.
Blueprint FIRST: original-native-hs-first-stage-input.tex. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSFirstStageInput
noncomputable section
open Hironaka Hironaka SourceReducedComplexSpace
  OriginalLocalEmbeddingStalkHS OriginalIntrinsicHSSuperlevels OriginalNativeHSCompactShadowWindows
  OriginalNativeHSOuterHistory BlowupTowers CanonicalCentres

variable {X : SourceReducedComplexSpace} {K : Set X.obj.left}
  (M : Maximum X K) (hK : IsCompact K)
  (s : OriginalNativeShadowFirstBlowup.Step M hK)
local notation "H" => originalStalkHS X M.point
local notation "N" => OriginalNativeShadowFirstBlowup.target M hK
local notation "F" => OriginalNativeShadowFirstBlowup.centres M hK
local notation "w" => OriginalNativeShadowFlatWindows.window M hK
local notation "xs" => OriginalNativeShadowFirstStage.nativeStage M hK s

/-- The literal compact inverse of the original retained compact set. -/
def compact : Set (N).source.obj.left := (N).inclusion.hom.left.base ⁻¹' K

theorem compact_isCompact : IsCompact (compact M hK) := (N).shadow_compact hK

/-- The actual first singular-centre arrow, with its chronological provenance. -/
def physicalHistory : PhysicalHistory (N).source s.source :=
  .snoc (.nil (N).source) s.projection s.singular

theorem history_projection : (physicalHistory M hK s).projection=(xs).q := by
  change s.projection ≫ 𝟙 (N).source=s.projection
  exact Category.comp_id _

theorem physical_length : (physicalHistory M hK s).length=1 := rfl

/-- Concrete range join from B34's FirstPrefix choices to the ACTUAL FirstStage choices. -/
theorem threshold_covered :
    originalSingularHSThreshold s.source H ∩ s.projection.hom.left.base ⁻¹' compact M hK ⊆
      ⋃ i,range (((xs).map i).hom.left.base) := by
  rintro y ⟨hyC,hyK⟩
  obtain ⟨i,hi⟩:=mem_iUnion.mp
    (OriginalNativeShadowFirstThresholdCover.threshold_shadow_covered M hK s ⟨hyK,hyC⟩)
  have hOld : s.projection.hom.left.base y∈range ((F).windowMap i).hom.left.base :=
    (Set.ext_iff.mp (OriginalNativeShadowFirstPrefix.nativeWindow_range M hK s i) y).mp hi
  have hFlat : s.projection.hom.left.base y∈range (w i).toLocalEmbedding.toPoint :=
    (Set.ext_iff.mp (OriginalNativeShadowFlatWindows.range_dictionary M hK i)
      (s.projection.hom.left.base y)).mpr hOld
  exact mem_iUnion.mpr ⟨i,(Set.ext_iff.mp
    (OriginalNativeShadowFirstStage.native_range M hK s i) y).mpr hFlat⟩

/-- Existing input, INTERNALLY initialized from the SAME actual first physical step.
The only branch hypothesis says that the actual retained threshold has survived. -/
def phaseInput
    (hne : (originalSingularHSThreshold s.source H ∩
      s.projection.hom.left.base ⁻¹' compact M hK).Nonempty) :
    @OriginalNativeHSUniformRestrictedStage.Input (H 1-1) (ValTy (H 1-1))
      inferInstance ⟨OriginalNativeShadowInvariantCentre.level M hK⟩ := by
  letI : Nonempty (ValTy (H 1-1)) := ⟨OriginalNativeShadowInvariantCentre.level M hK⟩
  exact
    { base := (N).source
      ι := (M.windows hK).ι
      window := w
      rawRecord := OriginalNativeShadowFlatWindows.rawRecord M hK
      profile := H
      native := OriginalNativeShadowFlatWindows.native_record M hK
      exponent := OriginalNativeShadowInvariantCentre.exponent M hK
      positive := OriginalNativeShadowInvariantCentre.exponent_pos M hK
      commonMark i j := (OriginalNativeShadowFlatWindows.record_mark M hK i).trans
        (OriginalNativeShadowFlatWindows.record_mark M hK j).symm
      invariant := OriginalNativeShadowInvariantCentre.invariant M
      clock := 1
      stage := OriginalNativeShadowFirstStage.ambientStage M hK
      nativeStage := xs
      history := physicalHistory M hK s
      history_projection := history_projection M hK s
      compact := compact M hK
      compact_isCompact := compact_isCompact M hK
      shadowCover := threshold_covered M hK s
      shadowNonempty := hne }

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSFirstStageInput
