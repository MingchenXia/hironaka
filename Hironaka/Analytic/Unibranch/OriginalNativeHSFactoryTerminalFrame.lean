import Hironaka.Analytic.Unibranch.OriginalNativeHSShadowPhaseFactory
import Hironaka.Analytic.Unibranch.OriginalNativeHSShadowInitialCover
import Hironaka.Analytic.Unibranch.OriginalNativeHSShadowFactoryGeometry

/-! ACTUAL factory data at its genuine dimension, with literal-original
canonicality. Blueprint FIRST: original-native-hs-factory-terminal-frame.tex.
No caller frame/phase supplier or independent endpoint is introduced. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSFactoryTerminalFrame
noncomputable section
open Hironaka SourceReducedComplexSpace
  OriginalLocalEmbeddingStalkHS OriginalIntrinsicHSSuperlevels
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaG11VanishingWindows
  HironakaG11VanishingPrincipalization HironakaG11StrictTransformTowers
  HironakaG11CompatibleCanonicalTowers HironakaG11PresReduction
  MarkedIdeals HironakaActualPowerBoundaryExponents CanonicalCentres

variable (X : SourceReducedComplexSpace) (K : Set X.obj.left) (hK : IsCompact K)
  (hSing : (K ∩ intrinsicSingularLocus X.obj).Nonempty)
local notation "M" => OriginalNativeHSShadowPhaseFactory.maximum X K hK hSing
local notation "P" => OriginalNativeHSShadowPhaseFactory.finalInput X K hK hSing
local notation "B" => OriginalNativeHSShadowPhaseFactory.base X K hK hSing

/-- The true computed dimension; no unproved identification with a separately chosen model. -/
abbrev dimension : ℕ := originalStalkHS (OriginalNativeHSCompactShadowBarrier.nativeSource (M) hK)
  (OriginalNativeHSCompactShadowBarrier.nativePoint (M) hK) 1 - 1
abbrev profile : ℕ → ℕ := originalStalkHS X (OriginalNativeHSCompactShadowWindows.Maximum.point (M))

theorem dimension_eq : dimension X K hK hSing=profile X K hK hSing 1-1 :=
  congrArg (fun H : ℕ → ℕ => H 1-1) (OriginalNativeHSCompactShadowBarrier.nativePoint_hs (M) hK)

def window : (P).ι → DimEmbedding (B) (dimension X K hK hSing) := OriginalNativeHSEmptyStop.window (P)
def rawRecord : ∀i,MarkedIdeal (dimension X K hK hSing) (Amb (window X K hK hSing) i) :=
  OriginalNativeHSEmptyStop.rawRecord (P)

theorem native_record (i : (P).ι) : IsNativeWindowRecord (window X K hK hSing i)
    (rawRecord X K hK hSing i) (profile X K hK hSing) :=
  (congrArg (fun H => IsNativeWindowRecord (window X K hK hSing i)
    (rawRecord X K hK hSing i) H) (OriginalNativeHSShadowPhaseFactory.profile_eq X K hK hSing)).mp
      (OriginalNativeHSEmptyStop.native_record (P) i)

def exponent : (P).ι → ℕ := (P).exponent
theorem positive (i : (P).ι) : 1≤exponent X K hK hSing i := (P).positive i

/-- EXACT old towers and clock; only the already-proved literal original
canonicality is exposed without the route wrapper. -/
def stage : GStage (canonicalInvariant (dimension X K hK hSing))
    (fun i=>powerMarked (rawRecord X K hK hSing i) (exponent X K hK hSing i))
    (mapAdm (window X K hK hSing)) (P).clock where
  T := (OriginalNativeHSEmptyStop.stage (P)).T
  length := (OriginalNativeHSEmptyStop.stage (P)).length
  canonical := OriginalNativeHSShadowPhaseFactory.canonical X K hK hSing
  compatible := (OriginalNativeHSEmptyStop.stage (P)).compatible

def nativeStage : XStage (window X K hK hSing) (stage X K hK hSing).T :=
  OriginalNativeHSEmptyStop.nativeStage (P)

theorem history_projection : (OriginalNativeHSShadowPhaseFactory.history X K hK hSing).projection=
    (nativeStage X K hK hSing).q := rfl

theorem terminal (i : (P).ι) : MarkedIdeals.MarkedIdeal.IsGeoResolution
    (powerMarked (rawRecord X K hK hSing i) (exponent X K hK hSing i))
    (((stage X K hK hSing).T i).2) :=
  OriginalNativeHSShadowPhaseFactory.resolution X K hK hSing i

theorem threshold_covered : originalSingularHSThreshold (B) (profile X K hK hSing) ⊆
    ⋃i,range (window X K hK hSing i).toLocalEmbedding.toPoint :=
  OriginalNativeHSShadowInitialCover.factory_initial_threshold_covered X K hK hSing

theorem off_threshold : IsIsoOver (nativeStage X K hK hSing).q
    (originalSingularHSThreshold (B) (profile X K hK hSing))ᶜ :=
  OriginalNativeHSShadowFactoryGeometry.isIsoOver_threshold_compl X K hK hSing

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSFactoryTerminalFrame
