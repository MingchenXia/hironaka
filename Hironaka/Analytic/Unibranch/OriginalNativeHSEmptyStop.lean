import Hironaka.Analytic.Unibranch.OriginalNativeHSBaseOpenNativeStage
import Hironaka.Analytic.Unibranch.OriginalNativeShadowUniformBound
import Hironaka.Analytic.Unibranch.OriginalNativeCurrentHSReadout
import Hironaka.Analytic.Unibranch.OriginalNativeHSThresholdIsomorphism

/-! EMPTY actual compact threshold-shadow derives one true base shrink and
WHOLE terminal retained canonical towers, on the SAME native physical history.
No future terminal packet or smoothness of the entire lower-H source is assumed.
Blueprint FIRST: original-native-hs-empty-stop.tex. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSEmptyStop
noncomputable section
open Hironaka Hironaka.BlowupSequences
  Hironaka SourceReducedComplexSpace OriginalLocalEmbeddingStalkHS
  HironakaIntrinsicComplexAnalyticRegularLocus OriginalIntrinsicHSSuperlevels
  HironakaG11VanishingWindows HironakaG11VanishingPrincipalization HironakaG11PresReduction
  HironakaG11StrictTransformTowers HironakaG11CompatibleCanonicalTowers
  HironakaG11HSPhaseInduction HironakaActualPowerBoundaryExponents
  OriginalNativeHSOuterHistory OriginalRelativelyCompactRestriction
  BlowupTowers BlowupTowerTransforms ResolutionInvariantSeq MarkedIdeals MarkedIdeals.MarkedIdeal
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

/-- ONLY ordinary PRESENT raw records, actual stages/history and an EMPTY shadow branch. -/
structure Input (n : ℕ) (Λ : Type) [LinearOrder Λ] where
  base : SourceReducedComplexSpace
  ι : Type
  window : ι → DimEmbedding base n
  rawRecord : ∀ i, MarkedIdeal n (Amb window i)
  profile : ℕ → ℕ
  native : ∀ i, IsNativeWindowRecord (window i) (rawRecord i) profile
  exponent : ι → ℕ
  positive : ∀ i, 1 ≤ exponent i
  invariant : ResolutionInvariant.{0} n n Λ
  clock : ℕ
  stage : GStage invariant (fun i => powerMarked (rawRecord i) (exponent i)) (mapAdm window) clock
  nativeStage : XStage window stage.T
  history : PhysicalHistory base nativeStage.Y
  history_projection : history.projection = nativeStage.q
  compact : Set base.obj.left
  compact_isCompact : IsCompact compact
  shadowEmpty : originalSingularHSThreshold nativeStage.Y profile ∩
    nativeStage.q.hom.left.base ⁻¹' compact = ∅

variable {n : ℕ} {Λ : Type} [LinearOrder Λ] (P : Input n Λ)

private theorem threshold_closed : IsClosed (originalSingularHSThreshold P.nativeStage.Y P.profile) :=
  (original_hs_threshold_dictionary P.nativeStage.Y P.profile).2.1.isClosed

/-- Internally computed ONE actual precompact base retaining the entire compact set. -/
def neighbourhood := OriginalNativeShadowUniformBound.emptyNeighbourhood P.nativeStage.q
  P.nativeStage.isSingularCentreModification.isProperMap P.compact P.compact_isCompact
  (originalSingularHSThreshold P.nativeStage.Y P.profile) (threshold_closed P) P.shadowEmpty

private abbrev targetOpen := (neighbourhood P).openSet
private abbrev targetCompact := (neighbourhood P).compactClosure
private abbrev targetInclusion := inclusion P.base (targetOpen P) (targetCompact P)
private theorem targetInclusion_open : LocallyRingedSpace.IsOpenImmersion (targetInclusion P).hom.left :=
  inclusion_isOpenImmersion _ _ _

def window : P.ι → DimEmbedding (restriction P.base (targetOpen P) (targetCompact P)) n :=
  OriginalNativeHSBaseOpenWindows.window P.window (targetInclusion P) (targetInclusion_open P)

def rawRecord (i : P.ι) : MarkedIdeal n (Amb (window P) i) :=
  OriginalNativeHSBaseOpenWindows.rawRecord P.window (targetInclusion P) (targetInclusion_open P)
    P.rawRecord i

theorem native_record (i : P.ι) : IsNativeWindowRecord (window P i) (rawRecord P i) P.profile :=
  OriginalNativeHSBaseOpenWindows.native_record P.window (targetInclusion P) (targetInclusion_open P)
    P.rawRecord P.native i

def record (i : P.ι) : MarkedIdeal n (Amb (window P) i) := powerMarked (rawRecord P i) (P.exponent i)

/-- SAME whole restricted canonical histories, including every old/born boundary entry. -/
def stage : GStage P.invariant (record P) (mapAdm (window P)) P.clock :=
  OriginalNativeHSBaseOpenStage.stage P.window (targetInclusion P) (targetInclusion_open P)
    P.rawRecord P.native P.exponent P.positive P.invariant P.stage

def nativeStage : XStage (window P) (stage P).T :=
  OriginalNativeHSBaseOpenNativeStage.compatibleNativeStage P.window (targetOpen P) (targetCompact P)
    P.rawRecord P.native P.exponent P.positive P.invariant P.stage P.nativeStage P.history P.history_projection

def physicalHistory : PhysicalHistory (restriction P.base (targetOpen P) (targetCompact P))
    (nativeStage P).Y :=
  OriginalNativeHSBaseOpenNativeStage.physicalHistory P.history (targetOpen P) (targetCompact P)

def sourceInclusion : (nativeStage P).Y ⟶ P.nativeStage.Y :=
  OriginalNativeHSBaseOpenNativeStage.sourceInclusion P.history (targetOpen P) (targetCompact P)

theorem sourceInclusion_isOpenImmersion :
    LocallyRingedSpace.IsOpenImmersion (sourceInclusion P).hom.left :=
  inclusion_isOpenImmersion _ _ _

theorem history_projection : (physicalHistory P).projection = (nativeStage P).q := rfl

theorem history_length : (physicalHistory P).length = P.history.length :=
  OriginalNativeHSBaseOpenNativeStage.physical_length P.history (targetOpen P) (targetCompact P)

theorem projection_square : (nativeStage P).q ≫ targetInclusion P =
    sourceInclusion P ≫ P.nativeStage.q :=
  (OriginalNativeHSBaseOpenNativeStage.projection_square P.history (targetOpen P) (targetCompact P)).trans
    (congrArg (fun a => sourceInclusion P ≫ a) P.history_projection)

theorem scalar : (nativeStage P).q.hom.left ≫
    (restriction P.base (targetOpen P) (targetCompact P)).obj.hom = (nativeStage P).Y.obj.hom :=
  Over.w (nativeStage P).q.hom

theorem proper : IsProperMap (nativeStage P).q.hom.left.base :=
  (nativeStage P).isSingularCentreModification.isProperMap

theorem originalReg : IsIsoOver (nativeStage P).q
    (intrinsicRegularLocus (restriction P.base (targetOpen P) (targetCompact P)).obj) :=
  (nativeStage P).isSingularCentreModification.isIsoOver_intrinsicRegularLocus

def compact : Set (restriction P.base (targetOpen P) (targetCompact P)).obj.left :=
  (neighbourhood P).shadow

theorem compact_isCompact : IsCompact (compact P) :=
  (neighbourhood P).shadow_compact P.compact_isCompact

/-- The ENTIRE actual new native threshold is empty, not just its compact shadow. -/
theorem threshold_empty : originalSingularHSThreshold (nativeStage P).Y P.profile = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hOld : (sourceInclusion P).hom.left.base y ∈
      originalSingularHSThreshold P.nativeStage.Y P.profile :=
    (Set.ext_iff.mp (OriginalNativeHSThresholdIsomorphism.threshold_preimage_openImmersion P.profile
      (sourceInclusion P) (sourceInclusion_isOpenImmersion P)) y).mpr hy
  have hOver : P.nativeStage.q.hom.left.base ((sourceInclusion P).hom.left.base y) ∈
      range (neighbourhood P).inclusion.hom.left.base := by
    rw [(neighbourhood P).inclusion_range]
    change P.nativeStage.q.hom.left.base y.val ∈ targetOpen P
    have hz : P.history.projection.hom.left.base y.val ∈ targetOpen P := y.property
    exact P.history_projection ▸ hz
  have hBad : (sourceInclusion P).hom.left.base y ∈
      P.nativeStage.q.hom.left.base ⁻¹' range (neighbourhood P).inclusion.hom.left.base ∩
        originalSingularHSThreshold P.nativeStage.Y P.profile := ⟨hOver, hOld⟩
  have he : P.nativeStage.q.hom.left.base ⁻¹' range (neighbourhood P).inclusion.hom.left.base ∩
      originalSingularHSThreshold P.nativeStage.Y P.profile = ∅ :=
    OriginalNativeShadowUniformBound.empty_threshold_preimage P.nativeStage.q
      P.nativeStage.isSingularCentreModification.isProperMap P.compact P.compact_isCompact
      (originalSingularHSThreshold P.nativeStage.Y P.profile) (threshold_closed P) P.shadowEmpty
  rw [he] at hBad
  exact hBad

/-- EVERY ambient cosupport point is excluded, using genuine presentation/carrier incidence. -/
theorem cosupp_empty (i : P.ι) : (geoTransformAlong (record P i) ((stage P).T i).2).cosupp = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hP := OriginalNativeCurrentHSReadout.chosen_presentation (window P) (rawRecord P)
    P.exponent (native_record P) P.positive P.invariant i ((stage P).T i).2 ((stage P).canonical i)
  have hCarrier := hP.1 hy
  have hc : y ∈ (nativeStage P).carrier i := by
    rw [(nativeStage P).carrier_eq i]
    exact hCarrier
  let c : (nativeStage P).carrier i := ⟨y, hc⟩
  have hData := OriginalNativeCurrentHSReadout.current_native_data (window P) (rawRecord P)
    P.exponent (native_record P) P.positive P.invariant (stage P) (nativeStage P) i c
  have hEq := hData.2.1.mp hy
  have hT : ((nativeStage P).map i).hom.left.base c ∈
      originalSingularHSThreshold (nativeStage P).Y P.profile :=
    ⟨hData.2.2 hy, fun l => (congrFun hEq l).ge⟩
  rw [threshold_empty P] at hT
  exact hT

theorem canonical (i : P.ι) : IsCanonical (record P i) (P.invariant.inv (record P i))
    ((stage P).T i).2 := (stage P).canonical i

/-- Genuine WHOLE retained original canonical tower is a geometric resolution. -/
theorem resolution (i : P.ι) : IsGeoResolution (record P i) ((stage P).T i).2 :=
  ⟨P.invariant.isInvValue.isGeoTestTower_of_isCanonical
    (OriginalNativeCurrentHSReadout.chosen_isHSWindowRecord (window P) (rawRecord P)
      P.exponent (native_record P) P.positive i).1 _ (canonical P i), cosupp_empty P i⟩

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSEmptyStop
