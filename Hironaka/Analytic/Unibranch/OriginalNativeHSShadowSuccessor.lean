import Hironaka.Analytic.Unibranch.OriginalNativeHSUniformRestrictedStage
import Hironaka.Analytic.Unibranch.OriginalNativeCurrentCentreBlowup
import Hironaka.Analytic.Unibranch.OriginalNativeCurrentHSNonincrease

/-! Actual dynamic successor of the SAME uniformly restricted canonical and
physical histories. Blueprint FIRST: original-native-hs-shadow-successor.tex.
No centre/p/future-window/bound/compactcosupp packet is an input. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSShadowSuccessor
noncomputable section
open Hironaka Hironaka.BlowupSequences
  Hironaka SourceReducedComplexSpace HironakaG11VanishingWindows
  HironakaG11VanishingPrincipalization HironakaG11StrictTransformTowers HironakaG11CompatibleCanonicalTowers
  HironakaG11ManifoldWindowCentres HironakaG11WindowTowers HironakaG11BlowupLocality
  OriginalNativeHSOuterHistory OriginalNativeHSUniformRestrictedStage OriginalIntrinsicHSSuperlevels
  OriginalLocalEmbeddingStalkHS HironakaG11SingularCentreModification SmoothCentreModification
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaActualPowerBoundaryExponents

variable {n : ℕ} {Λ : Type} [LinearOrder Λ] [Nonempty Λ] (P : Input n Λ)
private abbrev windows := OriginalNativeHSUniformRestrictedStage.window P
private abbrev raw := OriginalNativeHSUniformRestrictedStage.rawRecord P
private abbrev native := OriginalNativeHSUniformRestrictedStage.native_record P
private abbrev records := OriginalNativeHSUniformRestrictedStage.record P
private abbrev currentStage := OriginalNativeHSUniformRestrictedStage.stage P
private abbrev currentNative := OriginalNativeHSUniformRestrictedStage.nativeStage P
private abbrev domains := OriginalNativeCurrentCentreBlowup.domain (windows P) (raw P) P.profile (native P) P.exponent P.positive
private abbrev cosuppSubset := OriginalNativeCurrentCentreBlowup.initial_cosupp_subset
  (windows P) (raw P) P.profile (native P) P.exponent P.positive P.invariant
private abbrev selfCover := OriginalNativeCurrentCentreBlowup.selfCover (windows P) (raw P) P.exponent
private abbrev transport := OriginalNativeCurrentCentreBlowup.recordsTransport
  (windows P) (raw P) P.profile (native P) P.exponent P.positive (common_mark P) P.invariant
private abbrev family := OriginalNativeCurrentCentreBlowup.centres
  (windows P) (raw P) P.profile (native P) P.exponent P.positive (common_mark P) P.invariant (currentStage P) (currentNative P)

/-- TRUE next canonical heads of the SAME retained histories. -/
def ambientStage : GStage P.invariant.toResolutionInvariant (records P) (mapAdm (windows P)) (P.clock + 1) :=
  (currentStage P).next (domains P) (cosuppSubset P) (selfCover P) (adm_exists_map (windows P)) (transport P)

/-- The actual internally constructed native centre blowup, not a caller input. -/
def step := OriginalNativeCurrentCentreBlowup.step
  (windows P) (raw P) P.profile (native P) P.exponent P.positive (common_mark P) P.invariant
  (currentStage P) (currentNative P) (threshold_covered P)

private theorem attained : ∃ i, ∃ c : (currentNative P).carrier i,
    c.val ∈ rcos (records P) (currentStage P).T i ∧
    rvalue P.invariant.toResolutionInvariant (records P) (currentStage P).T i c.val = level P := by
  obtain ⟨i, c, hc, hv, _hK⟩ := maximum_attained P
  exact ⟨i, c, hc, hv⟩

theorem centre_eq_level (i : P.ι) : (family P).centre i =
    {y | y ∈ rcos (records P) (currentStage P).T i ∧
      rvalue P.invariant.toResolutionInvariant (records P) (currentStage P).T i y = level P} :=
  OriginalNativeCurrentCentreBlowup.centre_eq_level
    (windows P) (raw P) P.profile (native P) P.exponent P.positive (common_mark P) P.invariant
    (currentStage P) (currentNative P) (level P)
    (fun i c hc => uniform_bound P i c.val hc) (attained P) i

private abbrev nextSpace (i : P.ι) : CMfd.{0} n :=
  gnextSpace (domains P) (cosuppSubset P) (selfCover P) (adm_exists_map (windows P)) (transport P) (currentStage P) i
private abbrev nextMap (i : P.ι) : nextSpace P i → ((currentStage P).T i).1 :=
  gnextMap (domains P) (cosuppSubset P) (selfCover P) (adm_exists_map (windows P)) (transport P) (currentStage P) i
private abbrev nextBlowup (i : P.ι) :=
  gnextMap_isBlowup (domains P) (cosuppSubset P) (selfCover P) (adm_exists_map (windows P)) (transport P) (currentStage P) i

private theorem compatible : (family P).Compatible :=
  OriginalNativeCurrentCentreBlowup.centres_compatible
    (windows P) (raw P) P.profile (native P) P.exponent P.positive (common_mark P) P.invariant
    (currentStage P) (currentNative P)
private theorem closed : IsClosed (family P).support :=
  OriginalNativeCurrentCentreBlowup.support_closed
    (windows P) (raw P) P.profile (native P) P.exponent P.positive (common_mark P) P.invariant
    (currentStage P) (currentNative P) (threshold_covered P)
private theorem singular : (family P).support ⊆
    HironakaIntrinsicComplexAnalyticRegularLocus.intrinsicSingularLocus (currentNative P).Y.obj :=
  OriginalNativeCurrentCentreBlowup.support_singular
    (windows P) (raw P) P.profile (native P) P.exponent P.positive (common_mark P) P.invariant
    (currentStage P) (currentNative P)

private theorem actual_blowup : IsSmoothCentreBlowup (step P).projection
    (OriginalAnalyticClosedSubspace.inclusion (currentNative P).Y (family P).support
      ((family P).isAnalyticSubset_support (compatible P) (closed P))) := (step P).blowup

private def strictSource (i : P.ι) := OriginalNativeShadowThresholdStep.strictSource
  (family P) (nextSpace P) (nextMap P) (nextBlowup P) i

private theorem exists_windows : ∃ L : ∀ i, strictSource P i ⟶ (step P).source, ∀ i,
    LocallyRingedSpace.IsOpenImmersion (L i).hom.left ∧
    L i ≫ (step P).projection = OriginalNativeShadowThresholdStep.strictProjection
      (family P) (nextSpace P) (nextMap P) (nextBlowup P) i ≫ (family P).map i ∧
    range (L i).hom.left.base = (step P).projection.hom.left.base ⁻¹' range ((family P).map i).hom.left.base ∧
    ∀ L', L' ≫ (step P).projection = OriginalNativeShadowThresholdStep.strictProjection
      (family P) (nextSpace P) (nextMap P) (nextBlowup P) i ≫ (family P).map i → L' = L i :=  OriginalNativeShadowThresholdStep.exists_strict_native_windows
  (family P) (compatible P) (closed P) (step P).projection (actual_blowup P)
  (nextSpace P) (nextMap P) (nextBlowup P) (singular P)

/-- Every window/strict carrier/map is DERIVED on the SAME actual native step. -/
def nativeStage : XStage (windows P) (ambientStage P).T where
  Y := (step P).source
  q := (step P).projection ≫ (currentNative P).q
  isSingularCentreModification := .cons (step P).projection (currentNative P).q
    (step P).singular (currentNative P).isSingularCentreModification
  carrier i := strictTransform n (nextMap P i) ((currentNative P).carrier i)
  analytic i := HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
    (nextBlowup P i) ((currentNative P).analytic i)
  map := (exists_windows P).choose
  isOpenImmersion i := (exists_windows P).choose_spec i |>.1
  carrier_eq i := OriginalNativeCurrentHSNonincrease.strict_carrier_next_eq
    (windows P) (raw P) P.exponent (native P) P.positive P.invariant.toResolutionInvariant
    (currentStage P) (currentNative P) (transport P) i
  square i c hc := by
    have h1 := congrArg (fun f => f.hom.left.base c) ((exists_windows P).choose_spec i).2.1
    change (currentNative P).q.hom.left.base
      ((step P).projection.hom.left.base (((exists_windows P).choose i).hom.left.base c)) = _
    exact (congrArg (currentNative P).q.hom.left.base h1).trans
      ((currentNative P).square i
        ((EmbeddedBlowup.strictTransformMorphism (nextBlowup P i) ((currentNative P).analytic i)).hom.left.base c) hc)
  range_map i := by
    refine ((exists_windows P).choose_spec i).2.2.1.trans ?_
    ext y
    exact Set.ext_iff.mp ((currentNative P).range_map i) ((step P).projection.hom.left.base y)

theorem native_projection : (nativeStage P).q = (step P).projection ≫ (currentNative P).q := rfl

def physicalHistory := PhysicalHistory.snoc (OriginalNativeHSUniformRestrictedStage.physicalHistory P)
  (step P).projection (step P).singular

theorem history_projection : (physicalHistory P).projection = (nativeStage P).q :=
  congrArg (fun q => (step P).projection ≫ q) (OriginalNativeHSUniformRestrictedStage.history_projection P)

theorem physical_length : (physicalHistory P).length = P.history.length + 1 :=
  congrArg (fun m => m + 1) (OriginalNativeHSUniformRestrictedStage.physical_length P)

theorem surviving_value_lt (i : P.ι) (z : ((ambientStage P).T i).1)
    (hz : z ∈ rcos (records P) (ambientStage P).T i) :
    rvalue P.invariant.toResolutionInvariant (records P) (ambientStage P).T i z < level P :=
  rvalue_next_lt (domains P) (cosuppSubset P) (selfCover P) (adm_exists_map (windows P)) (transport P)
    (currentStage P) (OriginalNativeHSUniformRestrictedStage.greatest P) i z hz

private theorem hs_data :
    (∀ y, originalStalkHS (step P).source y ≤ originalStalkHS (currentNative P).Y ((step P).projection.hom.left.base y)) ∧
    IsIsoOver (step P).projection (originalSingularHSThreshold (currentNative P).Y P.profile)ᶜ := by
  obtain ⟨_L, _hL, hHS, hOff, _hEq⟩ := OriginalNativeCurrentHSNonincrease.exists_next_hs_nonincrease
    (windows P) (raw P) P.exponent (native P) P.positive P.invariant.toResolutionInvariant
    (currentStage P) (currentNative P) (transport P) (closed P) (step P).projection (actual_blowup P)
  exact ⟨hHS, hOff⟩

theorem hs_nonincrease (y : (step P).source.obj.left) :
    originalStalkHS (step P).source y ≤ originalStalkHS (currentNative P).Y ((step P).projection.hom.left.base y) :=
  (hs_data P).1 y

theorem off_threshold : IsIsoOver (step P).projection
    (originalSingularHSThreshold (currentNative P).Y P.profile)ᶜ := (hs_data P).2

theorem threshold_covered : originalSingularHSThreshold (nativeStage P).Y P.profile ⊆
    ⋃ i, range (((nativeStage P).map i).hom.left.base) := by
  intro y hy
  have hImage := OriginalNativeShadowThresholdStep.threshold_image (family P) (compatible P) (closed P)
    (step P).projection (actual_blowup P)
    (OriginalNativeCurrentCentreBlowup.support_threshold
      (windows P) (raw P) P.profile (native P) P.exponent P.positive (common_mark P) P.invariant
      (currentStage P) (currentNative P)) hy
  obtain ⟨i, hi⟩ := mem_iUnion.mp (OriginalNativeHSUniformRestrictedStage.threshold_covered P hImage)
  exact mem_iUnion.mpr ⟨i, (Set.ext_iff.mp ((exists_windows P).choose_spec i).2.2.1 y).mpr hi⟩

theorem centre_meets_shadow : ((currentNative P).q.hom.left.base ⁻¹' compact P ∩ (family P).support).Nonempty := by
  obtain ⟨i, c, hc, hv, hK⟩ := maximum_attained P
  have hSupport := OriginalNativeCurrentCentreBlowup.mem_support_of_value_eq
    (windows P) (raw P) P.profile (native P) P.exponent P.positive (common_mark P) P.invariant
    (currentStage P) (currentNative P) (level P) (fun i c hc => uniform_bound P i c.val hc) i c hc hv
  refine ⟨((currentNative P).map i).hom.left.base c, ?_, hSupport⟩
  let y := ((currentNative P).map i).hom.left.base c
  have hSquare := congrArg (fun f => f.hom.left.base y)
    (OriginalNativeHSBaseOpenNativeStage.projection_square P.history
      (neighbourhood P).openSet (neighbourhood P).compactClosure)
  have hHistory := congrArg (fun q => q.hom.left.base
    ((OriginalNativeHSBaseOpenNativeStage.sourceInclusion P.history
      (neighbourhood P).openSet (neighbourhood P).compactClosure).hom.left.base y)) P.history_projection
  change (OriginalRelativelyCompactRestriction.inclusion P.base (neighbourhood P).openSet (neighbourhood P).compactClosure).hom.left.base
    ((currentNative P).q.hom.left.base y) ∈ P.compact
  exact (hSquare.trans hHistory).symm ▸ hK

/-- The genuine next PRESENT data when its ACTUAL threshold shadow survives. -/
def nextInput (hne : (originalSingularHSThreshold (nativeStage P).Y P.profile ∩
    (nativeStage P).q.hom.left.base ⁻¹' compact P).Nonempty) : Input n Λ where
  base := (neighbourhood P).source
  ι := P.ι
  window := windows P
  rawRecord := raw P
  profile := P.profile
  native := native P
  exponent := P.exponent
  positive := P.positive
  commonMark := common_mark P
  invariant := P.invariant
  clock := P.clock + 1
  stage := ambientStage P
  nativeStage := nativeStage P
  history := physicalHistory P
  history_projection := history_projection P
  compact := compact P
  compact_isCompact := compact_isCompact P
  shadowCover := fun _ hy => threshold_covered P hy.1
  shadowNonempty := hne

private theorem level_lt_of_bound (Q : Input n Λ) (b : Λ)
    (hBound : ∀ i (y : (Q.stage.T i).1), y ∈ rcos (fun j => powerMarked (Q.rawRecord j) (Q.exponent j)) Q.stage.T i →
      rvalue Q.invariant.toResolutionInvariant (fun j => powerMarked (Q.rawRecord j) (Q.exponent j)) Q.stage.T i y < b) :
    level Q < b := by
  let hD : ∀ i, ResolutionInvariantSpec.IsInvDomain n (powerMarked (Q.rawRecord i) (Q.exponent i)) :=
    fun i => (OriginalNativeCurrentHSReadout.chosen_isHSWindowRecord Q.window Q.rawRecord Q.exponent
      Q.native Q.positive i).1
  have hClass := HironakaG1NativeWindowInitialClass.initialClassData_of_native_powers
    Q.window Q.rawRecord Q.profile Q.native Q.exponent Q.positive Q.commonMark
  obtain ⟨i, c, _hca, hc, hv, _hOver⟩ := OriginalNativeShadowUniformBound.maximizing_window
    Q.window (fun j => powerMarked (Q.rawRecord j) (Q.exponent j)) Q.invariant Q.stage Q.nativeStage
    hD hClass Q.nativeStage.q Q.nativeStage.isSingularCentreModification.isProperMap
    Q.compact Q.compact_isCompact (OriginalNativeHSUniformRestrictedStage.threshold Q)
    (threshold_closed Q) (threshold_trace Q) Q.shadowCover Q.shadowNonempty
  have hValue : rvalue Q.invariant.toResolutionInvariant
      (fun j => powerMarked (Q.rawRecord j) (Q.exponent j)) Q.stage.T i c.val = level Q := hv
  exact hValue ▸ hBound i c.val hc

/-- Actual strict descent for the NEXT internally chosen compact-shadow maximum. -/
theorem next_level_lt (hne : (originalSingularHSThreshold (nativeStage P).Y P.profile ∩
    (nativeStage P).q.hom.left.base ⁻¹' compact P).Nonempty) : level (nextInput P hne) < level P :=
  level_lt_of_bound (nextInput P hne) (level P) (fun i y hy => surviving_value_lt P i y hy)

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSShadowSuccessor
