import Hironaka.Analytic.Unibranch.OriginalNativeHSBaseOpenCurrentReadout
import Hironaka.Analytic.Unibranch.OriginalNativeShadowUniformBound
import Hironaka.Analytic.Unibranch.OriginalNativeCurrentHSReadout
import Hironaka.Analytic.Unibranch.OriginalNativeHSThresholdIsomorphism

/-! ONE internally derived base shrink of a PRESENT actual compact-shadow stage.
Only initial native records/common powers and actual old histories are inputs.
No lambda, bound, centre, new step or completed phase is an input.
Blueprint FIRST: original-native-hs-uniform-restricted-stage.tex. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSUniformRestrictedStage
noncomputable section
open Hironaka Hironaka.BlowupSequences
  Hironaka SourceReducedComplexSpace HironakaG11VanishingWindows
  HironakaG11VanishingPrincipalization HironakaG11StrictTransformTowers HironakaG11CompatibleCanonicalTowers
  OriginalNativeHSOuterHistory OriginalRelativelyCompactRestriction OriginalLocalEmbeddingStalkHS
  OriginalIntrinsicHSSuperlevels HironakaIntrinsicComplexAnalyticRegularLocus HironakaG11PresReduction
  HironakaG1CanonicalStageCentreIdeal HironakaActualPowerBoundaryExponents
  BlowupTowers BlowupTowerTransforms ResolutionInvariantSeq MarkedIdeals MarkedIdeals.MarkedIdeal CanonicalCentres HironakaG8LocalHistory HironakaG11InvBMClass
open ResolutionInvariantSpec (IsInvDomain)

/-- ONLY genuine PRESENT records/histories and natural current compact-shadow IH. -/
structure Input (n : ℕ) (Λ : Type) [LinearOrder Λ] [Nonempty Λ] where
  base : SourceReducedComplexSpace
  ι : Type
  window : ι → DimEmbedding base n
  rawRecord : ∀ i, MarkedIdeal n (Amb window i)
  profile : ℕ → ℕ
  native : ∀ i, IsNativeWindowRecord (window i) (rawRecord i) profile
  exponent : ι → ℕ
  positive : ∀ i, 1 ≤ exponent i
  commonMark : ∀ i j, (powerMarked (rawRecord i) (exponent i)).d = (powerMarked (rawRecord j) (exponent j)).d
  invariant : BMInvariant.{0,0} n (fun {Y} A A' => LocWPEquiv (X := Y) A A') n Λ
  clock : ℕ
  stage : GStage invariant.toResolutionInvariant (fun i => powerMarked (rawRecord i) (exponent i)) (mapAdm window) clock
  nativeStage : XStage window stage.T
  history : PhysicalHistory base nativeStage.Y
  history_projection : history.projection = nativeStage.q
  compact : Set base.obj.left
  compact_isCompact : IsCompact compact
  shadowCover : originalSingularHSThreshold nativeStage.Y profile ∩ nativeStage.q.hom.left.base ⁻¹' compact ⊆
    ⋃ i, range (nativeStage.map i).hom.left.base
  shadowNonempty : (originalSingularHSThreshold nativeStage.Y profile ∩ nativeStage.q.hom.left.base ⁻¹' compact).Nonempty

variable {n : ℕ} {Λ : Type} [LinearOrder Λ] [Nonempty Λ] (P : Input n Λ)

private abbrev chosen := fun i => powerMarked (P.rawRecord i) (P.exponent i)
private abbrev domains : ∀ i, IsInvDomain n (chosen P i) :=
  fun i => (OriginalNativeCurrentHSReadout.chosen_isHSWindowRecord P.window P.rawRecord P.exponent P.native P.positive i).1

private theorem initialClass : InitialClassData P.window (chosen P) :=
  HironakaG1NativeWindowInitialClass.initialClassData_of_native_powers P.window P.rawRecord P.profile
    P.native P.exponent P.positive P.commonMark

def threshold : Set P.nativeStage.Y.obj.left := originalSingularHSThreshold P.nativeStage.Y P.profile

theorem threshold_closed : IsClosed (threshold P) := (original_hs_threshold_dictionary P.nativeStage.Y P.profile).2.1.isClosed

theorem threshold_trace (i : P.ι) (c : P.nativeStage.carrier i) :
    (P.nativeStage.map i).hom.left.base c ∈ threshold P ↔ c.val ∈ rcos (chosen P) P.stage.T i := by
  have h := OriginalNativeCurrentHSReadout.current_native_data P.window P.rawRecord P.exponent
    P.native P.positive P.invariant.toResolutionInvariant P.stage P.nativeStage i c
  constructor
  · rintro ⟨_hsing, hge⟩
    exact h.2.1.mpr (le_antisymm h.1 hge)
  · intro hc
    exact ⟨h.2.2 hc, fun l => (congrFun (h.2.1.mp hc) l).ge⟩

/-- The computed actual ONE precompact neighbourhood, never a caller packet. -/
def neighbourhood := OriginalNativeShadowUniformBound.neighbourhood P.window (chosen P) P.invariant P.stage P.nativeStage
  (domains P) (initialClass P) P.nativeStage.q P.nativeStage.isSingularCentreModification.isProperMap
  P.compact P.compact_isCompact (threshold P) (threshold_closed P) (threshold_trace P) P.shadowCover

def level : Λ := OriginalNativeShadowUniformBound.level P.window (chosen P) P.invariant P.stage P.nativeStage
  (domains P) (initialClass P) P.nativeStage.q P.nativeStage.isSingularCentreModification.isProperMap
  P.compact P.compact_isCompact (threshold P) (threshold_closed P) (threshold_trace P) P.shadowCover P.shadowNonempty

private abbrev targetOpen := (neighbourhood P).openSet
private abbrev targetCompact := (neighbourhood P).compactClosure
private abbrev targetInclusion := inclusion P.base (targetOpen P) (targetCompact P)
private theorem targetInclusion_open : LocallyRingedSpace.IsOpenImmersion (targetInclusion P).hom.left := inclusion_isOpenImmersion _ _ _

def window : P.ι → DimEmbedding (restriction P.base (targetOpen P) (targetCompact P)) n :=
  OriginalNativeHSBaseOpenWindows.window P.window (targetInclusion P) (targetInclusion_open P)

def rawRecord (i : P.ι) : MarkedIdeal n (Amb (window P) i) :=
  OriginalNativeHSBaseOpenWindows.rawRecord P.window (targetInclusion P) (targetInclusion_open P) P.rawRecord i

theorem native_record (i : P.ι) : IsNativeWindowRecord (window P i) (rawRecord P i) P.profile :=
  OriginalNativeHSBaseOpenWindows.native_record P.window (targetInclusion P) (targetInclusion_open P) P.rawRecord P.native i

def record (i : P.ι) : MarkedIdeal n (Amb (window P) i) := powerMarked (rawRecord P i) (P.exponent i)

def stage : GStage P.invariant.toResolutionInvariant (record P) (mapAdm (window P)) P.clock :=
  OriginalNativeHSBaseOpenStage.stage P.window (targetInclusion P) (targetInclusion_open P)
    P.rawRecord P.native P.exponent P.positive P.invariant.toResolutionInvariant P.stage

def nativeStage : XStage (window P) (stage P).T :=
  OriginalNativeHSBaseOpenNativeStage.compatibleNativeStage P.window (targetOpen P) (targetCompact P)
    P.rawRecord P.native P.exponent P.positive P.invariant.toResolutionInvariant P.stage
    P.nativeStage P.history P.history_projection

def physicalHistory : PhysicalHistory (restriction P.base (targetOpen P) (targetCompact P)) (nativeStage P).Y :=
  OriginalNativeHSBaseOpenNativeStage.physicalHistory P.history (targetOpen P) (targetCompact P)

private abbrev localHistory (i : P.ι) :=
  OriginalNativeHSBaseOpenWindows.history P.window (targetInclusion P) (targetInclusion_open P) i (P.stage.T i).2

private def sourceInclusion : (nativeStage P).Y ⟶ P.nativeStage.Y :=
  OriginalNativeHSBaseOpenNativeStage.sourceInclusion P.history (targetOpen P) (targetCompact P)

private theorem sourceInclusion_open : LocallyRingedSpace.IsOpenImmersion (sourceInclusion P).hom.left :=
  inclusion_isOpenImmersion _ _ _

private theorem source_over (y : (nativeStage P).Y.obj.left) :
    P.nativeStage.q.hom.left.base ((sourceInclusion P).hom.left.base y) ∈
      range (neighbourhood P).inclusion.hom.left.base := by
  rw [(neighbourhood P).inclusion_range]
  change P.nativeStage.q.hom.left.base y.val ∈ targetOpen P
  have hy : P.history.projection.hom.left.base y.val ∈ targetOpen P := y.property
  exact P.history_projection ▸ hy

private def oldRepresentative (i : P.ι) (z : (nativeStage P).carrier i) : P.nativeStage.carrier i :=
  ⟨((localHistory P i).back z.val).val, z.property⟩

private theorem representative_point (i : P.ι) (z : (nativeStage P).carrier i) :
    (sourceInclusion P).hom.left.base (((nativeStage P).map i).hom.left.base z) =
      (P.nativeStage.map i).hom.left.base (oldRepresentative P i z) :=
  OriginalNativeHSBaseOpenCurrentReadout.window_source_point P.window P.nativeStage P.history P.history_projection
    (targetOpen P) (targetCompact P) i z

/-- EVERY whole current cosupport value, on the SAME retained original prefix. -/
private theorem carrier_bound (i : P.ι) (z : (nativeStage P).carrier i)
    (hz : z.val ∈ rcos (record P) (stage P).T i) :
    rvalue P.invariant.toResolutionInvariant (record P) (stage P).T i z.val ≤ level P := by
  have hCos := (OriginalNativeHSBaseOpenCurrentReadout.cosupp_iff P.window (targetInclusion P)
    (targetInclusion_open P) P.rawRecord P.native P.exponent P.positive P.invariant.toResolutionInvariant
    i (P.stage.T i).2 (P.stage.canonical i) z.val).mp hz
  have hValue := OriginalNativeHSBaseOpenCurrentReadout.value_eq P.window (targetInclusion P)
    (targetInclusion_open P) P.rawRecord P.native P.exponent P.positive P.invariant.toResolutionInvariant
    i (P.stage.T i).2 (P.stage.canonical i) z.val hz
  have hOver := source_over P (((nativeStage P).map i).hom.left.base z)
  have hOver' : P.nativeStage.q.hom.left.base ((P.nativeStage.map i).hom.left.base (oldRepresentative P i z)) ∈
      range (neighbourhood P).inclusion.hom.left.base :=
    congrArg P.nativeStage.q.hom.left.base (representative_point P i z) ▸ hOver
  exact hValue.trans_le (OriginalNativeShadowUniformBound.uniform_window_bound P.window (chosen P) P.invariant
    P.stage P.nativeStage (domains P) (initialClass P) P.nativeStage.q
    P.nativeStage.isSingularCentreModification.isProperMap P.compact P.compact_isCompact
    (threshold P) (threshold_closed P) (threshold_trace P) P.shadowCover P.shadowNonempty
    i (oldRepresentative P i z) hOver' hCos)

/-- Bound on EVERY AMBIENT cosupport point, with carrier incidence DERIVED. -/
theorem uniform_bound (i : P.ι) (y : ((stage P).T i).1) (hy : y ∈ rcos (record P) (stage P).T i) :
    rvalue P.invariant.toResolutionInvariant (record P) (stage P).T i y ≤ level P := by
  have hp := OriginalNativeCurrentHSReadout.chosen_presentation (window P) (rawRecord P) P.exponent
    (native_record P) P.positive P.invariant.toResolutionInvariant i ((stage P).T i).2 ((stage P).canonical i)
  have hCarrier : y ∈ (nativeStage P).carrier i := by
    rw [(nativeStage P).carrier_eq i]
    exact (hp).1 hy
  exact carrier_bound P i ⟨y, hCarrier⟩ hy

theorem maximum_attained : ∃ i, ∃ z : (nativeStage P).carrier i,
    z.val ∈ rcos (record P) (stage P).T i ∧
    rvalue P.invariant.toResolutionInvariant (record P) (stage P).T i z.val = level P ∧
    P.nativeStage.q.hom.left.base ((sourceInclusion P).hom.left.base (((nativeStage P).map i).hom.left.base z)) ∈ P.compact := by
  obtain ⟨i, c, hca, hc, hv, hOver⟩ := OriginalNativeShadowUniformBound.maximizing_window
    P.window (chosen P) P.invariant P.stage P.nativeStage (domains P) (initialClass P) P.nativeStage.q
    P.nativeStage.isSingularCentreModification.isProperMap P.compact P.compact_isCompact
    (threshold P) (threshold_closed P) (threshold_trace P) P.shadowCover P.shadowNonempty
  have hU : P.nativeStage.q.hom.left.base ((P.nativeStage.map i).hom.left.base c) ∈ targetOpen P :=
    (Set.ext_iff.mp (neighbourhood P).inclusion_range _).mp hOver
  obtain ⟨z, hTerminal, hPoint⟩ := OriginalNativeHSBaseOpenCurrentReadout.exists_window_preimage P.window
    P.nativeStage P.history P.history_projection (targetOpen P) (targetCompact P) i c hU
  have hCos : z.val ∈ rcos (record P) (stage P).T i :=
    (OriginalNativeHSBaseOpenCurrentReadout.cosupp_iff P.window (targetInclusion P) (targetInclusion_open P)
      P.rawRecord P.native P.exponent P.positive P.invariant.toResolutionInvariant
      i (P.stage.T i).2 (P.stage.canonical i) z.val).mpr (hTerminal.symm ▸ hc)
  have hValue := OriginalNativeHSBaseOpenCurrentReadout.value_eq P.window (targetInclusion P)
    (targetInclusion_open P) P.rawRecord P.native P.exponent P.positive P.invariant.toResolutionInvariant
    i (P.stage.T i).2 (P.stage.canonical i) z.val hCos
  refine ⟨i, z, hCos, hValue.trans ((congrArg (P.invariant.toResolutionInvariant.inv (chosen P i) (P.stage.T i).2)
    hTerminal).trans hv), ?_⟩
  have hMem := (OriginalNativeShadowUniformBound.anchor_mem P.window (chosen P) P.invariant P.stage P.nativeStage
    (domains P) (initialClass P) P.nativeStage.q P.nativeStage.isSingularCentreModification.isProperMap
    P.compact P.compact_isCompact (threshold P) (threshold_closed P) (threshold_trace P) P.shadowCover P.shadowNonempty).2
  have hOld : P.nativeStage.q.hom.left.base ((P.nativeStage.map i).hom.left.base c) ∈ P.compact :=
    (congrArg P.nativeStage.q.hom.left.base hca).symm ▸ hMem
  exact (congrArg P.nativeStage.q.hom.left.base hPoint).symm ▸ hOld

/-- WHOLE new literal threshold is covered AFTER the one proper-fibre shrink. -/
theorem threshold_covered : originalSingularHSThreshold (nativeStage P).Y P.profile ⊆
    ⋃ i, range (((nativeStage P).map i).hom.left.base) := by
  intro y hy
  have hOld : (sourceInclusion P).hom.left.base y ∈ threshold P :=
    (Set.ext_iff.mp (OriginalNativeHSThresholdIsomorphism.threshold_preimage_openImmersion P.profile
      (sourceInclusion P) (sourceInclusion_open P)) y).mpr hy
  have hDomain := (OriginalNativeShadowUniformBound.uniform_native_bound P.window (chosen P) P.invariant
    P.stage P.nativeStage (domains P) (initialClass P) P.nativeStage.q
    P.nativeStage.isSingularCentreModification.isProperMap P.compact P.compact_isCompact
    (threshold P) (threshold_closed P) (threshold_trace P) P.shadowCover P.shadowNonempty
    ((sourceInclusion P).hom.left.base y) hOld (source_over P y)).1
  obtain ⟨i, c, hcy, _hc⟩ := hDomain
  have hU : P.nativeStage.q.hom.left.base ((P.nativeStage.map i).hom.left.base c) ∈ targetOpen P := by
    have hOver := source_over P y
    rw [(neighbourhood P).inclusion_range] at hOver
    exact (congrArg P.nativeStage.q.hom.left.base hcy).symm ▸ hOver
  obtain ⟨z, _hTerminal, hPoint⟩ := OriginalNativeHSBaseOpenCurrentReadout.exists_window_preimage P.window
    P.nativeStage P.history P.history_projection (targetOpen P) (targetCompact P) i c hU
  exact mem_iUnion.mpr ⟨i, z, (sourceInclusion_open P).base_open.injective (hPoint.trans hcy)⟩

theorem greatest : IsGreatest (gfootValues P.invariant.toResolutionInvariant (record P) (fun _ => univ) (stage P).T) (level P) := by
  obtain ⟨i, z, hz, hv, _hK⟩ := maximum_attained P
  refine ⟨mem_iUnion.mpr ⟨i, z.val, ⟨hz, mem_univ _⟩, hv⟩, ?_⟩
  rintro v hv
  obtain ⟨j, y, hy, rfl⟩ := mem_iUnion.mp hv
  exact uniform_bound P j y hy.1

theorem common_mark (i j : P.ι) : (record P i).d = (record P j).d := P.commonMark i j

theorem history_projection : (physicalHistory P).projection = (nativeStage P).q := rfl

theorem physical_length : (physicalHistory P).length = P.history.length :=
  OriginalNativePhysicalHistoryRestriction.length_restrict P.history (targetOpen P) (targetCompact P)

def compact : Set (restriction P.base (targetOpen P) (targetCompact P)).obj.left :=
  (targetInclusion P).hom.left.base ⁻¹' P.compact

theorem compact_isCompact : IsCompact (compact P) := (neighbourhood P).shadow_compact P.compact_isCompact

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSUniformRestrictedStage
