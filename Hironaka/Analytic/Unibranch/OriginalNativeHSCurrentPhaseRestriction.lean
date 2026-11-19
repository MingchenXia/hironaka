import Hironaka.Analytic.Unibranch.OriginalNativeHSPrescribedFibreShrink
import Hironaka.Analytic.Unibranch.OriginalNativeHSOuterEndpointRange
import Hironaka.Analytic.Unibranch.OriginalNativeHSShadowOuterRun
import Hironaka.Analytic.Unibranch.OriginalNativeHSFactoryTerminalFrame
import Hironaka.Analytic.Unibranch.OriginalNativePrescribedTerminalPhaseComparison

/-! The SAME actual phase and SAME computed next prescribed endpoint.
Blueprint FIRST: original-native-hs-current-phase-restriction.tex.
No future comparison, chosen phase domain or smooth-map properness input. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentPhaseRestriction
noncomputable section
open SourceReducedComplexSpace OriginalNativeHSOuterHistory OriginalNativeHSShadowOuterState
  OriginalRelativelyCompactRestriction Hironaka
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaG11VanishingWindows
  HironakaG11VanishingPrincipalization HironakaG11CompatibleCanonicalTowers
  MarkedIdeals HironakaActualPowerBoundaryExponents OriginalIntrinsicHSSuperlevels
  HironakaG11PresReduction

private def nativeIsoOfRange {A B D : SourceReducedComplexSpace} (f : A ⟶ D) (g : B ⟶ D)
    (hf : LocallyRingedSpace.IsOpenImmersion f.hom.left)
    (hg : LocallyRingedSpace.IsOpenImmersion g.hom.left)
    (hr : range f.hom.left.base = range g.hom.left.base) : A ≅ B := by
  let := hf
  let := hg
  let e := HironakaEmbeddedNativeMorphism.openImmersionIsoOfRangeEq f.hom.left g.hom.left hr
  have hs : e.hom ≫ g.hom.left = f.hom.left :=
    HironakaEmbeddedNativeMorphism.openImmersionIsoOfRangeEq_hom_fac _ _ hr
  have hp : e.hom ≫ B.obj.hom = A.obj.hom := by
    rw [← Over.w g.hom,← Category.assoc,hs]
    exact Over.w f.hom
  exact ObjectProperty.isoMk sourceReducedComplexSpaceProperty (Over.isoMk e hp)

private theorem nativeIsoOfRange_square {A B D : SourceReducedComplexSpace} (f : A ⟶ D) (g : B ⟶ D)
    (hf : LocallyRingedSpace.IsOpenImmersion f.hom.left)
    (hg : LocallyRingedSpace.IsOpenImmersion g.hom.left)
    (hr : range f.hom.left.base = range g.hom.left.base) :
    (nativeIsoOfRange f g hf hg hr).hom ≫ g = f := by
  let := hf
  let := hg
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact HironakaEmbeddedNativeMorphism.openImmersionIsoOfRangeEq_hom_fac _ _ hr

variable {X : SourceReducedComplexSpace} {K : Set X.obj.left}
  (S : State X K) (W : Opens X.obj.left) (hW : IsCompact (closure (W : Set X.obj.left)))
  (hRange : closure (W : Set X.obj.left) ⊆ range S.inclusion.hom.left.base)
  (hContains : K ⊆ W) (hK : IsCompact K) (hne : (singularShadow S).Nonempty)
  (E : Opens X.obj.left) (hExtra : K ⊆ E)

include hne in
private theorem phaseNonempty : (shadow S ∩ intrinsicSingularLocus S.source.obj).Nonempty := by
  simpa only [singularShadow,inter_comm] using hne

private abbrev nextState := OriginalNativeHSShadowOuterRun.next S hK hne
private abbrev oldEndpoint := OriginalNativeHSCurrentOverlap.endpoint S W hW hRange
private abbrev oldInclusion := OriginalNativeHSCurrentOverlap.inclusion S W hW hRange
private abbrev original : S.source ⟶ X := S.history.projection ≫ S.inclusion
local notation "SF" => OriginalNativeHSShadowPhaseFactory.source S.source (shadow S)
  (shadow_compact S hK) (phaseNonempty S hne)
local notation "jF" => OriginalNativeHSShadowPhaseFactory.baseInclusion S.source (shadow S)
  (shadow_compact S hK) (phaseNonempty S hne)
local notation "hjF" => OriginalNativeHSShadowPhaseFactory.baseInclusion_isOpenImmersion S.source (shadow S)
  (shadow_compact S hK) (phaseNonempty S hne)
local notation "hF" => OriginalNativeHSShadowPhaseFactory.history S.source (shadow S)
  (shadow_compact S hK) (phaseNonempty S hne)
local notation "oldJ" => OriginalNativeHSOuterSuccessor.oldInclusion S.history
  (baseShadow S) (baseShadow_compact S hK) hne

private def guard : Opens S.source.obj.left :=
  ⟨range (jF).hom.left.base ∩ range (oldJ).hom.left.base,
    (hjF).base_open.isOpen_range.inter
      (OriginalNativeHSOuterEndpointRange.oldInclusion_isOpenImmersion S.history
        (baseShadow S) (baseShadow_compact S hK) hne).base_open.isOpen_range⟩

private theorem guard_shadow : shadow S ⊆ guard S hK hne := by
  intro y hy
  exact ⟨OriginalNativeHSShadowPhaseFactory.compact_retained S.source (shadow S)
    (shadow_compact S hK) (phaseNonempty S hne) hy,
    OriginalNativeHSOuterSuccessor.oldShadow_retained S.history (baseShadow S)
      (baseShadow_compact S hK) hne hy⟩

private def goodOpen : Opens (oldEndpoint S W hW hRange).obj.left :=
  ⟨(oldInclusion S W hW hRange).hom.left.base ⁻¹' (guard S hK hne : Set S.source.obj.left),
    (guard S hK hne).isOpen.preimage (oldInclusion S W hW hRange).hom.left.base.hom.continuous⟩

private theorem ownCompact_good : OriginalNativeHSPrescribedFibreShrink.compact S W hW hRange ⊆
    goodOpen S W hW hRange hK hne := by
  intro z hz
  apply guard_shadow S hK hne
  have hs := congrArg (fun f : oldEndpoint S W hW hRange ⟶ X => f.hom.left.base z)
    (OriginalNativePrescribedOpenHistory.projection_square S.inclusion S.inclusion_isOpenImmersion W hW hRange S.history)
  exact (congrArg (fun x : X.obj.left => x ∈ K) hs).mp hz

private def extraOpen : Opens X.obj.left :=
  ⟨range (nextState S hK hne).inclusion.hom.left.base ∩ E,
    (nextState S hK hne).inclusion_isOpenImmersion.base_open.isOpen_range.inter E.isOpen⟩
include hExtra in
private theorem extraContains : K ⊆ extraOpen S hK hne E :=
  fun _ hx => ⟨(nextState S hK hne).contains hx,hExtra hx⟩

local notation "G" => goodOpen S W hW hRange hK hne
local notation "hG" => ownCompact_good S W hW hRange hK hne
local notation "ex" => extraOpen S hK hne E
local notation "hEx" => extraContains S hK hne E hExtra

def openSet := OriginalNativeHSPrescribedFibreShrink.openSet S W hW hRange hContains hK (G) (hG) (ex) (hEx)
theorem compactClosure : IsCompact (closure (openSet S W hW hRange hContains hK hne E hExtra : Set X.obj.left)) :=
  OriginalNativeHSPrescribedFibreShrink.compactClosure S W hW hRange hContains hK (G) (hG) (ex) (hEx)
theorem contains : K ⊆ openSet S W hW hRange hContains hK hne E hExtra :=
  OriginalNativeHSPrescribedFibreShrink.contains S W hW hRange hContains hK (G) (hG) (ex) (hEx)
theorem closure_subset_old : closure (openSet S W hW hRange hContains hK hne E hExtra : Set X.obj.left) ⊆ W :=
  OriginalNativeHSPrescribedFibreShrink.closure_subset_old S W hW hRange hContains hK (G) (hG) (ex) (hEx)
theorem closure_subset_extra : closure (openSet S W hW hRange hContains hK hne E hExtra : Set X.obj.left) ⊆ E :=
  fun _ hx => (OriginalNativeHSPrescribedFibreShrink.closure_subset_extra S W hW hRange hContains hK (G) (hG) (ex) (hEx) hx).2
theorem closure_nextRange : closure (openSet S W hW hRange hContains hK hne E hExtra : Set X.obj.left) ⊆
    range (nextState S hK hne).inclusion.hom.left.base :=
  fun _ hx => (OriginalNativeHSPrescribedFibreShrink.closure_subset_extra S W hW hRange hContains hK (G) (hG) (ex) (hEx) hx).1

def currentOpen := OriginalNativeHSPrescribedFibreShrink.currentOpen S W hW hRange hContains hK (G) (hG) (ex) (hEx)
theorem currentOpen_compactClosure : IsCompact (closure (currentOpen S W hW hRange hContains hK hne E hExtra : Set S.source.obj.left)) :=
  OriginalNativeHSPrescribedFibreShrink.currentOpen_compactClosure S W hW hRange hContains hK (G) (hG) (ex) (hEx)
theorem currentOpen_factoryRange : closure (currentOpen S W hW hRange hContains hK hne E hExtra : Set S.source.obj.left) ⊆
    range (jF).hom.left.base := by
  intro y hy
  obtain ⟨z,hz,rfl⟩ := OriginalNativeHSPrescribedFibreShrink.currentOpen_closure_in_good S W hW hRange hContains hK (G) (hG) (ex) (hEx) hy
  exact hz.1
theorem currentOpen_oldRange : closure (currentOpen S W hW hRange hContains hK hne E hExtra : Set S.source.obj.left) ⊆
    range (oldJ).hom.left.base := by
  intro y hy
  obtain ⟨z,hz,rfl⟩ := OriginalNativeHSPrescribedFibreShrink.currentOpen_closure_in_good S W hW hRange hContains hK (G) (hG) (ex) (hEx) hy
  exact hz.2
theorem currentOpen_shadow : shadow S ⊆ currentOpen S W hW hRange hContains hK hne E hExtra :=
  OriginalNativeHSPrescribedFibreShrink.currentOpen_shadow S W hW hRange hContains hK (G) (hG) (ex) (hEx)

local notation "V" => openSet S W hW hRange hContains hK hne E hExtra
local notation "hV" => compactClosure S W hW hRange hContains hK hne E hExtra
local notation "vNext" => closure_nextRange S W hW hRange hContains hK hne E hExtra
local notation "Q" => currentOpen S W hW hRange hContains hK hne E hExtra
local notation "hQ" => currentOpen_compactClosure S W hW hRange hContains hK hne E hExtra
local notation "qF" => currentOpen_factoryRange S W hW hRange hContains hK hne E hExtra
local notation "wF" => OriginalNativeHSFactoryTerminalFrame.window S.source (shadow S) (shadow_compact S hK) (phaseNonempty S hne)
local notation "rF" => OriginalNativeHSFactoryTerminalFrame.rawRecord S.source (shadow S) (shadow_compact S hK) (phaseNonempty S hne)
local notation "HF" => OriginalNativeHSFactoryTerminalFrame.profile S.source (shadow S) (shadow_compact S hK) (phaseNonempty S hne)
local notation "nF" => OriginalNativeHSFactoryTerminalFrame.native_record S.source (shadow S) (shadow_compact S hK) (phaseNonempty S hne)
local notation "eF" => OriginalNativeHSFactoryTerminalFrame.exponent S.source (shadow S) (shadow_compact S hK) (phaseNonempty S hne)
local notation "heF" => OriginalNativeHSFactoryTerminalFrame.positive S.source (shadow S) (shadow_compact S hK) (phaseNonempty S hne)
local notation "sF" => OriginalNativeHSFactoryTerminalFrame.stage S.source (shadow S) (shadow_compact S hK) (phaseNonempty S hne)
local notation "xF" => OriginalNativeHSFactoryTerminalFrame.nativeStage S.source (shadow S) (shadow_compact S hK) (phaseNonempty S hne)
local notation "hProj" => OriginalNativeHSFactoryTerminalFrame.history_projection S.source (shadow S) (shadow_compact S hK) (phaseNonempty S hne)

def phaseWindow := OriginalNativePrescribedTerminalPhaseComparison.window (jF) (hjF) (Q) (hQ) (qF) (wF)
def phaseRawRecord := OriginalNativePrescribedTerminalPhaseComparison.rawRecord (jF) (hjF) (Q) (hQ) (qF) (wF) (rF)
theorem phase_native_record
    (i : (OriginalNativeHSShadowPhaseFactory.finalInput S.source (shadow S)
      (shadow_compact S hK) (phaseNonempty S hne)).ι) :
    IsNativeWindowRecord (phaseWindow S W hW hRange hContains hK hne E hExtra i)
      (phaseRawRecord S W hW hRange hContains hK hne E hExtra i) (HF) :=
  OriginalNativePrescribedTerminalPhaseComparison.native_record
    (jF) (hjF) (Q) (hQ) (qF) (wF) (rF) (HF) (nF) i
def phaseStage := OriginalNativePrescribedTerminalPhaseComparison.stage (jF) (hjF) (Q) (hQ) (qF)
  (wF) (rF) (HF) (nF) (eF) (heF) (sF)
def phaseNativeStage := OriginalNativePrescribedTerminalPhaseComparison.nativeStage (jF) (hjF) (Q) (hQ) (qF)
  (wF) (rF) (HF) (nF) (eF) (heF) (sF) (xF) (hF) (hProj)
def phase_history := OriginalNativePrescribedOpenHistory.history (jF) (hjF) (Q) (hQ) (qF) (hF)
theorem phase_projection_history : (phase_history S W hW hRange hContains hK hne E hExtra).projection=
    (phaseNativeStage S W hW hRange hContains hK hne E hExtra).q :=
  (OriginalNativePrescribedTerminalPhaseComparison.projection_history (jF) (hjF) (Q) (hQ) (qF)
    (wF) (rF) (HF) (nF) (eF) (heF) (sF) (xF) (hF) (hProj)).symm
theorem phase_terminal
    (i : (OriginalNativeHSShadowPhaseFactory.finalInput S.source (shadow S)
      (shadow_compact S hK) (phaseNonempty S hne)).ι) :
    MarkedIdeals.MarkedIdeal.IsGeoResolution
      (powerMarked (phaseRawRecord S W hW hRange hContains hK hne E hExtra i) ((eF) i))
      (((phaseStage S W hW hRange hContains hK hne E hExtra).T i).2) :=
  OriginalNativePrescribedTerminalPhaseComparison.terminal (jF) (hjF) (Q) (hQ) (qF)
    (wF) (rF) (HF) (nF) (eF) (heF) (sF)
    (OriginalNativeHSFactoryTerminalFrame.terminal S.source (shadow S) (shadow_compact S hK) (phaseNonempty S hne)) i
theorem phase_threshold_covered : originalSingularHSThreshold (restriction S.source (Q) (hQ)) (HF) ⊆
    ⋃i,range (phaseWindow S W hW hRange hContains hK hne E hExtra i).toLocalEmbedding.toPoint :=
  OriginalNativePrescribedTerminalPhaseComparison.threshold_covered
  (jF) (hjF) (Q) (hQ) (qF) (wF) (HF)
  (OriginalNativeHSFactoryTerminalFrame.threshold_covered S.source (shadow S) (shadow_compact S hK) (phaseNonempty S hne))
theorem phase_off_threshold : IsIsoOver (phaseNativeStage S W hW hRange hContains hK hne E hExtra).q
    (originalSingularHSThreshold (restriction S.source (Q) (hQ)) (HF))ᶜ :=
  OriginalNativePrescribedTerminalPhaseComparison.off_threshold
  (jF) (hjF) (Q) (hQ) (qF) (wF) (rF) (HF) (nF) (eF) (heF) (sF) (xF) (hF) (hProj)
  (OriginalNativeHSFactoryTerminalFrame.off_threshold S.source (shadow S) (shadow_compact S hK) (phaseNonempty S hne))

def phaseInclusion : (phaseNativeStage S W hW hRange hContains hK hne E hExtra).Y ⟶ (SF) :=
  OriginalNativePrescribedOpenHistory.sourceInclusion (jF) (hjF) (Q) (hQ) (qF) (hF)
theorem phaseInclusion_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion
    (phaseInclusion S W hW hRange hContains hK hne E hExtra).hom.left :=
  OriginalNativePrescribedOpenHistory.sourceInclusion_isOpenImmersion (jF) (hjF) (Q) (hQ) (qF) (hF)
theorem phaseInclusion_range : range (phaseInclusion S W hW hRange hContains hK hne E hExtra).hom.left.base =
    ((hF).projection ≫ (jF)).hom.left.base ⁻¹' (Q : Set S.source.obj.left) := by
  change range (Subtype.val : preimageOpen (OriginalNativePrescribedOpenHistory.pullbackOpen (jF) (Q))
    (hF).projection → (SF).obj.left)=_
  rw [Subtype.range_coe]
  rfl
theorem phase_projection_square : (phaseNativeStage S W hW hRange hContains hK hne E hExtra).q ≫
    inclusion S.source (Q) (hQ) =
    phaseInclusion S W hW hRange hContains hK hne E hExtra ≫ (hF).projection ≫ (jF) :=
  OriginalNativePrescribedTerminalPhaseComparison.projection_square (jF) (hjF) (Q) (hQ) (qF)
    (wF) (rF) (HF) (nF) (eF) (heF) (sF) (xF) (hF) (hProj)

private abbrev nextEndpoint := OriginalNativeHSCurrentOverlap.endpoint (nextState S hK hne) (V) (hV) (vNext)
private abbrev nextInclusion := OriginalNativeHSCurrentOverlap.inclusion (nextState S hK hne) (V) (hV) (vNext)
private abbrev nextHistory := OriginalNativeHSCurrentOverlap.history (nextState S hK hne) (V) (hV) (vNext)
private abbrev nextOriginal : (nextState S hK hne).source ⟶ X :=
  (nextState S hK hne).history.projection ≫ (nextState S hK hne).inclusion
private abbrev factoryOriginal : (SF) ⟶ S.source := (hF).projection ≫ (jF)
private abbrev actualNextInclusion := OriginalNativeHSOuterEndpointRange.endpointInclusion S.history
  (baseShadow S) (baseShadow_compact S hK) hne
private def wholeInclusion : nextEndpoint S W hW hRange hContains hK hne E hExtra ⟶ (SF) :=
  nextInclusion S W hW hRange hContains hK hne E hExtra ≫ actualNextInclusion S hK hne
private theorem wholeInclusion_open : LocallyRingedSpace.IsOpenImmersion
    (wholeInclusion S W hW hRange hContains hK hne E hExtra).hom.left :=
  @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ _
    (OriginalNativePrescribedOpenHistory.sourceInclusion_isOpenImmersion
      (nextState S hK hne).inclusion (nextState S hK hne).inclusion_isOpenImmersion (V) (hV) (vNext)
      (nextState S hK hne).history) _
    (OriginalNativeHSOuterEndpointRange.endpointInclusion_isOpenImmersion S.history
      (baseShadow S) (baseShadow_compact S hK) hne)

private theorem next_point (z : (nextState S hK hne).source.obj.left) :
    (nextOriginal S hK hne).hom.left.base z = (original S).hom.left.base
      ((factoryOriginal S hK hne).hom.left.base ((actualNextInclusion S hK hne).hom.left.base z)) :=
  congrArg (fun f : (nextState S hK hne).source ⟶ X => f.hom.left.base z)
    (OriginalNativeHSShadowOuterRun.next_projection_square S hK hne)

private theorem wholeInclusion_range : range (wholeInclusion S W hW hRange hContains hK hne E hExtra).hom.left.base =
    (factoryOriginal S hK hne).hom.left.base ⁻¹' (Q : Set S.source.obj.left) := by
  ext y
  constructor
  · rintro ⟨z,rfl⟩
    have hz := z.property
    change (nextOriginal S hK hne).hom.left.base z.val ∈ (V : Set X.obj.left) at hz
    change (original S).hom.left.base ((factoryOriginal S hK hne).hom.left.base
      ((actualNextInclusion S hK hne).hom.left.base z.val)) ∈ (V : Set X.obj.left)
    exact (congrArg (fun x : X.obj.left => x ∈ (V : Set X.obj.left)) (next_point S hK hne z.val)).mp hz
  · intro hy
    have hOld := currentOpen_oldRange S W hW hRange hContains hK hne E hExtra (subset_closure hy)
    have he := OriginalNativeHSOuterEndpointRange.endpoint_range S.history
      (baseShadow S) (baseShadow_compact S hK) hne
    obtain ⟨z,hz⟩ := (Set.ext_iff.mp he y).mpr hOld
    have hp : (nextOriginal S hK hne).hom.left.base z =
        (original S).hom.left.base ((factoryOriginal S hK hne).hom.left.base y) :=
      (next_point S hK hne z).trans (congrArg (fun u => (original S).hom.left.base
        ((factoryOriginal S hK hne).hom.left.base u)) hz)
    let u : (nextEndpoint S W hW hRange hContains hK hne E hExtra).obj.left :=
      ⟨z,(congrArg (fun x : X.obj.left => x ∈ (V : Set X.obj.left)) hp).mpr hy⟩
    exact ⟨u,hz⟩

def comparison : (phaseNativeStage S W hW hRange hContains hK hne E hExtra).Y ≅
    nextEndpoint S W hW hRange hContains hK hne E hExtra :=
  nativeIsoOfRange (phaseInclusion S W hW hRange hContains hK hne E hExtra)
    (wholeInclusion S W hW hRange hContains hK hne E hExtra)
    (phaseInclusion_isOpenImmersion S W hW hRange hContains hK hne E hExtra)
    (wholeInclusion_open S W hW hRange hContains hK hne E hExtra)
    ((phaseInclusion_range S W hW hRange hContains hK hne E hExtra).trans
      (wholeInclusion_range S W hW hRange hContains hK hne E hExtra).symm)
theorem comparison_square : (comparison S W hW hRange hContains hK hne E hExtra).hom ≫
    wholeInclusion S W hW hRange hContains hK hne E hExtra =
    phaseInclusion S W hW hRange hContains hK hne E hExtra :=
  nativeIsoOfRange_square _ _ _ _ _

theorem comparison_projection : (comparison S W hW hRange hContains hK hne E hExtra).hom ≫
    (nextHistory S W hW hRange hContains hK hne E hExtra).projection =
    (phaseNativeStage S W hW hRange hContains hK hne E hExtra).q ≫
      (OriginalNativeHSCurrentOverlap.history S (V) (hV)
        (OriginalNativeHSPrescribedFibreShrink.closureRange S W hW hRange hContains hK (G) (hG) (ex) (hEx))).projection := by
  apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
  intro z
  apply (inclusion_isOpenImmersion X (V) (hV)).base_open.injective
  let c := (comparison S W hW hRange hContains hK hne E hExtra).hom.hom.left.base z
  have hn := congrArg (fun f : nextEndpoint S W hW hRange hContains hK hne E hExtra ⟶ X => f.hom.left.base c)
    (OriginalNativePrescribedOpenHistory.projection_square (nextState S hK hne).inclusion
      (nextState S hK hne).inclusion_isOpenImmersion (V) (hV) (vNext) (nextState S hK hne).history)
  have hc := congrArg (fun f : (phaseNativeStage S W hW hRange hContains hK hne E hExtra).Y ⟶ (SF) => f.hom.left.base z)
    (comparison_square S W hW hRange hContains hK hne E hExtra)
  have hp := congrArg (fun f : (phaseNativeStage S W hW hRange hContains hK hne E hExtra).Y ⟶ S.source => f.hom.left.base z)
    (phase_projection_square S W hW hRange hContains hK hne E hExtra)
  have ho := congrArg (fun f : OriginalNativeHSCurrentOverlap.endpoint S (V) (hV)
      (OriginalNativeHSPrescribedFibreShrink.closureRange S W hW hRange hContains hK (G) (hG) (ex) (hEx)) ⟶ X =>
      f.hom.left.base ((phaseNativeStage S W hW hRange hContains hK hne E hExtra).q.hom.left.base z))
    (OriginalNativePrescribedOpenHistory.projection_square S.inclusion S.inclusion_isOpenImmersion
      (V) (hV) (OriginalNativeHSPrescribedFibreShrink.closureRange S W hW hRange hContains hK (G) (hG) (ex) (hEx)) S.history)
  exact hn.trans ((next_point S hK hne c.val).trans
    ((congrArg (fun u => (original S).hom.left.base ((factoryOriginal S hK hne).hom.left.base u)) hc).trans
      ((congrArg (original S).hom.left.base hp).symm.trans ho.symm)))

theorem comparison_scalar : (comparison S W hW hRange hContains hK hne E hExtra).hom.hom.left ≫
    (nextEndpoint S W hW hRange hContains hK hne E hExtra).obj.hom =
    (phaseNativeStage S W hW hRange hContains hK hne E hExtra).Y.obj.hom :=
  Over.w (comparison S W hW hRange hContains hK hne E hExtra).hom.hom

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentPhaseRestriction
