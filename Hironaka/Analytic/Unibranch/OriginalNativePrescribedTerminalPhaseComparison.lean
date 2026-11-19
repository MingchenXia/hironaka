import Hironaka.Analytic.Unibranch.OriginalNativeHSBaseOpenNativeStage
import Hironaka.Analytic.Unibranch.OriginalNativeStageBaseIso
import Hironaka.Analytic.Unibranch.OriginalNativePrescribedOpenHistory
import Hironaka.Analytic.Unibranch.OriginalNativeTerminalPhaseGluing
import Hironaka.Analytic.Unibranch.OriginalNativeHSInitialThresholdCover
import Hironaka.MarkedIdeal.MarkedIdealOpenBiholomorphism

/-! Concrete independent terminal phases on the LITERAL same prescribed
native X|U. Blueprint FIRST: original-native-prescribed-terminal-phase-comparison.tex.
No endpoint map, common clock, or future phase supplier is input. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativePrescribedTerminalPhaseComparison
noncomputable section
open Hironaka Hironaka.BlowupSequences
  Hironaka SourceReducedComplexSpace HironakaG11VanishingWindows
  HironakaG11VanishingPrincipalization HironakaG11StrictTransformTowers HironakaG11PresReduction
  HironakaG11CompatibleCanonicalTowers BlowupTowers ResolutionInvariantSeq MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaActualPowerBoundaryExponents CanonicalCentres OriginalNativeHSOuterHistory
  OriginalIntrinsicHSSuperlevels OriginalRelativelyCompactRestriction

section OnePhase
variable {X B : SourceReducedComplexSpace} {n : ℕ} {ι : Type}
  (j : B ⟶ X) (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left)
  (U : Opens X.obj.left) (hU : IsCompact (closure (U : Set X.obj.left)))
  (hRange : closure (U : Set X.obj.left) ⊆ range j.hom.left.base)
  (w : ι → DimEmbedding B n)
local notation "UB" => OriginalNativePrescribedOpenHistory.pullbackOpen j U
local notation "hUB" => OriginalNativePrescribedOpenHistory.pullbackOpen_compactClosure j hj U hU hRange
local notation "inc" => OriginalNativePrescribedOpenHistory.baseInclusion j hj U hU hRange
local notation "hinc" => inclusion_isOpenImmersion B (UB) (hUB)
local notation "E" => OriginalNativePrescribedOpenHistory.comparison j hj U hU hRange
local notation "wR" => OriginalNativeHSBaseOpenWindows.window w (inc) (hinc)

/-- The actual coordinate window, with its derived full common-base native map. -/
def window : ι → DimEmbedding (restriction X U hU) n :=
  OriginalNativeStageBaseIso.window (wR) (E).symm

variable (raw : ∀i,MarkedIdeal n (Amb w i)) (H : ℕ → ℕ)
  (hRaw : ∀i,IsNativeWindowRecord (w i) (raw i) H)

def rawRecord : ∀i,MarkedIdeal n (Amb (window j hj U hU hRange w) i) :=
  OriginalNativeHSBaseOpenWindows.rawRecord w (inc) (hinc) raw

include hRaw in
theorem native_record (i : ι) :
    IsNativeWindowRecord (window j hj U hU hRange w i) (rawRecord j hj U hU hRange w raw i) H :=
  OriginalNativeStageBaseIso.native_record (wR) (E).symm
    (OriginalNativeHSBaseOpenWindows.rawRecord w (inc) (hinc) raw) H
    (OriginalNativeHSBaseOpenWindows.native_record w (inc) (hinc) raw hRaw) i

variable (e : ι → ℕ) (he : ∀i,1≤e i) {m : ℕ}
  (s : GStage (canonicalInvariant n) (fun i=>powerMarked (raw i) (e i)) (mapAdm w) m)
local notation "sR" => OriginalNativeHSBaseOpenStage.stage w (inc) (hinc) raw hRaw e he (canonicalInvariant n) s

def stage : GStage (canonicalInvariant n)
    (fun i=>powerMarked (rawRecord j hj U hU hRange w raw i) (e i))
    (mapAdm (window j hj U hU hRange w)) m :=
  OriginalNativeStageBaseIso.stage (wR) (E).symm (canonicalInvariant n)
    (OriginalNativeHSBaseOpenWindows.record w (inc) (hinc) raw e) (sR)

variable (xs : XStage w s.T) (h : PhysicalHistory B xs.Y) (hHistory : h.projection=xs.q)
local notation "xsR" => OriginalNativeHSBaseOpenNativeStage.compatibleNativeStage w (UB) (hUB)
  raw hRaw e he (canonicalInvariant n) s xs h hHistory

def nativeStage : XStage (window j hj U hU hRange w)
    (stage j hj U hU hRange w raw H hRaw e he s).T :=
  OriginalNativeStageBaseIso.nativeStage (wR) (E).symm (xsR)

theorem projection_history : (nativeStage j hj U hU hRange w raw H hRaw e he s xs h hHistory).q=
    (OriginalNativePrescribedOpenHistory.history j hj U hU hRange h).projection :=
  (OriginalNativePrescribedOpenHistory.projection_formula j hj U hU hRange h).symm

theorem projection_square :
    (nativeStage j hj U hU hRange w raw H hRaw e he s xs h hHistory).q ≫ inclusion X U hU =
      OriginalNativePrescribedOpenHistory.sourceInclusion j hj U hU hRange h ≫ xs.q ≫ j := by
  rw [projection_history]
  exact (OriginalNativePrescribedOpenHistory.projection_square j hj U hU hRange h).trans
    (congrArg (fun p => OriginalNativePrescribedOpenHistory.sourceInclusion j hj U hU hRange h ≫ p ≫ j) hHistory)

include hRaw he in
theorem terminal (hr : ∀i,IsGeoResolution (powerMarked (raw i) (e i)) (s.T i).2) (i : ι) :
    IsGeoResolution (powerMarked (rawRecord j hj U hU hRange w raw i) (e i))
      ((stage j hj U hU hRange w raw H hRaw e he s).T i).2 := by
  change IsGeoResolution (OriginalNativeHSBaseOpenWindows.record w (inc) (hinc) raw e i)
    (OriginalNativeHSBaseOpenWindows.history w (inc) (hinc) i (s.T i).2).tower
  rw [OriginalNativeHSBaseOpenWindows.record_eq_pullback w (inc) (hinc) raw hRaw e i]
  have hD := powerMarked_isInvDomain (raw i) (hRaw i).1 (he i)
  exact MarkedIdealOpenBiholomorphism.isGeoResolution_transport_restrict
    (OriginalNativeHSBaseOpenWindows.traceOpen w (inc) (hinc) i)
    (OriginalNativeHSBaseOpenWindows.baseEquiv w (inc) (hinc) i)
    hD.isWellFormed.isClosedSubmanifold_N hD.isWellFormed.isCoherent (hr i)

theorem threshold_covered
    (hCover : originalSingularHSThreshold B H ⊆ ⋃i,range (w i).toLocalEmbedding.toPoint) :
    originalSingularHSThreshold (restriction X U hU) H ⊆
      ⋃i,range (window j hj U hU hRange w i).toLocalEmbedding.toPoint :=
  OriginalNativeStageBaseIso.threshold_covered (wR) (E).symm H
    (OriginalNativeHSInitialThresholdCover.pullback_threshold_covered w H hCover (inc) (hinc))

include hRaw he hHistory in
theorem off_threshold (hOff : IsIsoOver xs.q (originalSingularHSThreshold B H)ᶜ) :
    IsIsoOver (nativeStage j hj U hU hRange w raw H hRaw e he s xs h hHistory).q
      (originalSingularHSThreshold (restriction X U hU) H)ᶜ := by
  have hOffH : IsIsoOver h.projection (originalSingularHSThreshold B H)ᶜ := hHistory.symm ▸ hOff
  have hRestricted : IsIsoOver (xsR).q
      (originalSingularHSThreshold (OriginalNativePrescribedOpenHistory.baseRestriction j hj U hU hRange) H)ᶜ := by
    change IsIsoOver (OriginalNativePhysicalHistoryRestriction.restrict h (UB) (hUB)).projection _
    rw [OriginalNativePhysicalHistoryRestriction.projection_restrict]
    exact OriginalNativeHSThresholdIsomorphism.isIsoOver_restrictionProjection_threshold_compl H
      h.projection h.singularModification.isProperMap (UB) (hUB) hOffH
  exact OriginalNativeStageBaseIso.off_threshold (wR) (E).symm (xsR) H hRestricted

end OnePhase

section TwoPhases
variable {X BT BS : SourceReducedComplexSpace} {n : ℕ} {ι κ : Type}
  (jT : BT ⟶ X) (jS : BS ⟶ X)
  (hjT : LocallyRingedSpace.IsOpenImmersion jT.hom.left)
  (hjS : LocallyRingedSpace.IsOpenImmersion jS.hom.left)
  (U : Opens X.obj.left) (hU : IsCompact (closure (U : Set X.obj.left)))
  (hRangeT : closure (U : Set X.obj.left) ⊆ range jT.hom.left.base)
  (hRangeS : closure (U : Set X.obj.left) ⊆ range jS.hom.left.base)
  (wT : ι → DimEmbedding BT n) (wS : κ → DimEmbedding BS n)
  (rawT : ∀i,MarkedIdeal n (Amb wT i)) (rawS : ∀j,MarkedIdeal n (Amb wS j))
  (H : ℕ → ℕ) (hRawT : ∀i,IsNativeWindowRecord (wT i) (rawT i) H)
  (hRawS : ∀j,IsNativeWindowRecord (wS j) (rawS j) H)
  (eT : ι → ℕ) (eS : κ → ℕ) (heT : ∀i,1≤eT i) (heS : ∀j,1≤eS j)
  {mT mS : ℕ}
  (sT : GStage (canonicalInvariant n) (fun i=>powerMarked (rawT i) (eT i)) (mapAdm wT) mT)
  (sS : GStage (canonicalInvariant n) (fun j=>powerMarked (rawS j) (eS j)) (mapAdm wS) mS)
  (xt : XStage wT sT.T) (xs : XStage wS sS.T)
  (hT : PhysicalHistory BT xt.Y) (hS : PhysicalHistory BS xs.Y)
  (hHistoryT : hT.projection=xt.q) (hHistoryS : hS.projection=xs.q)
local notation "wTC" => window jT hjT U hU hRangeT wT
local notation "wSC" => window jS hjS U hU hRangeS wS
local notation "rawTC" => rawRecord jT hjT U hU hRangeT wT rawT
local notation "rawSC" => rawRecord jS hjS U hU hRangeS wS rawS
local notation "sTC" => stage jT hjT U hU hRangeT wT rawT H hRawT eT heT sT
local notation "sSC" => stage jS hjS U hU hRangeS wS rawS H hRawS eS heS sS
local notation "NT" => nativeStage jT hjT U hU hRangeT wT rawT H hRawT eT heT sT xt hT hHistoryT
local notation "NS" => nativeStage jS hjS U hU hRangeS wS rawS H hRawS eS heS sS xs hS hHistoryS
local notation "qT" => PhysicalHistory.projection (OriginalNativePrescribedOpenHistory.history jT hjT U hU hRangeT hT)
local notation "qS" => PhysicalHistory.projection (OriginalNativePrescribedOpenHistory.history jS hjS U hU hRangeS hS)

/-- Native uniqueness is over the SAME literal prescribed base, with the
actual physical projections, independently of old ambient/physical clocks. -/
theorem maps_eq_over_prescribed_base (a b : (NS).Y ⟶ (NT).Y)
    (ha : a ≫ (qT)=(qS)) (hb : b ≫ (qT)=(qS)) : a=b := by
  have hpT := projection_history jT hjT U hU hRangeT wT rawT H hRawT eT heT sT xt hT hHistoryT
  have hpS := projection_history jS hjS U hU hRangeS wS rawS H hRawS eS heS sS xs hS hHistoryS
  apply OriginalNativeTerminalPhaseGluing.maps_eq_over_base
    (wTC) (wSC) (sTC).T (sSC).T (NT) (NS) a b
  · exact ((congrArg (fun q => a ≫ q) hpT).trans ha).trans hpS.symm
  · exact ((congrArg (fun q => b ≫ q) hpT).trans hb).trans hpS.symm

/-- The full original-X square follows from the actual prescribed square;
no properness of either composite into this larger X is asserted. -/
theorem original_square (F : (NS).Y ⟶ (NT).Y) (hF : F ≫ (qT)=(qS)) :
    F ≫ OriginalNativePrescribedOpenHistory.sourceInclusion jT hjT U hU hRangeT hT ≫ xt.q ≫ jT =
      OriginalNativePrescribedOpenHistory.sourceInclusion jS hjS U hU hRangeS hS ≫ xs.q ≫ jS := by
  have eqT : (qT) ≫ inclusion X U hU =
      OriginalNativePrescribedOpenHistory.sourceInclusion jT hjT U hU hRangeT hT ≫ xt.q ≫ jT :=
    (OriginalNativePrescribedOpenHistory.projection_square jT hjT U hU hRangeT hT).trans
      (congrArg (fun p => OriginalNativePrescribedOpenHistory.sourceInclusion jT hjT U hU hRangeT hT ≫ p ≫ jT) hHistoryT)
  have eqS : (qS) ≫ inclusion X U hU =
      OriginalNativePrescribedOpenHistory.sourceInclusion jS hjS U hU hRangeS hS ≫ xs.q ≫ jS :=
    (OriginalNativePrescribedOpenHistory.projection_square jS hjS U hU hRangeS hS).trans
      (congrArg (fun p => OriginalNativePrescribedOpenHistory.sourceInclusion jS hjS U hU hRangeS hS ≫ p ≫ jS) hHistoryS)
  exact (congrArg (fun p : (NT).Y ⟶ X => F ≫ p) eqT.symm).trans
    ((Category.assoc F (qT) (inclusion X U hU)).symm.trans
      ((congrArg (fun p : (NS).Y ⟶ restriction X U hU => p ≫ inclusion X U hU) hF).trans eqS))

variable
  (hrT : ∀i,IsGeoResolution (powerMarked (rawT i) (eT i)) (sT.T i).2)
  (hrS : ∀j,IsGeoResolution (powerMarked (rawS j) (eS j)) (sS.T j).2)
  (hCoverT : originalSingularHSThreshold BT H ⊆ ⋃i,range (wT i).toLocalEmbedding.toPoint)
  (hCoverS : originalSingularHSThreshold BS H ⊆ ⋃j,range (wS j).toLocalEmbedding.toPoint)
  (hOffT : IsIsoOver xt.q (originalSingularHSThreshold BT H)ᶜ)
  (hOffS : IsIsoOver xs.q (originalSingularHSThreshold BS H)ᶜ)

include hrT hrS hCoverT hCoverS hOffT hOffS in
/-- The endpoint iso is CONSTRUCTED from the two actual terminal phases;
its full square is on their literal prescribed physical projections. -/
theorem exists_comparison : ∃ F : (NS).Y ≅ (NT).Y, F.hom ≫ (qT)=(qS) := by
  obtain ⟨F,hF⟩ := OriginalNativeTerminalPhaseGluing.exists_global_comparison
    (wTC) (wSC) (rawTC) (rawSC) H
    (native_record jT hjT U hU hRangeT wT rawT H hRawT)
    (native_record jS hjS U hU hRangeS wS rawS H hRawS)
    eT eS heT heS (sTC).T (sSC).T (NT) (NS) (sTC).canonical (sSC).canonical
    (terminal jT hjT U hU hRangeT wT rawT H hRawT eT heT sT hrT)
    (terminal jS hjS U hU hRangeS wS rawS H hRawS eS heS sS hrS)
    (threshold_covered jT hjT U hU hRangeT wT H hCoverT)
    (threshold_covered jS hjS U hU hRangeS wS H hCoverS)
    (off_threshold jT hjT U hU hRangeT wT rawT H hRawT eT heT sT xt hT hHistoryT hOffT)
    (off_threshold jS hjS U hU hRangeS wS rawS H hRawS eS heS sS xs hS hHistoryS hOffS)
  refine ⟨F,?_⟩
  have hpT := projection_history jT hjT U hU hRangeT wT rawT H hRawT eT heT sT xt hT hHistoryT
  have hpS := projection_history jS hjS U hU hRangeS wS rawS H hRawS eS heS sS xs hS hHistoryS
  exact (congrArg (fun q => F.hom ≫ q) hpT).symm.trans (hF.trans hpS)

end TwoPhases
end
end Hironaka.Analytic.Unibranch.OriginalNativePrescribedTerminalPhaseComparison
