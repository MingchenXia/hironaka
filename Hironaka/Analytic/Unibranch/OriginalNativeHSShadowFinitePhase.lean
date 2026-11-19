import Hironaka.Analytic.Unibranch.OriginalNativeHSShadowFiniteRun
import Hironaka.Analytic.Unibranch.OriginalNativeHSEmptyStop

/-! The SAME finite successor run, its actual final whole-threshold shrink,
genuine composed base OI and actual finite physical history/full square.
Blueprint FIRST: original-native-hs-shadow-finite-phase.tex.
No endpoint supplier, compactcosupp, global clock or completed outer factory. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSShadowFinitePhase
noncomputable section
open Hironaka Hironaka.BlowupSequences
  Hironaka SourceReducedComplexSpace HironakaG11PresReduction
  HironakaG11VanishingWindows HironakaG11VanishingPrincipalization HironakaG11StrictTransformTowers
  HironakaG11CompatibleCanonicalTowers OriginalNativeHSOuterHistory
  HironakaIntrinsicComplexAnalyticRegularLocus OriginalIntrinsicHSSuperlevels
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  OriginalNativeHSUniformRestrictedStage OriginalNativeHSShadowFiniteRun HironakaG11InvBMClass HironakaG8LocalHistory

variable {n : ℕ} {Λ : Type} [LinearOrder Λ] [Nonempty Λ]

/-- Only the actual last successor's PRESENT data and its true empty-shadow witness. -/
def stopInput (P : Input n Λ) (hempty : afterShadow P = ∅) :
    OriginalNativeHSEmptyStop.Input n Λ where
  base := (neighbourhood P).source
  ι := P.ι
  window := OriginalNativeHSUniformRestrictedStage.window P
  rawRecord := OriginalNativeHSUniformRestrictedStage.rawRecord P
  profile := P.profile
  native := native_record P
  exponent := P.exponent
  positive := P.positive
  invariant := P.invariant.toResolutionInvariant
  clock := P.clock + 1
  stage := OriginalNativeHSShadowSuccessor.ambientStage P
  nativeStage := OriginalNativeHSShadowSuccessor.nativeStage P
  history := OriginalNativeHSShadowSuccessor.physicalHistory P
  history_projection := OriginalNativeHSShadowSuccessor.history_projection P
  compact := compact P
  compact_isCompact := compact_isCompact P
  shadowEmpty := hempty

/-- The actual source inclusion of the SAME present physical history's restriction. -/
def currentSourceInclusion (P : Input n Λ) : (nativeStage P).Y ⟶ P.nativeStage.Y :=
  OriginalNativeHSBaseOpenNativeStage.sourceInclusion P.history
    (neighbourhood P).openSet (neighbourhood P).compactClosure

theorem current_projection_square (P : Input n Λ) :
    (nativeStage P).q ≫ (neighbourhood P).inclusion = currentSourceInclusion P ≫ P.nativeStage.q :=
  (OriginalNativeHSBaseOpenNativeStage.projection_square P.history
    (neighbourhood P).openSet (neighbourhood P).compactClosure).trans
    (congrArg (fun a => currentSourceInclusion P ≫ a) P.history_projection)

namespace Run

def finalInput {P : Input n Λ} (r : OriginalNativeHSShadowFiniteRun.Run P) :
    OriginalNativeHSEmptyStop.Input n Λ :=
  stopInput r.terminalInput r.terminal_empty

theorem final_invariant_eq {P : Input n Λ} (r : OriginalNativeHSShadowFiniteRun.Run P) :
    (finalInput r).invariant = P.invariant.toResolutionInvariant := by
  exact congrArg (fun B : BMInvariant.{0,0} n
    (fun {Y} A A' => LocWPEquiv (X := Y) A A') n Λ => B.toResolutionInvariant) r.invariant_eq

def finalBase {P : Input n Λ} (r : OriginalNativeHSShadowFiniteRun.Run P) : SourceReducedComplexSpace :=
  (OriginalNativeHSEmptyStop.neighbourhood (finalInput r)).source

def finalWindow {P : Input n Λ} (r : OriginalNativeHSShadowFiniteRun.Run P) :=
  OriginalNativeHSEmptyStop.window (finalInput r)

def finalRawRecord {P : Input n Λ} (r : OriginalNativeHSShadowFiniteRun.Run P) :=
  OriginalNativeHSEmptyStop.rawRecord (finalInput r)

theorem final_native_record {P : Input n Λ} (r : OriginalNativeHSShadowFiniteRun.Run P)
    (i : (finalInput r).ι) : IsNativeWindowRecord (finalWindow r i) (finalRawRecord r i) P.profile := by
  have h := OriginalNativeHSEmptyStop.native_record (finalInput r) i
  exact r.profile_eq ▸ h

def finalRecord {P : Input n Λ} (r : OriginalNativeHSShadowFiniteRun.Run P) :=
  OriginalNativeHSEmptyStop.record (finalInput r)

def finalStage {P : Input n Λ} (r : OriginalNativeHSShadowFiniteRun.Run P) :=
  OriginalNativeHSEmptyStop.stage (finalInput r)

def finalNativeStage {P : Input n Λ} (r : OriginalNativeHSShadowFiniteRun.Run P) :=
  OriginalNativeHSEmptyStop.nativeStage (finalInput r)

def finalSource {P : Input n Λ} (r : OriginalNativeHSShadowFiniteRun.Run P) : SourceReducedComplexSpace :=
  (finalNativeStage r).Y

def history {P : Input n Λ} (r : OriginalNativeHSShadowFiniteRun.Run P) :
    PhysicalHistory (finalBase r) (finalSource r) :=
  OriginalNativeHSEmptyStop.physicalHistory (finalInput r)

theorem history_projection {P : Input n Λ} (r : OriginalNativeHSShadowFiniteRun.Run P) :
    (history r).projection = (finalNativeStage r).q :=
  OriginalNativeHSEmptyStop.history_projection (finalInput r)

theorem final_threshold_empty {P : Input n Λ} (r : OriginalNativeHSShadowFiniteRun.Run P) :
    originalSingularHSThreshold (finalSource r) P.profile = ∅ := by
  have h := OriginalNativeHSEmptyStop.threshold_empty (finalInput r)
  exact r.profile_eq ▸ h

theorem final_resolution {P : Input n Λ} (r : OriginalNativeHSShadowFiniteRun.Run P)
    (i : (finalInput r).ι) : IsGeoResolution (finalRecord r i) ((finalStage r).T i).2 :=
  OriginalNativeHSEmptyStop.resolution (finalInput r) i

theorem final_canonical {P : Input n Λ} (r : OriginalNativeHSShadowFiniteRun.Run P)
    (i : (finalInput r).ι) : ResolutionInvariantSpec.IsCanonical (finalRecord r i)
      (P.invariant.toResolutionInvariant.inv (finalRecord r i)) ((finalStage r).T i).2 := by
  have h := OriginalNativeHSEmptyStop.canonical (finalInput r) i
  exact final_invariant_eq r ▸ h

/-- The genuine composed native base OI, retaining every original compact point. -/
def baseInclusion : {P : Input n Λ} → (r : OriginalNativeHSShadowFiniteRun.Run P) → finalBase r ⟶ P.base
  | P, .stop _ _ => (OriginalNativeHSEmptyStop.neighbourhood (finalInput (.stop P _))).inclusion ≫
      (neighbourhood P).inclusion
  | P, .next _ _ tail => baseInclusion tail ≫ (neighbourhood P).inclusion

theorem baseInclusion_isOpenImmersion : {P : Input n Λ} → (r : OriginalNativeHSShadowFiniteRun.Run P) →
    LocallyRingedSpace.IsOpenImmersion (baseInclusion r).hom.left
  | P, .stop _ hempty => by
    exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _
      (OriginalNativeHSEmptyStop.neighbourhood (finalInput (.stop P hempty))).inclusion.hom.left
      (OriginalNativeHSEmptyStop.neighbourhood (finalInput (.stop P hempty))).inclusion_isOpenImmersion
      (neighbourhood P).inclusion.hom.left (neighbourhood P).inclusion_isOpenImmersion
  | P, .next _ hne tail => by
    exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _
      (baseInclusion tail).hom.left (baseInclusion_isOpenImmersion tail)
      (neighbourhood P).inclusion.hom.left (neighbourhood P).inclusion_isOpenImmersion

theorem compact_retained : {P : Input n Λ} → (r : OriginalNativeHSShadowFiniteRun.Run P) →
    P.compact ⊆ range (baseInclusion r).hom.left.base
  | P, .stop _ hempty => by
    intro x hx
    let u : (neighbourhood P).source.obj.left := ⟨x, (neighbourhood P).contains hx⟩
    have hu : u ∈ compact P := hx
    refine ⟨⟨u, (OriginalNativeHSEmptyStop.neighbourhood (finalInput (.stop P hempty))).contains hu⟩, rfl⟩
  | P, .next _ hne tail => by
    intro x hx
    let u : (neighbourhood P).source.obj.left := ⟨x, (neighbourhood P).contains hx⟩
    obtain ⟨v, hv⟩ := compact_retained tail (show u ∈ compact P from hx)
    exact ⟨v, congrArg (neighbourhood P).inclusion.hom.left.base hv⟩

/-- Actual phase morphism to the old current source, keeping every constructed arrow. -/
def phaseProjection : {P : Input n Λ} → (r : OriginalNativeHSShadowFiniteRun.Run P) →
    finalSource r ⟶ P.nativeStage.Y
  | P, .stop _ hempty => OriginalNativeHSEmptyStop.sourceInclusion (finalInput (.stop P hempty)) ≫
      (OriginalNativeHSShadowSuccessor.step P).projection ≫ currentSourceInclusion P
  | P, .next _ _ tail => phaseProjection tail ≫
      (OriginalNativeHSShadowSuccessor.step P).projection ≫ currentSourceInclusion P

private theorem paste_square {A B C D E F G : SourceReducedComplexSpace}
    (f : A ⟶ B) (j : B ⟶ C) (u : C ⟶ G) (a : A ⟶ D)
    (p : D ⟶ E) (b : E ⟶ C) (c : E ⟶ F) (q : F ⟶ G)
    (h0 : f ≫ j = a ≫ p ≫ b) (h1 : b ≫ u = c ≫ q) :
    f ≫ (j ≫ u) = (a ≫ p ≫ c) ≫ q := by
  calc
    f ≫ (j ≫ u) = (f ≫ j) ≫ u := (Category.assoc _ _ _).symm
    _ = (a ≫ p ≫ b) ≫ u := congrArg (fun t => t ≫ u) h0
    _ = a ≫ p ≫ (b ≫ u) := by simp only [Category.assoc]
    _ = a ≫ p ≫ (c ≫ q) := congrArg (fun t => a ≫ p ≫ t) h1
    _ = (a ≫ p ≫ c) ≫ q := by simp only [Category.assoc]

theorem projection_square : {P : Input n Λ} → (r : OriginalNativeHSShadowFiniteRun.Run P) →
    (finalNativeStage r).q ≫ baseInclusion r = phaseProjection r ≫ P.nativeStage.q
  | P, .stop _ hempty =>
    paste_square (finalNativeStage (.stop P hempty)).q
      (OriginalNativeHSEmptyStop.neighbourhood (finalInput (.stop P hempty))).inclusion
      (neighbourhood P).inclusion
      (OriginalNativeHSEmptyStop.sourceInclusion (finalInput (.stop P hempty)))
      (OriginalNativeHSShadowSuccessor.step P).projection (nativeStage P).q
      (currentSourceInclusion P) P.nativeStage.q
      (OriginalNativeHSEmptyStop.projection_square (finalInput (.stop P hempty)))
      (current_projection_square P)
  | P, .next _ _hne tail =>
    paste_square (finalNativeStage tail).q (baseInclusion tail) (neighbourhood P).inclusion
      (phaseProjection tail) (OriginalNativeHSShadowSuccessor.step P).projection (nativeStage P).q
      (currentSourceInclusion P) P.nativeStage.q (projection_square tail) (current_projection_square P)

def steps : {P : Input n Λ} → OriginalNativeHSShadowFiniteRun.Run P → ℕ
  | _, .stop _ _ => 1
  | _, .next _ _ tail => steps tail + 1

theorem physical_length : {P : Input n Λ} → (r : OriginalNativeHSShadowFiniteRun.Run P) →
    (history r).length = P.history.length + steps r
  | P, .stop _ hempty =>
    (OriginalNativeHSEmptyStop.history_length (finalInput (.stop P hempty))).trans
      (OriginalNativeHSShadowSuccessor.physical_length P)
  | P, .next _ hne tail => by
    exact (physical_length tail).trans (by
      change (OriginalNativeHSShadowSuccessor.physicalHistory P).length + steps tail = _
      rw [OriginalNativeHSShadowSuccessor.physical_length]
      simp only [steps, Nat.add_assoc, Nat.add_comm 1])

theorem proper {P : Input n Λ} (r : OriginalNativeHSShadowFiniteRun.Run P) :
    IsProperMap (finalNativeStage r).q.hom.left.base :=
  OriginalNativeHSEmptyStop.proper (finalInput r)

theorem originalReg {P : Input n Λ} (r : OriginalNativeHSShadowFiniteRun.Run P) :
    IsIsoOver (finalNativeStage r).q (intrinsicRegularLocus (finalBase r).obj) :=
  OriginalNativeHSEmptyStop.originalReg (finalInput r)

theorem scalar {P : Input n Λ} (r : OriginalNativeHSShadowFiniteRun.Run P) :
    (finalNativeStage r).q.hom.left ≫ (finalBase r).obj.hom = (finalSource r).obj.hom :=
  OriginalNativeHSEmptyStop.scalar (finalInput r)

end Run
end
end Hironaka.Analytic.Unibranch.OriginalNativeHSShadowFinitePhase
